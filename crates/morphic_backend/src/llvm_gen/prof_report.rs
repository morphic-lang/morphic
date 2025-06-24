use crate::data::low_ast as low;
use crate::data::profile as prof;
use crate::data::tail_rec_ast as tail;
use crate::llvm_gen::fountain_pen::{Context, Scope, Tal};
use id_collections::IdVec;
use morphic_common::util::iter::try_zip_eq;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
pub struct ProfilePointDecls<T: Context> {
    pub counters: BTreeMap<low::CustomFuncId, ProfilePointCounters<T>>,
    pub skipped_tail_rec: BTreeSet<(low::CustomFuncId, tail::TailFuncId)>,
}

#[derive(Clone)]
pub struct ProfilePointCounters<T: Context> {
    // All of these globals are of type i64
    pub total_calls: T::GlobalValue,
    pub total_clock_nanos: T::GlobalValue,
    pub total_retain_count: Option<T::GlobalValue>,
    pub total_release_count: Option<T::GlobalValue>,
    pub total_rc1_count: Option<T::GlobalValue>,
}

#[derive(Clone, Copy, Debug)]
enum Format {
    SingleLine,
    MultiLine,
}

#[derive(Clone, Debug)]
enum Json<'a, T: Context> {
    Array(Format, Vec<Json<'a, T>>),
    Object(Format, Vec<(&'a str, Json<'a, T>)>),
    ConstString(String),
    ConstU64(u64),
    DynU64(T::Value),
}

#[derive(Clone, Copy, Debug)]
enum FormatContext {
    Indent(u32),
    SingleLine,
}

impl FormatContext {
    fn indent(self) -> Self {
        match self {
            FormatContext::Indent(level) => FormatContext::Indent(level + 1),
            FormatContext::SingleLine => FormatContext::SingleLine,
        }
    }

    fn apply(self, format: &Format) -> Self {
        match format {
            Format::MultiLine => self,
            Format::SingleLine => FormatContext::SingleLine,
        }
    }

    // generate a newline if we're in multiline mode.
    fn gen_opt_newline<T: Context>(&self, s: &T::Scope) {
        match self {
            FormatContext::Indent(level) => {
                let mut sep = "\n".to_owned();
                sep.push_str(&"  ".repeat(*level as usize));
                s.call_void(s.context().tal().prof_report_write_string(), &[s.str(&sep)]);
            }

            FormatContext::SingleLine => {}
        }
    }

    // generate a whitespace separator.
    // either an indented newline, or a single space.
    fn gen_ws_sep<T: Context>(&self, s: &T::Scope) {
        match self {
            FormatContext::Indent(_) => {
                self.gen_opt_newline::<T>(s);
            }

            FormatContext::SingleLine => {
                s.call_void(s.context().tal().prof_report_write_string(), &[s.str(" ")]);
            }
        }
    }
}

impl<'a, T: Context> Json<'a, T> {
    fn gen_serialize_rec(&self, s: &T::Scope, ctx: FormatContext) {
        let prof_report_write_string = s.context().tal().prof_report_write_string();
        match self {
            Json::Array(format, items) => {
                let this_ctx = ctx.apply(format);
                let sub_ctx = this_ctx.indent();
                s.call_void(prof_report_write_string, &[s.str("[")]);
                if items.len() > 0 {
                    sub_ctx.gen_opt_newline::<T>(s);
                }
                for (i, item) in items.iter().enumerate() {
                    item.gen_serialize_rec(s, sub_ctx);
                    if i + 1 < items.len() {
                        s.call_void(prof_report_write_string, &[s.str(",")]);
                        sub_ctx.gen_ws_sep::<T>(s);
                    } else {
                        this_ctx.gen_opt_newline::<T>(s);
                    }
                }
                s.call_void(prof_report_write_string, &[s.str("]")]);
            }

            Json::Object(format, items) => {
                let this_ctx = ctx.apply(format);
                let sub_ctx = this_ctx.indent();
                s.call_void(prof_report_write_string, &[s.str("{")]);
                if items.len() > 0 {
                    sub_ctx.gen_opt_newline::<T>(s);
                }
                for (i, (key, val)) in items.iter().enumerate() {
                    s.call_void(
                        prof_report_write_string,
                        &[s.str(&format!("{}: ", json::stringify(key as &str)))],
                    );
                    val.gen_serialize_rec(s, sub_ctx);
                    if i + 1 < items.len() {
                        s.call_void(prof_report_write_string, &[s.str(",")]);
                        sub_ctx.gen_ws_sep::<T>(s);
                    } else {
                        this_ctx.gen_opt_newline::<T>(s);
                    }
                }
                s.call_void(prof_report_write_string, &[s.str("}")]);
            }

            Json::ConstString(string) => {
                s.call_void(
                    prof_report_write_string,
                    &[s.str(&json::stringify(string as &str))],
                );
            }

            Json::ConstU64(val) => {
                s.call_void(prof_report_write_string, &[s.str(&val.to_string())]);
            }

            Json::DynU64(val) => {
                s.call_void(s.context().tal().prof_report_write_u64(), &[*val]);
            }
        }
    }

    fn gen_serialize(&self, s: &T::Scope) {
        self.gen_serialize_rec(s, FormatContext::Indent(0));
    }
}

pub fn define_prof_report_fn<T: Context>(
    context: &T,
    profile_points: &IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    profile_point_decls: &IdVec<prof::ProfilePointId, ProfilePointDecls<T>>,
) -> T::FunctionValue {
    let result = context.declare_func("prof_report", &[], None);

    // load-bearing '&' due to closure shenanigans
    let s = &context.scope(result);

    s.call_void(context.tal().prof_report_init(), &[]);

    let to_write: Json<'_, T> = {
        use Format::*;
        use Json::*;

        Object(
            MultiLine,
            vec![
                (
                    "clock_res_nanos",
                    DynU64(s.call(context.tal().prof_clock_res_nanos(), &[])),
                ),
                (
                    "timings",
                    Array(
                        MultiLine,
                        try_zip_eq(profile_points, profile_point_decls)
                            .unwrap()
                            .flat_map(|(_prof_id, prof_point, prof_decls)| {
                                prof_point
                                    .reporting_names
                                    .iter()
                                    .map(move |(module, function)| {
                                        Object(
                                            MultiLine,
                                            vec![
                                                (
                                                    "module",
                                                    Array(
                                                        SingleLine,
                                                        module
                                                            .0
                                                            .iter()
                                                            .map(|elem| {
                                                                ConstString(elem.0.to_owned())
                                                            })
                                                            .collect(),
                                                    ),
                                                ),
                                                ("function", ConstString(function.0.to_owned())),
                                                (
                                                    "specializations",
                                                    Array(
                                                        MultiLine,
                                                        prof_decls
                                                            .counters
                                                            .iter()
                                                            .map(|(low_id, counters)| {
                                                                let mut entries = vec![
                                                                    (
                                                                        "low_func_id",
                                                                        ConstU64(low_id.0 as u64),
                                                                    ),
                                                                    (
                                                                        "total_calls",
                                                                        DynU64(s.ptr_get(
                                                                            s.i64_t(),
                                                                            context.global_value_as_pointer(counters
                                                                                .total_calls)
                                                                        )),
                                                                    ),
                                                                    (
                                                                        "total_clock_nanos",
                                                                        DynU64(s.ptr_get(
                                                                            s.i64_t(),
                                                                            context.global_value_as_pointer(counters
                                                                                .total_clock_nanos)
                                                                        )),
                                                                    ),
                                                                ];

                                                                if let Some(total_retain_count) =
                                                                    counters.total_retain_count
                                                                {
                                                                    entries.push((
                                                                        "total_retain_count",
                                                                        DynU64(s.ptr_get(
                                                                            s.i64_t(),
                                                                            context.global_value_as_pointer(total_retain_count)
                                                                        )),
                                                                    ));
                                                                }

                                                                if let Some(total_release_count) =
                                                                    counters.total_release_count
                                                                {
                                                                    entries.push((
                                                                        "total_release_count",
                                                                        DynU64(s.ptr_get(
                                                                            s.i64_t(),
                                                                            context.global_value_as_pointer(total_release_count)
                                                                        )),
                                                                    ));

                                                                    if let Some(total_rc1_count) =
                                                                        counters.total_rc1_count
                                                                    {
                                                                        entries.push((
                                                                        "total_rc1_count",
                                                                        DynU64(s.ptr_get(
                                                                            s.i64_t(),
                                                                            context.global_value_as_pointer(total_rc1_count)
                                                                        )),
                                                                    ));
                                                                    }
                                                                }

                                                                Object(SingleLine, entries)
                                                            })
                                                            .collect(),
                                                    ),
                                                ),
                                                // We include these because we don't want skipped
                                                // tail-recursive functions to be silently lost, but
                                                // we also don't want to generate a warning or error
                                                // during compilation purely due to profiling
                                                // concerns.
                                                //
                                                // Most likely, anything consuming a profile report
                                                // should throw an error if this array is nonempty
                                                // for a function it cares about.
                                                (
                                                    "skipped_tail_rec_specializations",
                                                    Array(
                                                        MultiLine,
                                                        prof_decls
                                                            .skipped_tail_rec
                                                            .iter()
                                                            .map(|(low_id, tail_id)| {
                                                                Object(
                                                                    SingleLine,
                                                                    vec![
                                                                        (
                                                                            "low_func_id",
                                                                            ConstU64(
                                                                                low_id.0 as u64,
                                                                            ),
                                                                        ),
                                                                        (
                                                                            "tail_func_id",
                                                                            ConstU64(
                                                                                tail_id.0 as u64,
                                                                            ),
                                                                        ),
                                                                    ],
                                                                )
                                                            })
                                                            .collect(),
                                                    ),
                                                ),
                                            ],
                                        )
                                    })
                            })
                            .collect(),
                    ),
                ),
            ],
        )
    };

    to_write.gen_serialize(&s);

    s.call_void(context.tal().prof_report_done(), &[]);

    s.ret_void();

    result
}
