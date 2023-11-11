use std::collections::BTreeSet;

use crate::data::raw_ast as raw;

id_type!(pub ProfilePointId);

#[derive(Clone, Debug)]
pub struct ProfilePoint {
    // A single function may appear in a profiling report under multiple names, because the user may
    // pass two or more '--profile' arguments which alias the same underlying function.
    pub reporting_names: BTreeSet<(raw::ModPath, raw::ValName)>,
    pub record_rc: bool,
}
