use quote::{quote, ToTokens};
use syn::spanned::Spanned;
use syn::Error;

mod parse;

// We expect the data structures we emit to be declared in this module of the main Morphic crate.
#[allow(non_snake_case)]
fn DATA_MODULE() -> proc_macro2::TokenStream {
    "crate::data::borrow_model".parse().unwrap()
}

fn declare_term(term: &parse::Term) -> proc_macro2::TokenStream {
    let data_module = DATA_MODULE();
    match term {
        parse::Term::Var(var) => {
            let var = var.inner.to_string();
            quote! {
                #data_module::RawTerm::Var(#var.to_string())
            }
        }
        parse::Term::App(name, args) => {
            let name = name.inner.to_string();
            let args = args.iter().map(|arg| declare_term(arg)).collect::<Vec<_>>();
            quote! {
                #data_module::RawTerm::App(#name.to_string(), vec![#(#args),*])
            }
        }
        parse::Term::Tuple(fields) => {
            let fields = fields
                .iter()
                .map(|field| declare_term(field))
                .collect::<Vec<_>>();
            quote! {
                #data_module::RawTerm::Tuple(vec![#(#fields),*])
            }
        }
    }
}

fn declare_prop_expr(prop_expr: &parse::PropExpr) -> proc_macro2::TokenStream {
    let data_module = DATA_MODULE();
    let type_var = prop_expr.type_var.inner.to_string();
    let prop = prop_expr.prop.inner.to_string();
    quote! {
        #data_module::RawPropExpr {
            type_var: #type_var.to_string(),
            prop: #prop.to_string(),
        }
    }
}

fn declare_constr(constr: &parse::Constr) -> proc_macro2::TokenStream {
    let data_module = DATA_MODULE();
    let lhs = declare_prop_expr(&constr.lhs);
    let rhs = declare_prop_expr(&constr.rhs);
    quote! {
        #data_module::RawConstr {
            lhs: #lhs,
            rhs: #rhs,
        }
    }
}

fn declare_option<T: ToTokens>(opt: &Option<T>) -> proc_macro2::TokenStream {
    match opt {
        Some(inner) => quote! { Some(#inner) },
        None => quote! { None },
    }
}

fn declare_args(args: &parse::Args) -> Result<proc_macro2::TokenStream, Error> {
    let data_module = DATA_MODULE();
    let mut fixed = Vec::new();
    let mut variadic = None;
    for (i, arg) in args.iter().enumerate() {
        match arg {
            parse::Arg::Fixed(arg) => {
                fixed.push(declare_term(arg));
            }
            parse::Arg::Variadic(arg, dots) => {
                if i + 1 == args.len() {
                    variadic = Some(declare_term(arg));
                } else {
                    return Err(Error::new(dots.span(), "variadic argument must be last"));
                }
            }
        }
    }
    let variadic = declare_option(&variadic);
    Ok(quote! {
        #data_module::RawArgs {
            fixed: vec![#(#fixed),*],
            variadic: #variadic,
        }
    })
}

fn declare_signature(sig: &parse::Signature) -> Result<proc_macro2::TokenStream, Error> {
    let data_module = DATA_MODULE();
    let attrs = &sig.attrs;
    let pub_token = &sig.pub_token;
    let name = &sig.name.inner;
    let args = declare_args(&sig.args)?;
    let ret = declare_term(&sig.ret);
    let constrs = match &sig.where_clause {
        Some(where_clause) => where_clause
            .constrs
            .iter()
            .map(|constr| declare_constr(constr))
            .collect::<Vec<_>>(),
        None => Vec::new(),
    };
    Ok(quote! {
        #(#attrs)*
        #[allow(non_upper_case_globals)]
        #pub_token static #name: ::once_cell::sync::Lazy<Signature> = ::once_cell::sync::Lazy::new(|| {
            #data_module::resolve_signature(#data_module::RawSignature {
                args: #args,
                ret: #ret,
                constrs: vec![#(#constrs),*],
            })
            .unwrap()
        });
    })
}

#[proc_macro]
pub fn declare_signatures(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as parse::Input);

    let sigs = input
        .sigs
        .iter()
        .map(|sig| declare_signature(sig))
        .collect::<Result<Vec<_>, _>>();

    proc_macro::TokenStream::from(match sigs {
        Ok(sigs) => quote! { #(#sigs)* },
        Err(err) => err.to_compile_error(),
    })
}
