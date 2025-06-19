#![allow(dead_code)]

mod model;

#[proc_macro]
pub fn declare_signatures(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    model::declare_signatures(input)
}
