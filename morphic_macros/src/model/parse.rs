#![allow(dead_code)]

use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{token, Attribute, Error, Ident, Token};

#[derive(Clone, Debug)]
pub struct LowerName {
    pub inner: Ident,
}

impl Parse for LowerName {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident: Ident = input.parse()?;
        if ident.to_string().chars().next().unwrap().is_lowercase() {
            Ok(LowerName { inner: ident })
        } else {
            Err(Error::new(ident.span(), "expected lowercase identifier"))
        }
    }
}

#[derive(Clone, Debug)]
pub struct UpperName {
    pub inner: Ident,
}

impl Parse for UpperName {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident: Ident = input.parse()?;
        if ident.to_string().chars().next().unwrap().is_uppercase() {
            Ok(UpperName { inner: ident })
        } else {
            Err(Error::new(ident.span(), "expected uppercase identifier"))
        }
    }
}

#[derive(Clone, Debug)]
pub enum Term {
    Var(LowerName),
    App(UpperName, Vec<Term>),
    Tuple(Punctuated<Term, Token![,]>),
}

fn parse_atomic_term(input: ParseStream) -> syn::Result<Term> {
    let lookahead = input.lookahead1();
    if lookahead.peek(token::Paren) {
        let content;
        let _paren_token: token::Paren = syn::parenthesized!(content in input);
        let terms = content.parse_terminated(Term::parse, Token![,])?;
        if terms.len() == 1 {
            Ok(terms.into_iter().next().unwrap())
        } else {
            Ok(Term::Tuple(terms))
        }
    } else if lookahead.peek(Ident) {
        let ident: Ident = input.parse()?;
        let first = ident.to_string().chars().next().unwrap();
        if first.is_lowercase() {
            Ok(Term::Var(LowerName { inner: ident }))
        } else {
            assert!(first.is_uppercase());
            Ok(Term::App(UpperName { inner: ident }, Vec::new()))
        }
    } else {
        Err(lookahead.error())
    }
}

impl Parse for Term {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.fork().parse::<UpperName>().is_ok() {
            let name = input.parse()?;
            let mut args = Vec::new();
            while input.peek(token::Paren) || input.peek(Ident) {
                args.push(parse_atomic_term(input)?);
            }
            Ok(Term::App(name, args))
        } else {
            parse_atomic_term(input)
        }
    }
}

#[derive(Clone, Debug)]
pub struct PropExpr {
    pub type_var: LowerName,
    pub dot_token: Token![.],
    pub prop: LowerName,
}

impl Parse for PropExpr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(PropExpr {
            type_var: input.parse()?,
            dot_token: input.parse()?,
            prop: input.parse()?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Constr {
    pub lhs: PropExpr,
    pub eq_token: Token![=],
    pub rhs: PropExpr,
}

impl Parse for Constr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Constr {
            lhs: input.parse()?,
            eq_token: input.parse()?,
            rhs: input.parse()?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct WhereClause {
    pub where_token: Token![where],
    pub constrs: Punctuated<Constr, Token![,]>,
}

impl Parse for WhereClause {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(WhereClause {
            where_token: input.parse()?,
            constrs: input.call(Punctuated::parse_separated_nonempty)?,
        })
    }
}

#[derive(Clone, Debug)]
pub enum Arg {
    Fixed(Term),
    Variadic(Term, Token![..]),
}

impl Parse for Arg {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let term = input.parse()?;
        if input.peek(Token![..]) {
            let dots = input.parse()?;
            Ok(Arg::Variadic(term, dots))
        } else {
            Ok(Arg::Fixed(term))
        }
    }
}

pub type Args = Punctuated<Arg, Token![,]>;

#[derive(Clone, Debug)]
pub struct Signature {
    pub attrs: Vec<Attribute>,
    pub pub_token: Option<Token![pub]>,
    pub name: LowerName,
    pub colon_token: Token![:],
    pub paren_token: token::Paren,
    pub args: Args,
    pub arrow_token: Token![->],
    pub ret: Term,
    pub where_clause: Option<WhereClause>,
    pub semi_token: Token![;],
}

impl Parse for Signature {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let attrs = input.call(Attribute::parse_outer)?;
        let pub_token = input.parse()?;
        let name = input.parse()?;
        let colon_token = input.parse()?;
        let paren_token = syn::parenthesized!(content in input);
        let args = content.call(Punctuated::parse_terminated)?;
        let arrow_token = input.parse()?;
        let ret = input.parse()?;
        let where_clause = if input.peek(Token![where]) {
            Some(input.parse()?)
        } else {
            None
        };
        let semi_token = input.parse()?;

        Ok(Signature {
            attrs,
            pub_token,
            name,
            colon_token,
            paren_token,
            args,
            arrow_token,
            ret,
            where_clause,
            semi_token,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Input {
    pub sigs: Vec<Signature>,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut sigs = Vec::new();
        while !input.is_empty() {
            sigs.push(input.parse()?);
        }
        Ok(Input { sigs })
    }
}
