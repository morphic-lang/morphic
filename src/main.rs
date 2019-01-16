#![allow(dead_code)]

mod data;
mod lex;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parse);

fn main() {
    println!(
        "{:#?}",
        parse::ProgramParser::new().parse(lex::Lexer::new(
            "
            // This is a comment
            type Option a {
                Some(a),
                None,
            }

            type Iter a {
                Iter(() -> Option (a, Iter a)),
            }

            map(f: a -> b, opt: Option a): Option b =
                match opt {
                    Some(x) -> Some(f(x)),
                    None -> None,
                }

            circ_area(r: Float): Float =
                3.14159265 *. r *. r

            circ_area_gt_1(r: Float): Bool =
                3.14159265 *. r *. r >. 1

            curry(func: (a, b) -> c): a -> b -> c =
                \\x -> \\y -> func(x, y)

            cache(func: Int -> a, x0: Int): Int -> a =
                let y0 = func(x0) in
                \\x -> match x = x0 {
                    True -> y0,
                    False -> func(x),
                }

            main(): IO () =
                print(\"Hello, \\\"world\\\"!\")
        "
        ))
    );
}
