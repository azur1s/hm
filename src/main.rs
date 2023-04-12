#![allow(unused_macros)]
#![allow(clippy::new_without_default)]

#[macro_use]
pub mod exp;
pub mod infer;
pub mod renamer;

use crate::{exp::*, infer::infer_exprs};

fn main() {
    /*
    let id = \x -> x;
    let a = 15 + id(10);
    let x = 34 in
        a + x;
     */
    // let es = vec![
    //     define!("id", None, lambda!("x" => ident!("x"), None)),
    //     define!("a", None, binary!(BinaryOp::Add, num!(15.0), call!(ident!("id"), num!(10.0)))),
    //     let_!("x", None, num!(34.0), binary!(BinaryOp::Add, ident!("a"), ident!("x"))),
    // ];

    /*
    let id = \x -> x;
    let compose = \f g x -> f(g(x));
     */
    // let es = vec![
    //     define!("id", None, lambda!("x" => ident!("x"), None)),
    //     define!("compose", None,
    //         lambda!("f", "g", "x" =>
    //             call!(ident!("f"), call!(ident!("g"), ident!("x"))),
    //             None)),
    // ];

    /*
    let f = \w x y z -> w(x(y), z);
    let add = \x y -> x + y;
    let id = \x -> x;
    let a = f(add, id, 10, 20);
     */
    // let es = vec![
    //     define!("f", None,
    //         lambda!("w", "x", "y", "z" =>
    //             call!(ident!("w"), call!(ident!("x"), ident!("y")), ident!("z")),
    //             None)),
    //     define!("add", None,
    //         lambda!("x", "y" =>
    //             binary!(BinaryOp::Add, ident!("x"), ident!("y")),
    //             None)),
    //     define!("id", None, lambda!("x" => ident!("x"), None)),
    //     define!("a", None,
    //         call!(ident!("f"),
    //             ident!("add"), ident!("id"), num!(10.0), num!(20.0))),
    // ];

    // \w x y z -> w(x(y), z);
    // let es = vec![lambda!("w", "x", "y", "z" =>
    //     call!(ident!("w"), call!(ident!("x"), ident!("y")), ident!("z")),
    //     None
    // )];

    // def a = def b = 10;
    let es = vec![
        define!("a", None, define!("b", None, num!(10.0))),
    ];

    let start = std::time::Instant::now();
    let (tes, e) = infer_exprs(es.clone());
    let end = std::time::Instant::now();
    println!(
        "{}\x1b[0mType inference took {}s",
        match e.is_empty() {
            true => "\x1b[92mOK! ",
            false => "\x1b[91mERR! ",
        },
        (end - start).as_secs_f64()
    );

    println!("\x1b[95;1mExpressions:\x1b[0m");
    for e in es {
        println!("{e}");
    }

    if !tes.is_empty() {
        println!("\x1b[94;1mTyped expressions:\x1b[0m");
        for te in tes {
            println!("{te}");
        }
    }
    if !e.is_empty() {
        println!("\x1b[91;1mErrors:\x1b[0m");
        println!("{e}");
    }
}
