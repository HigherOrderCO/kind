//! A type checker for the kind2 language. It has some utilities
//! to [compile kind2 code][compiler] into a version that the checker
//! can understand and [transform the answer back][report] into a
//! version that the Rust side can manipulate.

pub mod compiler;
mod errors;
pub mod report;

use std::sync::mpsc::Sender;

use hvm::language;
use hvm::{runtime, syntax::Term};
use kind_report::data::Diagnostic;
use kind_tree::desugared::Book;
use report::parse_report;

pub const CHECKER: &str = include_str!("checker.hvm");

pub fn eval(file: &str, term: &str, dbug: bool) -> Result<Box<Term>, String> {
    let file = language::syntax::read_file(&format!("{}\nHVM_MAIN_CALL = {}", file, term))?;
    let book = language::rulebook::gen_rulebook(&file);
    let mut prog = runtime::Program::new();
    prog.add_book(&book);
    let size = runtime::default_heap_size();
    let tids = runtime::default_heap_tids();
    let heap = runtime::new_heap(size, tids);
    let tids = runtime::new_tids(tids);
    runtime::link(
        &heap,
        0,
        runtime::Fun(*book.name_to_id.get("HVM_MAIN_CALL").unwrap(), 0),
    );
    let host = 0;
    runtime::normalize(&heap, &prog, &tids, host, dbug);
    let code = language::readback::as_term(&heap, &prog, host);
    runtime::collect(&heap, &prog.aris, tids[0], runtime::load_ptr(&heap, host));
    runtime::free(&heap, 0, 0, 1);
    Ok(code)
}

/// Generates the checker in a string format that can be
/// parsed by HVM.
pub fn gen_checker(book: &Book, functions_to_check: Vec<String>) -> String {
    let mut checker = CHECKER.to_string();
    checker.push_str(&compiler::codegen_book(book, functions_to_check).to_string());
    checker
}

/// Type checks a dessugared book. It spawns an HVM instance in order
/// to run a compiled version of the book
pub fn type_check(
    book: &Book,
    tx: Sender<Box<dyn Diagnostic>>,
    functions_to_check: Vec<String>,
) -> bool {
    let file = gen_checker(book, functions_to_check);

    match eval(&file.to_string(), "Main", false) {
        Ok(term) => {
            let errs = parse_report(&term).expect(&format!(
                "Internal Error: Cannot parse the report message from the type checker: {}",
                term
            ));
            let succeeded = errs.is_empty();

            for err in errs {
                tx.send(Box::new(err)).unwrap()
            }

            succeeded
        }
        Err(_) => panic!(),
    }
}

/// Runs the type checker but instead of running the check all function
/// we run the "eval_main" that runs the generated version that both HVM and
/// and the checker can understand.
pub fn eval_api(book: &Book) -> Box<Term> {
    let file = compiler::codegen_book(book, Vec::new());

    let file = language::syntax::read_file(&file.to_string()).unwrap();

    let book = language::rulebook::gen_rulebook(&file);

    let mut prog = runtime::Program::new();
    prog.add_book(&book);

    let heap = runtime::new_heap(runtime::default_heap_size(), runtime::default_heap_tids());
    let tids = runtime::new_tids(runtime::default_heap_tids());

    // Allocates the main term
    runtime::link(
        &heap,
        0,
        runtime::Fun(*book.name_to_id.get("Kind.API.eval_main").unwrap(), 0),
    );
    let host = 0;

    // Normalizes it
    runtime::normalize(&heap, &prog, &tids, host, false);

    // Reads it back to a string
    let term = language::readback::as_term(&heap, &prog, host);

    // Frees used memory
    runtime::collect(&heap, &prog.aris, tids[0], runtime::load_ptr(&heap, host));
    runtime::free(&heap, 0, 0, 1);

    term
}