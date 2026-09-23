//! skijack -- a surface language over SKI, in Rust.
//!
//! The pipeline, end to end: [`compile`] parses, checks (Stage A), generates
//! the type-generated forms, types (Stage B) and expands to closed
//! ``{S,K,I}`` terms; [`run::run_level1`] runs a level-1 declaration;
//! [`dictionary::lift`] names what the dictionary knows.

pub mod abi;
pub mod ast;
pub mod check;
pub mod corpus;
pub mod dictionary;
pub mod env;
pub mod errors;
pub mod expand;
pub mod generate;
pub mod lexicon;
pub mod parser;
pub mod quote;
pub mod reduce;
pub mod render;
pub mod run;
pub mod term;
pub mod typecheck;

pub use errors::{Problem, ProblemKind, Site, SkijackError};
pub use expand::{expand_program, Expansion, Level1Program, PRELUDE_NAMES};
pub use lexicon::Lexicon;
pub use parser::{parse, parse_ascii, parse_unicode};
pub use render::{render_expr, render_program};

pub const VERSION: &str = "0.2.0";

/// Source text -> a compiled program: parse, Stage A, generation, Stage B,
/// expansion.
pub fn compile(source: &str, lexicon: Lexicon) -> errors::Result<Expansion> {
    compile_with(source, lexicon, true, true)
}

pub fn compile_with(source: &str, lexicon: Lexicon, check: bool, generate_forms: bool) -> errors::Result<Expansion> {
    let program = parse(source, lexicon)?;
    expand_program(&program, check, generate_forms)
}
