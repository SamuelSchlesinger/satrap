//! Interactive SMT-LIB support and typed SMT terms.
//!
//! The currently implemented solver fragment is quantifier-free Boolean logic.
//! The session and term APIs are intentionally persistent so additional
//! theories can share the same incremental SAT engine.

mod api;
mod arithmetic;
mod bitvec;
mod encode;
mod engine;
mod session;
mod sexpr;
mod term;
mod theory;
mod uf;

pub use api::{
    AnyTerm, ArraySort, ArrayTerm, ArrayValue, BitVecTerm, BitVecValue, BoolTerm, CheckResult,
    Context, ContextError, Function, SmtSort, UninterpretedSort, UninterpretedTerm,
    UninterpretedValue, Value,
};
pub use session::{CommandOutput, Session, SessionIoError, run};
pub use term::{
    ArraySortId, FunctionId, Sort, SortId, TermError, TermId, TermStore, UninterpretedSortId,
};
