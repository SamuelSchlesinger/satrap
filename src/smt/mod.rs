//! Interactive SMT-LIB support and typed SMT terms.
//!
//! The session and term APIs are persistent and share one incremental SAT
//! engine across Boolean, bit-vector, UF, array, and exact linear-arithmetic
//! fragments.

mod api;
mod arithmetic;
mod bitvec;
mod encode;
mod engine;
mod proof;
mod session;
mod sexpr;
mod term;
mod theory;
mod uf;
mod validate;

pub use api::{
    AnyTerm, ArraySort, ArrayTerm, ArrayValue, BitVecTerm, BitVecValue, BoolTerm, CheckResult,
    Context, ContextError, Function, IntTerm, RealTerm, SmtSort, UninterpretedSort,
    UninterpretedTerm, UninterpretedValue, Value,
};
pub use num_bigint::BigInt;
pub use num_rational::BigRational;
pub use session::{CommandOutput, Session, SessionIoError, run};
pub use term::{
    ArraySortId, FunctionId, Sort, SortId, TermError, TermId, TermStore, UninterpretedSortId,
};
