# SMT-LIB support

The `smt` executable implements a streaming, interactive subset of
[SMT-LIB 2.7](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf),
release 2025-07-07. This page records the checked boundary. The project does
not yet claim full language or protocol conformance.

## Session behavior

The process reads one complete command at a time, writes and flushes its
response immediately, and retains the context for the next command. Tested
command-level errors produce `(error "...")` and continue without poisoning
the session. Lexical or malformed top-level S-expression recovery remains
open: those errors currently terminate the reader.

The implemented command families are:

| Family | Commands |
| --- | --- |
| Configuration | `set-logic`, `set-option`, `get-option`, `set-info`, `get-info` |
| Declarations | `declare-sort` with arity zero, `define-sort`, `declare-const`, `declare-fun`, `define-const`, `define-fun` |
| Assertions | `assert`, `push`, `pop` |
| Solving | `check-sat`, `check-sat-assuming` |
| Inspection | `get-model`, `get-value`, `get-assignment`, `get-assertions`, `get-unsat-core`, `get-unsat-assumptions`, `get-proof` |
| Lifecycle | `reset-assertions`, `reset`, `echo`, `exit` |

Standard datatype, sort-parameter, and recursive-function commands return
`unsupported`. Unknown nonstandard command names are command errors.

`reset` restores a fresh session. `reset-assertions` removes assertions,
scopes, learned search state, and theory state. Declarations survive it only
when `:global-declarations` is true; retained array declarations reinstall
their theory axioms in the rebuilt solver.

## Options and output

The session implements:

- `:print-success`;
- `:produce-models`, `:produce-assignments`, `:produce-assertions` (and the
  legacy alias `:interactive-mode`), `:produce-unsat-cores`,
  `:produce-unsat-assumptions`, and `:produce-proofs`;
- `:global-declarations`;
- `:regular-output-channel` and `:diagnostic-output-channel`; and
- `:reproducible-resource-limit`.

The two required output-channel options take effect for the response to their
own `set-option` command. File channels are opened append-only and responses
are flushed. If a channel cannot be opened, the command reports an error,
restores the prior channel, and continues. The diagnostic channel is retained
even though the solver does not yet emit an ordinary diagnostic stream.
Unsupported options return `unsupported`; `get-option :random-seed` reports
the deterministic value `0`.

## Result modes

| Result | Permitted inspection | Correctness meaning |
| --- | --- | --- |
| `sat` | Model, value, and named Boolean assignment queries when enabled | The returned candidate passed the solver's in-process validation for the implemented fragment. |
| `unknown` | The same model/value/assignment queries when enabled, plus `get-info :reason-unknown` | The deterministic total structure is available because SMT-LIB enters model-inspection mode, but it is not claimed to satisfy the active assertions. |
| `unsat` | Named core, failed-assumption, and query-specific proof queries when enabled | The reported artifact is checked according to its documented proof or replay boundary. |

Any assertion, declaration, scope change, or reset invalidates the preceding
result. Resource exhaustion and incomplete theory combinations return
`unknown`; they do not guess `sat` or `unsat`.

## Logics

The session accepts 14 explicit quantifier-free selectors:

`QF_BOOL`, `QF_BV`, `QF_UF`, `QF_UFBV`, `QF_ABV`, `QF_AUFBV`, `QF_IDL`,
`QF_LIA`, `QF_RDL`, `QF_LRA`, `QF_UFIDL`, `QF_UFLIA`, `QF_UFLRA`, and
`QF_AUFLIA`.

`ALL` enables the union of the implemented front-end features. It is useful
for interactive exploration but can honestly return `unknown` for incomplete
mixed integer/real reasoning. Proof production is deliberately rejected with
`ALL`: query-specific certificates are advertised only for the 14 explicit
logics. The exact certificate construction and independent checker are
described in [Proof checking](PROOF_CHECKING.md).

## Validation boundary

Rust unit and integration tests cover online response flushing, mode
transitions, immediate output redirection and rollback, scoped declarations,
errors and context reuse, model inspection after `unknown`, and
`reset-assertions` with both local and global declarations. The shared push/CI
gate also runs raw and structured session fuzz targets, 3,872 deterministic
queries against pinned independent solvers, model replays, core replays, and
the query-specific proof corpus.

Those checks are strong regression evidence, not a complete conformance suite.
The remaining protocol work includes:

- recovery after malformed lexical or top-level S-expression input;
- full semantics for nested inline `:named` annotations and every closed
  Boolean label reported by `get-assignment`;
- parameterized sort aliases and polymorphic definitions;
- datatypes, recursion, maps, and quantifiers;
- preserving user sort-alias spelling in every printed response; and
- a fragment-complete, standard-section-indexed conformance corpus.

These gaps remain release blockers in the [research roadmap](ROADMAP.md).
