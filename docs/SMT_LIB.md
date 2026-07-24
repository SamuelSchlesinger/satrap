# SMT-LIB support

The `smt` executable implements a streaming, interactive subset of
[SMT-LIB 2.7](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf),
release 2025-07-07. This page records the checked boundary. The project does
not yet claim full language or protocol conformance.

## Session behavior

The process reads one complete command at a time, writes and flushes its
response immediately, and retains the context for the next command. Tested
command and syntax errors produce `(error "...")` and continue without
poisoning the session. When a lexical error is detected inside a command, the
response is flushed immediately; before parsing another command, the reader
discards the rest of that malformed top-level expression. Resynchronization
tracks nested lists and respects comments, strings, doubled string quotes, and
quoted symbols, so a balanced bad command cannot consume a following command.
An unexpected top-level `)` is consumed as one bad expression.

An actually unterminated list, string, or quoted symbol has no unambiguous
following command boundary and cannot be diagnosed as unterminated while the
stream remains open. At end of input it produces one error response and the
process then exits normally. If another lexical defect was detected earlier
inside such a construct, its response is immediate but resynchronization waits
for the closing delimiter or end of input. A failure of the underlying input
or output stream remains a fatal I/O error rather than a recoverable SMT-LIB
command error.

Within the checked front-end boundary, continued execution is transactional.
Rejected declarations, definitions, assertions, assumption lists, inline
definitions, and value queries restore the term arena as well as the visible
signature and assertion stack. This includes UF/application identities,
arithmetic auxiliaries, array read demands, and hash-consing indexes. An
assumption list is fully parsed and sort-checked before any Boolean prefix is
encoded, so a bad later assumption cannot perturb the next deterministic
check. Multi-level `push` preflights the packed-variable ceiling and reserves
all required scope storage before changing the stack; an oversized request
therefore fails promptly with every prior scope intact.

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

## Inline named terms

The implemented term-bearing commands follow the SMT-LIB 2.7 semantics for
`(! term :named label)`. Closed named subterms are enumerated depth-first,
left-to-right, in postorder and installed as nullary definitions before the
enclosing command runs. A label is therefore available to later subterms in
the same command and to later commands, but not before its annotation. Labels
that capture a `let` variable or function parameter are rejected because their
terms are not closed. Duplicate, forward, and malformed labels are command
errors, and a failed command does not retain its provisional label bindings.

Labels follow ordinary declaration scope, including
`:global-declarations`. Every active Boolean label is returned by
`get-assignment` when assignment production is enabled; named non-Boolean
terms remain usable but are omitted from that response. Only a label on the
whole term in exactly `(assert (! term :named label))` participates in
`get-unsat-core`. A nested label is an assignment label, not an assertion
selector. `get-assertions` preserves the original annotated terms rather than
printing their stripped internal form.

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

Uninterpreted-sort values in `get-value` and `get-model` responses are
solver-defined abstract values. Every occurrence is printed with the explicit
SMT-LIB sort ascription required by Section 4.2.6, for example
`(as @uc!0!0 U)`. The symbol is model-local and is not added to the user
signature.

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
command and syntax errors with context reuse, balanced parser
resynchronization, rejected-command term and model identity, atomic bulk scope
limits, model inspection after `unknown`, sort-ascribed abstract model values,
and `reset-assertions` with both local and global declarations. The shared
push/CI gate also runs raw and structured session fuzz targets, 3,872
deterministic queries against pinned independent solvers, model replays, core
replays, and the query-specific proof corpus.

Those checks are strong regression evidence, not a complete conformance suite.
The remaining protocol work includes:

- parameterized sort aliases and polymorphic definitions;
- datatypes, recursion, maps, and quantifiers;
- preserving user sort-alias spelling in every printed response; and
- a fragment-complete, standard-section-indexed conformance corpus, including
  broader quoted-symbol and annotation-attribute coverage and injected
  failures during solver, theory, proof, and stream mutation.

These gaps remain release blockers in the [research roadmap](ROADMAP.md).
