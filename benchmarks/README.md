# Benchmarks

`smoke/` contains tiny, original instances that exercise the benchmark runner.
They are not performance evidence.

Keep downloaded competition and research corpora outside the repository unless
their license explicitly permits redistribution. Record corpus origin, license,
content hashes, family labels, and train/development/held-out role in a manifest.

The checked-in manifests are metadata only:

- `satcomp-2025-development.json` is the eight-instance tuning slice used for
  early ablations.
- `satcomp-2025-heldout-selection.json` is the immutable output-blind selection
  lock.
- `satcomp-2025-heldout.json` adds the exact compressed/CNF hashes needed by
  `tools/fetch_corpus.py`.
- `reg-n-training.json` pins six family-disjoint REGN instances used to close
  the bounded-variable-addition capability gap. It is training data, excludes
  the already revealed 2025 held-out REGN instance, and is not a general
  competition sample.
- `smoke/factor-macro-unsat.cnf` is a proof fixture at both frozen guarded-BVA
  boundaries: exactly 16 ingested short clauses per declared variable and a
  `4 × 4` product satisfying `mn = 2(m+n)`.

Neither real corpus is representative of the complete competition track; the
role fields and notes are part of the evidence boundary.
