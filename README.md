# BFS-Avoidance Frontier

**Rigidity of Pattern-Avoiding Breadth-First Reading Words of Increasing Trees**

For every branching bound `k >= 2`, this work proves two equalities of sets of reading words:

- A 312-avoiding permutation is realizable on an increasing ordered tree of maximum outdegree k exactly when it satisfies the complete k-ary heap inequalities.
- A 231-avoiding permutation of length `1 modulo k` realizable with maximum outdegree k is realizable on a full k-ary tree.

Both arguments use the nondecreasing sequence of BFS parent positions. They preserve the word itself. The full-degree construction is linear in the word length when supplied with an initial realization.

[Read the paper](paper/main.pdf) | [Mathematical statements](docs/THEOREMS.md) | [Verification scope](docs/COMPUTATIONAL_VERIFICATION.md) | [Release instructions](release/README.md)

## Binary consequences

The results imply, for positive indices:

- `A245899(n) = A246747(n)`.
- `A245902(r) = A245899(2r-1)`.
- `A245901(r) = A245898(2r-1)`.

A245899 inherits the known Catalan-convolution recurrence for heaps. The 321 heap analogue first fails at length 4, witnessed by 1423. The full binary analogue first fails at odd length 11: 8,095 unary-binary words versus 8,048 full binary words. All 47 missing words are retained as a certificate.

The data package adds 28 entries to the six sequences relative to the retained baseline: 27 direct enumerations and A245898(15), inferred from the proved full binary identity. Many 312 values also occur in the earlier heap sequence. Defant's general heap theorem implies exponential growth rate 4 per vertex for all three patterns, for both bounded-degree and full trees at admissible sizes.

## Verification

The development combines mathematical proofs with two explicitly scoped verification methods:

- **Lean 4:** the binary theorems are proved on inductive ordered trees through a semantic bridge. The arbitrary-k heap equivalence and full-degree construction are proved over the exact parent-sequence constraints. The general tree reconstruction is proved in the paper. The axiom audit reports only Lean's standard axioms. See [general-k formalization](docs/GENERAL_K_FORMALIZATION.md).
- **Computation:** two enumerators agree on all retained counts through length 11. The full table is recomputed by the prefix-search solver. A separate degree-sequence dynamic program checks the exact counterexample list and general-k constructions. Recurrence checks cover the long 312 b-files. Finite computations verify their stated ranges.

## Reproduce

Requirements: Python 3 (standard library only), Lean 4.24.0 through elan, and a LaTeX distribution with latexmk.

```sh
make verify-python       # binary suite and artifact checks through length 11
make verify-lean         # all formal statements and the axiom audit
make recompute           # every retained directly enumerated term
make paper               # PDF from its LaTeX source
make verify-publication  # sources, receipts, table, and punctuation checks
```

The full computation uses up to four processes. Retained execution receipts are in `data/verification/20260929/`. Detailed method and coverage are in `docs/COMPUTATIONAL_VERIFICATION.md`.

## Layout

- `paper/`: article source and PDF.
- `lean/`: binary tree proofs, auxiliary promotion lemma, and general parent-sequence proofs.
- `python/`: reference tree enumeration, prefix solver, independent degree-sequence recognition, and verification drivers.
- `data/`: raw tables, new-entry summary, counterexamples, and verification receipts.
- `oeis-submission/`: indexed b-files and contribution preparation notes.
- `release/`: packaging, verification, metadata, and publication provenance.

## Citation, licensing, and assistance

See `CITATION.cff` for citation metadata and `LICENSES.md` for component licenses. Original code is MIT; the revised manuscript, documentation, and original research data are CC BY 4.0. Previously distributed versions retain their existing licenses.

The work used Claude and Codex for assistance with exploration, writing, programs, and formalization. The author is responsible for the final mathematical statements and presentation. The repository is a research artifact; publication as a preprint does not signify journal acceptance.
