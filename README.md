# BFS-Avoidance Frontier

**Two rigidity theorems for pattern-avoiding BFS reading words of increasing
trees — resolving three conjectures recorded in the OEIS, with prose proofs,
exhaustive computational verification, and complete machine-checked
formalizations in Lean 4.**

## The problem

An *increasing tree* on `n` nodes carries the labels `1..n` with every child
larger than its parent. Its *BFS reading word* is the permutation obtained by
reading the labels level by level, left to right. Levin, Pudwell, Riehl and
Sandberg (*Pattern avoidance in k-ary heaps*, Australas. J. Combin. 64 (2016))
asked how many permutations avoid a classical length-3 pattern **and** arise
as such reading words. Six OEIS sequences (A245898–A245903) cover unary-binary
trees (≤ 2 children per node) and full binary trees (0 or 2 children) against
the patterns 231, 312 and 321 — all six were tagged `more` ("needs extension")
with only 5–8 known terms each, frozen since 2014.

## Results

**Theorem A (312 heap collapse).** A 312-avoiding permutation is the BFS word
of *some* increasing unary-binary tree **iff** it satisfies the plain
binary-heap array condition `w[⌊i/2⌋] < w[i]`. Realizability over the entire
infinite family of tree shapes collapses to one fixed shape, and the
conjectured bijection is the **identity map**. This settles the conjecture
recorded in OEIS A246747 ("May be equal to A245899") and yields
`A245902(k) = A245899(2k−1)`; A245899 thereby inherits a proven
Catalan-convolution recurrence.

**Theorem B (231 parity collapse).** Every odd-length 231-avoiding BFS word of
an increasing unary-binary tree is also the BFS word of an increasing *full
binary* tree. Hence `A245901(k) = A245898(2k−1)`.

**Sharpness.** Both collapses provably fail for the pattern 321: at length 11
there are 8095 unary-binary words but only 8048 full-binary words; the 47
counterexample permutations are listed explicitly as a certificate.

**Key technical ingredient.** An unconditional *promotion cascade* lemma:
growing a BFS level by the next element never destroys realizability of the
remaining suffix — true for **all** words, no pattern hypothesis. Pattern
avoidance is needed at exactly one parity-driven extension step, which is
precisely where 321 breaks.

**New data.** 28 previously unknown sequence terms (A245898–A245900 extended
from n = 8 to n = 14; A245901–A245903 from length 9 to length 15). See
[`data/NEW_TERMS.md`](data/NEW_TERMS.md).

## Three independent layers of verification

1. **Prose proofs** — [`docs/THEOREMS.md`](docs/THEOREMS.md), self-contained
   and human-readable.
2. **Exhaustive computation** — every lemma and both theorems verified on all
   instances at small sizes (hundreds of thousands of cases, zero failures),
   plus two independent algorithms reproducing all 36 published OEIS terms:
   [`docs/COMPUTATIONAL_VERIFICATION.md`](docs/COMPUTATIONAL_VERIFICATION.md),
   runnable via `make verify-python`.
3. **Machine-checked formalization** — complete Lean 4 proofs
   ([`lean/`](lean/)), no `sorry`, standard axioms only, **stated on genuine
   inductive trees** (`theoremA_trees`, `theoremB_trees`) via a proven
   semantic bridge, so no encoding needs to be trusted. Verified end-to-end by
   `make verify-lean`; the kernel-checked build *is* the proof.

## Repository layout

```
├── README.md                        ← you are here
├── LICENSE                          MIT
├── CITATION.cff                     citation metadata
├── Makefile                         make all | verify-python | verify-lean | recompute
├── docs/
│   ├── THEOREMS.md                  the theorems and their prose proofs
│   ├── COMPUTATIONAL_VERIFICATION.md  double-computation methodology & matrix
│   └── PRIOR_WORK.md                novelty audit (OEIS / arXiv sweep, July 2026)
├── data/
│   ├── NEW_TERMS.md                 all new sequence terms, consolidated
│   ├── raw/                         solver outputs (ub_*.txt, b_*.txt)
│   └── certificates/                the 47 explicit 321-counterexample words
├── python/
│   ├── reference.py                 brute-force ground truth (tree enumeration)
│   ├── solver.py                    fast independent algorithm (pruned prefix-DFS)
│   └── verify_theorems.py           exhaustive lemma/theorem verification suite
└── lean/                            Lean 4 formalization (see lean/README.md)
    └── BfsWords/                    Defs · Basic · Balanced · TheoremA ·
                                     Cascade · B231 · TheoremB · Trees · Sanity
```

## Reproduce everything

```sh
make verify-python   # ~1 min: all lemmas + theorems on exhaustive small cases
make verify-lean     # Lean kernel checks every proof; prints the axiom audit
make recompute       # regenerate the new OEIS terms (minutes)
```

Requirements: Python 3 (stdlib only); [elan](https://github.com/leanprover/elan)
for Lean (toolchain pinned in `lean/lean-toolchain`, no external Lean
dependencies).

## Status and provenance

* The three resolved conjectures were open and publicly recorded (OEIS
  A246747 cross-reference; sequence data coincidences) from 2014 until this
  work (July 2026). [`docs/PRIOR_WORK.md`](docs/PRIOR_WORK.md) documents the
  literature audit.
* Research, proofs, code and formalization were produced in an AI-assisted
  session (Claude, Anthropic) directed by the repository author; every claim
  is independently checkable by the verification layers above, none of which
  requires trusting that process.
* Planned next steps: OEIS submissions (new terms + proof references) and an
  arXiv note.

## Citing

See [`CITATION.cff`](CITATION.cff). If you extend the sequences or the
theorems, a reference to this repository and to Levin–Pudwell–Riehl–Sandberg
(2016) would be appreciated.
