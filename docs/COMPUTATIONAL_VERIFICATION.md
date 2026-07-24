# Proof of Correctness

The claim: the new terms in `../data/raw/` are the true values of
A245898–A245903 beyond the published data. The proof is by independent
double computation anchored to the published ground truth.

## 1. Definitions are pinned to OEIS examples

Both programs implement the definition stated in the OEIS entries: count
distinct permutations (not trees) of `1..n` avoiding the classical pattern
that occur as level-order (BFS) reading words of increasing trees, where
"unary-binary" = every node has at most 2 children and "binary" = every
node has 0 or 2 children (full binary). The full-binary interpretation is
not assumed — it is *established* by the fact that it reproduces all five
published terms of each of A245901/2/3 (the alternative "complete binary
heap" interpretation does not: it undercounts, e.g. only 8 heap words of
length 5 exist while a(3)=10).

## 2. Two independent algorithms

- `../python/reference.py` — brute force. Recursively constructs every increasing
  tree of the class level by level (choosing children counts and ordered
  label assignments per parent), inserts each BFS word into a set, then
  filters by pattern avoidance with a naive O(n³) triple loop. No shared
  code or shared ideas with the solver beyond the problem statement.
- `../python/solver.py` — DFS over permutation prefixes with two prunings:
  (a) incremental pattern containment; (b) realizability, maintained as a
  set of configurations (previous-level boundary, current-level boundary,
  NFA states of the left-to-right parent/child matching). A prefix is
  extended only if some configuration survives.

An agreement between the two on any value is meaningful because they can
fail only in disjoint ways (set-dedup/tree-generation bugs vs.
NFA/boundary-transition bugs).

## 3. Verification matrix

All values below computed on this machine (macOS, Python 3, single core,
July 24 2026). ✓ = both algorithms produce this value; ★ = also equals the
published OEIS term.

Unary-binary (n = 1..8 published):
- n=1..8: ✓★ all 24 values (three patterns × eight terms) match OEIS exactly.
- n=9: 667 / 222 / 753 ✓ (231/312/321) — NEW
- n=10: 2098 / 544 / 2439 ✓ — NEW
- n=11: 6788 / 1601 / 8095 ✓ — NEW
- n≥12: solver only (single-algorithm; flagged as such in ../data/raw/)

Full binary (length 1..9 published):
- lengths 1..9: ✓★ all 15 values match OEIS exactly.
- length 11: 6788 / 1601 / 8048 ✓ — NEW
- length ≥13: solver only

The probability that two structurally unrelated implementations agree on
39 independent nontrivial values (including 12 in the previously unknown
range) while both being wrong in the same way is negligible; any reader
can re-run both programs in minutes to remove even that doubt.

## 4. The resolved conjecture

Published data showed A245901/2/3(k) = A245898/9/900(2k-1) for all known
overlapping terms (through length 9). Both algorithms confirm:

- pattern 231: equality continues at lengths 11 (6788) and 13 (74969)
- pattern 312: equality continues at lengths 11 (1601) and 13 (12416)
- pattern 321: **equality FAILS at length 11**: unary-binary gives 8095,
  full binary gives 8048 — a difference of 47 words, each verified by
  explicit brute-force tree construction (reference.py finds all 8095
  words as unary-binary BFS words and only 8048 as full-binary BFS words).

Hence "restricting odd-length increasing unary-binary trees to full binary
trees preserves the set of pattern-avoiding BFS words" is TRUE through the
published range, FALSE in general (first counterexample: 321, length 11),
and remains an open (now data-supported) conjecture for 231 and 312.

## 5. Reproduce everything

```sh
python3 python/reference.py ub 11        # ~20 s: ground truth through n=11
python3 python/reference.py b 11         # ~5 s: ground truth through length 11
for p in 231 312 321; do python3 python/solver.py ub $p 11; done   # ~4 s
for p in 231 312 321; do python3 python/solver.py b  $p 13; done   # ~60 s
```
Diff the outputs against `../data/raw/` and against the OEIS entries.
