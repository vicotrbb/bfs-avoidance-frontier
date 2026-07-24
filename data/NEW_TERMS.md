# New Terms for OEIS A245898–A245903

All values below were previously unpublished (the OEIS entries, tagged
`more`, ended at n = 8 / length 9 since 2014). Every value with
n ≤ 11 (unary-binary) or length ≤ 11 (full binary) was computed by **two
independent algorithms** (`../python/reference.py`, brute-force tree
enumeration; `../python/solver.py`, pruned prefix-DFS) which agree on all
published terms and on each other everywhere they overlap. Deeper values
come from the solver alone, anchored by that overlap. Raw solver outputs
are in `raw/`.

## Unary-binary increasing trees (word length n)

| n  | A245898 (avoid 231) | A245899 (avoid 312) | A245900 (avoid 321) |
|----|--------------------:|--------------------:|--------------------:|
| 9  | 667    | 222    | 753    |
| 10 | 2098   | 544    | 2439   |
| 11 | 6788   | 1601   | 8095   |
| 12 | 22349  | 4095   | 27350  |
| 13 | 74969  | 12416  | 93885  |
| 14 | 254848 | 33785  | 326396 |

## Increasing full binary trees (word length 2k−1)

| length | A245901 (avoid 231) | A245902 (avoid 312) | A245903 (avoid 321) |
|--------|--------------------:|--------------------:|--------------------:|
| 11 | 6788   | 1601   | 8048    |
| 13 | 74969  | 12416  | 92716   |
| 15 | 877865 | 105769 | 1125054 |

## Proven identities (see `../docs/THEOREMS.md` and `../lean/`)

* **A245899(n) = A246747(n)** for all n (Theorem A) — so A245899 inherits
  A246747's Catalan-convolution recurrence and 1000-term b-file.
* **A245902(k) = A245899(2k−1)** for all k (Theorem A corollary).
* **A245901(k) = A245898(2k−1)** for all k (Theorem B).
* For pattern **321 the analogous identity is false**: at length 11 there
  are 8095 unary-binary words vs. 8048 full-binary words; the 47 witnesses
  are listed in `certificates/certificate_321_n11.txt`.
