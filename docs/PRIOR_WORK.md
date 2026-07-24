# Prior-Work / Novelty Audit (July 24, 2026)

Question: are Theorems A and B in THEOREMS.md new, or already in the literature?

## What exists

- **Levin, Pudwell, Riehl, Sandberg**, *Pattern avoidance in k-ary heaps*,
  Australas. J. Combin. 64.1 (2016) 120–139. Introduced the objects; counted
  pattern-avoiding **heaps** (fixed complete shape) for all length-3 pattern
  sets except {321}. Source of A246747 and its Catalan recurrence. Did NOT
  treat arbitrary unary-binary trees, and left the A245899 = A246747
  connection as an observed coincidence.
- **Colin Defant**, *Proofs of conjectures about pattern-avoiding linear
  extensions*, DMTCS 21:4 #16 (2019), arXiv:1905.02309. Proves a DIFFERENT
  LPRS conjecture: the growth rate lim |H²_n(321)|^{1/n} = 4 for 321-avoiding
  binary heaps. No unary-binary trees, no word-set equalities.
- **Bettinelli, Fusy, Mailler, Randazzo**, *A bijective study of basketball
  walks* (arXiv:1611.01478). Treats the **213** pattern only (tree-counting
  A245889 family, bijection with walks). Its Lemma 7 gives a validity
  criterion for labelings of a fixed unary-binary tree — related machinery,
  different theorems, different pattern.
- **Sela Fried**, *Proofs of some conjectures from the OEIS* (arXiv:2410.07237):
  covers 17 sequences, none of ours.

## Evidence the theorems were open until now

1. The live OEIS entries (checked July 24, 2026): A246747 still carries the
   cross-reference "**May be equal to A245899**" — OEIS's standard phrasing
   for an unproven observation — and A245899 still carries "A245902 appears
   to be the odd-indexed terms" plus the `more` keyword and no formula.
   OEIS editors routinely update entries when equalities are proven.
2. Targeted searches for the sequence IDs (A245899, A246747, A245898,
   A245901–A245903) in combination with "proof"/"conjecture"/"bijection"
   return no resolving paper.
3. The citation trail of LPRS 2016 (Defant, shrub-forest papers, rooted-forest
   pattern papers) contains no result on word-set equalities between
   unary-binary-tree BFS words and heap words, nor on odd-length
   full-binary collapses.

## Final arXiv full-text sweep (July 24, 2026)

The relevant literature on arXiv is small enough to enumerate completely:

- Query `"k-ary heaps" pattern` → **exactly one paper**: Defant 2019
  (arXiv:1905.02309), which proves the 321-heap growth-rate conjecture —
  read in full, no overlap with Theorems A/B.
- Query `"breadth-first search reading word"` → **zero papers**.
- Query `"increasing unary-binary trees"` → **exactly one paper**: the
  basketball-walks paper (arXiv:1611.01478), 213 pattern only —
  text extracted and checked, no overlap.
- Queries for the sequence IDs A245898/A245899/A245901/A245903 across
  arXiv full text → no genuine hits (two false positives checked and
  dismissed: arXiv:2205.10163 on perfect powers, arXiv:2410.16334 on
  involution asymptotics).

## Conclusion

To the best of a thorough same-day web/OEIS/arXiv audit: **Theorem A
(312 heap collapse, proving A245899 = A246747 and A245902(k) = A245899(2k−1))
and Theorem B (231 parity collapse, proving A245901(k) = A245898(2k−1)) are
new.** The questions were known (recorded as conjectures in OEIS since
2014); the proofs were not. Residual risk: an unindexed thesis or preprint —
a standard arXiv/journal check at submission time is recommended.
