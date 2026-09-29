# Mathematical review of the revised manuscript

Date: September 29, 2026.

A separate research agent in the same revision workflow reviewed the manuscript against the Lean definitions and primary sources. The review found no mathematical defects in:

- The parent-sequence reconstruction of ordered BFS trees.
- The capacity argument and both directions of general-k heap collapse.
- The full-degree block construction, exact child groups, and linear-time conversion from a supplied realization.
- The length-4 heap counterexample and the direct full binary obstruction at length 11.
- The exponential-growth corollary, admissible full-tree subsequence, and full binary sequence-index rate 16.
- The unconditional promotion lemma for arbitrary maximum outdegree.
- The distinction between general parent-sequence formalization and binary inductive-tree formalization.

The primary-source checks used Defant's Theorem 2.1 and Levin et al.'s Theorems 5 and 6. The independent recognizer audit is retained as `python/verify_parent_dp.py` and its result is in `parent-dp.json`: 47,304 comparisons and 1,874 reconstructed witnesses passed.

The integration review initially found that the old Makefile and umbrella Lean imports did not yet include the new checks. These were updated before the final integrated build. A helper-name collision between the new and old Lean modules was resolved by giving the new helper a parent-sequence-specific name. The final integrated axiom audit is recorded in `lean.log`.

This record describes an internal mathematical and implementation review, not journal peer review.
