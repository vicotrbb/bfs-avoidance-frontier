# Lean 4 formalization

Toolchain: Lean 4.24.0, with no external library dependencies.

```sh
cd lean
lake build
```

## General branching bounds

`BfsWords/ParentSequence.lean` defines the global parent-sequence constraints and proves:

- `parent_theoremA_iff`: for a distinct-label 312-avoiding word and positive k, existence of an increasing parent sequence of capacity k is equivalent to the complete k-ary heap inequalities.
- `parent_theoremB`: at length k*m+1, a 231-avoiding increasing parent sequence regroups into a valid increasing full parent sequence.
- `regroup_full_children`: the children of each used parent are precisely the k indices in one complete consecutive block.

The parent-sequence capacity predicate bounds the span of equal-parent indices. Monotonicity makes this equivalent to bounding each parent's fiber size. Fullness records exact equality of fibers with blocks. See `../docs/GENERAL_K_FORMALIZATION.md` for the theorem inventory.

The arbitrary-k reconstruction as an ordered inductive tree is proved mathematically in the paper. The general-k Lean statements use parent sequences; they do not claim an additional general tree bridge.

## Binary inductive trees

The original level-matching development is retained:

- `theoremA`: unary-binary word realizability is equivalent to the binary heap condition under 312 avoidance, distinct labels, and nonemptiness.
- `theoremB`: odd-length 231-avoiding unary-binary words are full binary words.
- `ubword_iff_tree` and `bword_iff_tree`: semantic bridges to an inductive ordered labeled tree type, its increasing and degree predicates, and its breadth-first traversal.
- `theoremA_trees` and `theoremB_trees`: the binary results stated on those inductive trees.

Auxiliary modules retain balanced matching, the unconditional binary promotion cascade `chain_plus`, and the original parity lemmas. These are additional proved statements; the revised paper's main arguments use parent sequences directly.

## Axiom audit

`Sanity.lean` imports both developments and prints axiom dependencies for nine statements. The principal results depend only on `propext`, `Classical.choice`, and `Quot.sound`. `regroup_full_children` uses `propext` and `Quot.sound`. No admitted proofs or additional axioms are present.

The formal statements establish the mathematical properties encoded by their definitions. The enumerator outputs and b-files are separately checked by the Python artifact verifier.
