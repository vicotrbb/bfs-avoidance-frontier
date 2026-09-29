# General branching bounds in Lean

The module `lean/BfsWords/ParentSequence.lean` formalizes the two general branching results using the global BFS parent sequence. It imports `BfsWords.Basic` and uses the existing `Has312`, `Has231`, and `List.Nodup` predicates. It introduces no dependencies, additional axioms, or admitted proofs.

## Representation

All word positions are zero based. Nonroot index `t` denotes word position `t + 1`; its parent has word position `p t`. `ParentSequence n k p` requires the parent to precede the child, requires parents to be nondecreasing, and bounds each equal-parent interval by `k` positions. Because the sequence is nondecreasing, its fibers are intervals, so the last condition is exactly a bound of `k` on the number of children per parent. `ParentIncreasing w p` requires every parent label to be smaller than its child label.

The branching bound may be any positive integer. The degenerate bound `k = 1` is therefore included as well as all usual branching bounds.

## Proved statements

- `ParentSequence.heap_parent_le`: the complete-heap parent `t / k` is at most the parent index in any valid realization.
- `parent_theoremA`: a distinct-label, 312-avoiding word with an increasing parent sequence satisfies every complete `k`-ary heap inequality.
- `heap_parent_valid`: the complete heap is itself a valid parent sequence.
- `parent_theoremA_iff`: existence of an increasing parent sequence is equivalent to the complete-heap inequalities, under distinct labels and 312 avoidance.
- `regroup_valid`: assigning each consecutive block to its first vertex's former parent preserves the parent-sequence constraints.
- `regroup_increasing`: the new edges increase when the labels are distinct and avoid 231.
- `regroup_fibers`: two children receive the same new parent if and only if they belong to the same block.
- `parent_theoremB`: when the word length is `k * m + 1`, regrouping produces a valid increasing full parent sequence.
- `regroup_full_children`: every used parent has precisely the children with nonroot indices `k * b + s`, where `s < k`.
- `full_block_member`: every index in each of those complete blocks belongs to the nonroot domain.

These statements establish the complete parent-sequence arguments, including both directions of heap collapse and the exact child groups in full collapse. The general branching results use the parent-sequence representation directly. The existing binary results additionally have their established bridge to inductive trees in `Trees.lean`. A corresponding general branching bridge to an inductive tree type is not part of this module.

## Validation

The following command succeeded with Lean 4.24.0:

```sh
cd lean
lake env lean BfsWords/ParentSequence.lean
```

The file also compiled to an object file. Kernel axiom audits report:

```text
parent_theoremA_iff: [propext, Classical.choice, Quot.sound]
parent_theoremB: [propext, Classical.choice, Quot.sound]
regroup_full_children: [propext, Quot.sound]
```

The first two use only the same three standard axioms reported by the existing development. The exact-child statement uses two of those axioms.
