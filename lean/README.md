# Machine-Checked Proofs (Lean 4)

Complete formalizations of Theorem A and Theorem B from `../docs/THEOREMS.md`,
verified by the Lean 4 kernel. **No `sorry`, no extra axioms**: both theorems
depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), as confirmed by the
`#print axioms` audit in `BfsWords/Sanity.lean`.

## Main results

```lean
-- BfsWords/TheoremA.lean
theorem theoremA {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has312 w)
    (hne : w ≠ []) : UBWord w ↔ HeapCond w

-- BfsWords/TheoremB.lean
theorem theoremB {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has231 w)
    (hodd : w.length % 2 = 1) (h : UBWord w) : BWord w
```

`UBWord w` / `BWord w`: `w` is the BFS reading word of an increasing
unary-binary / full binary tree (levels + order-preserving capped matchings,
`BfsWords/Defs.lean`). `HeapCond w`: the plain binary-heap array condition
`w[(i-1)/2] < w[i]`. Patterns are subsequence predicates (`Has312`, `Has231`).

Theorem A settles the OEIS-recorded conjecture A245899 = A246747 (the word
sets coincide — the bijection is the identity), plus A245902(k) = A245899(2k−1).
Theorem B settles A245901(k) = A245898(2k−1).

## The semantic bridge (no trust in encodings required)

`UBWord`/`BWord` are stated via level blocks and matchings.  To remove any
doubt that these capture "BFS word of an increasing tree",
`BfsWords/Trees.lean` defines **genuine rooted plane trees** — an inductive
type `LTree` with labeled nodes and ordered children — together with the
predicates `Inc` (child labels exceed parents), `UB` (≤ 2 children),
`FB` (0 or 2 children), and `levelOrder` (the reading word, level by level,
left to right — verbatim the OEIS definition).  Then it proves, in Lean:

```lean
theorem ubword_iff_tree : UBWord w ↔ ∃ t, Inc t ∧ UB t ∧ levelOrder [t] = w
theorem bword_iff_tree  : BWord w  ↔ ∃ t, Inc t ∧ FB t ∧ levelOrder [t] = w

theorem theoremA_trees :  -- Theorem A on genuine trees
    (∃ t, Inc t ∧ UB t ∧ levelOrder [t] = w) ↔ HeapCond w
theorem theoremB_trees :  -- Theorem B on genuine trees
    (∃ t, Inc t ∧ UB t ∧ levelOrder [t] = w) →
    (∃ t, Inc t ∧ FB t ∧ levelOrder [t] = w)
```

All six named results pass the axiom audit (standard axioms only).  The
remaining definitions (`Inc`, `UB`, `FB`, `levelOrder`, `HeapCond`,
`Has312`/`Has231` as subsequence patterns) are each a few self-evident
lines — there is no further encoding to trust.

## File map

| File | Content |
|---|---|
| `BfsWords/Defs.lean` | `Feas`, `FeasB`, `Chain`, `ChainB`, words, patterns, heap condition |
| `BfsWords/Basic.lean` | toolbox: append/split/drop lemmas, sublists, Nodup |
| `BfsWords/Balanced.lean` | Lemma A1 (balanced matching, the 312 engine) |
| `BfsWords/TheoremA.lean` | Theorem A, both directions, incl. the dyadic construction |
| `BfsWords/Cascade.lean` | promotion cascade `chain_plus` (unconditional T+), depth measure |
| `BfsWords/B231.lean` | Lemmas B3 (odd extension) & B4 (even fibers) — the 231 engine |
| `BfsWords/TheoremB.lean` | evenization by depth induction, Theorem B |
| `BfsWords/Trees.lean` | genuine rooted trees, `levelOrder`, the semantic bridge, `theoremA_trees`/`theoremB_trees` |
| `BfsWords/Sanity.lean` | axiom audit (6 results) + concrete witness examples |

## Verify yourself

```sh
cd lean && lake build       # requires elan; toolchain pinned in lean-toolchain
```

A successful build **is** the proof: the Lean kernel checks every step.
The build also prints the axiom audit for both theorems.

## A note on the formalization

Formalizing simplified the mathematics. The informal Theorem A proof needed
a case analysis forcing dyadic level sizes; the Lean proof replaced it with
one telescoping invariant (`s_{j+1} ≤ 2·s_j`, i.e. `|prev| ≤ |pre| + 1`)
plus floor-monotonicity, after which a single 312-triple closes every gap.
Lemmas B3/B4's explicit "chain-shift" of the informal proof dissolved into
plain structural inductions where the shift emerges from recursion.
