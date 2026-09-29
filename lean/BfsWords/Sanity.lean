/-
Sanity checks.

1. `#print axioms` ; verifies both theorems depend on nothing beyond the
   three standard Lean axioms (no `sorry`).
2. Concrete witnesses tying the formal definitions to the intended
   objects, machine-checked by `decide` / explicit constructors:
   * the heap condition and pattern predicates evaluate correctly;
   * a known BFS word is `UBWord`;
   * `theoremA`/`theoremB` instantiate on concrete words.
-/
import BfsWords.Trees
import BfsWords.ParentSequence

namespace BfsWords

-- The word 1 4 2 5 3 (0-indexed heap condition holds: parents 1,1,4,4→2?).
-- As a heap array [1,4,2,5,3]: parent of index 1 is 0 (1<4 ✓), of 2 is 0
-- (1<2 ✓), of 3 is 1 (4<5 ✓), of 4 is 1 (4>3 ✗) ; NOT a heap word.
example : ¬ HeapCond [1, 4, 2, 5, 3] := by
  intro h
  have := h 4 (by omega) (by simp)
  simp at this

-- [1,2,3,4,5] is a heap word.
example : HeapCond [1, 2, 3, 4, 5] := by
  intro i hi hlen
  simp at hlen
  rcases i with _ | _ | _ | _ | _ | i
  · omega
  · simp
  · simp
  · simp
  · simp
  · omega

-- [1,4,2,5,3] IS a BFS word of an increasing unary-binary tree:
-- levels (1)(4,2)(5,3) with 4→5? no: 5>4 as child of 4, 3>2 as child of 2.
example : UBWord [1, 4, 2, 5, 3] := by
  refine ⟨1, [[4, 2], [5, 3]], by simp, ?_⟩
  refine Chain.cons (by simp) ?_ (Chain.cons (by simp) ?_ Chain.nil)
  · -- Feas [1] [4,2]
    have : Feas [1] ([4, 2] ++ []) :=
      Feas.cons (by simp) (by intro c hc; simp at hc; omega) Feas.nil
    simpa using this
  · -- Feas [4,2] [5,3] : group [5] under 4, group [3] under 2
    have h2 : Feas [2] ([3] ++ []) :=
      Feas.cons (g := [3]) (by simp) (by intro c hc; simp at hc; omega) Feas.nil
    have : Feas (4 :: [2]) ([5] ++ [3]) :=
      Feas.cons (g := [5]) (by simp) (by intro c hc; simp at hc; omega)
        (by simpa using h2)
    simpa using this

-- [1,4,2,5,3] contains 312? Its subsequences: 4,2,5 has b=2<c=5? pattern
-- (4,2,5): b<c and c<a fails (5>4). (4,2,3): 2<3<4 ✓ ; a 312 occurrence.
example : Has312 [1, 4, 2, 5, 3] := by
  refine ⟨4, 2, 3, ?_, by omega, by omega⟩
  decide

-- Consistency of Theorem A on this word: it is UBWord but not HeapCond,
-- so by `theoremA` it must NOT avoid 312 ; matching the example above.

-- A 231-avoiding odd-length example for Theorem B:
-- w = [1,2,4,3,5]: levels (1)(2)(4,3)(5)? or (1)(2,4)(3,5)...
example : UBWord [1, 2, 4, 3, 5] := by
  refine ⟨1, [[2, 4], [3, 5]], by simp, ?_⟩
  refine Chain.cons (by simp) ?_ (Chain.cons (by simp) ?_ Chain.nil)
  · have : Feas [1] ([2, 4] ++ []) :=
      Feas.cons (by simp) (by intro c hc; simp at hc; omega) Feas.nil
    simpa using this
  · -- children (3,5) of parents (2,4): 3>2, 5>4
    have h2 : Feas [4] ([5] ++ []) :=
      Feas.cons (g := [5]) (by simp) (by intro c hc; simp at hc; omega)
        Feas.nil
    have : Feas (2 :: [4]) ([3] ++ [5]) :=
      Feas.cons (g := [3]) (by simp) (by intro c hc; simp at hc; omega)
        (by simpa using h2)
    simpa using this

-- Full binary witness for the same word, as Theorem B promises
-- (231-avoidance of [1,2,4,3,5]: ascent pairs all have later elements
-- above the smaller element ; no (c < a < b) subsequence).
example : BWord [1, 2, 4, 3, 5] := by
  refine ⟨1, [[2, 4], [3, 5]], by simp, ?_⟩
  refine ChainB.cons (by simp) ?_ (ChainB.cons (by simp) ?_ ChainB.nil)
  · have : FeasB [1] ([2, 4] ++ []) :=
      FeasB.cons (Or.inr rfl) (by intro c hc; simp at hc; omega) FeasB.nil
    simpa using this
  · -- (3,5) both under parent 2? 3>2, 5>2 ✓, parent 4 gets none
    have h2 : FeasB [4] ([] ++ []) :=
      FeasB.cons (Or.inl rfl) (by simp) FeasB.nil
    have : FeasB (2 :: [4]) ([3, 5] ++ []) :=
      FeasB.cons (Or.inr rfl) (by intro c hc; simp at hc; omega)
        (by simpa using h2)
    simpa using this

#print axioms parent_theoremA_iff
#print axioms parent_theoremB
#print axioms regroup_full_children
#print axioms theoremA
#print axioms theoremB
#print axioms ubword_iff_tree
#print axioms bword_iff_tree
#print axioms theoremA_trees
#print axioms theoremB_trees

-- Concrete tree-level sanity: the increasing unary-binary tree
--      1
--     / \
--    4   2
--    |   |
--    5   3
-- has level-order word [1,4,2,5,3].
example : levelOrder [.node 1 [.node 4 [.node 5 []], .node 2 [.node 3 []]]] =
    [1, 4, 2, 5, 3] := by
  simp [levelOrder, LTree.label, LTree.children]

end BfsWords
