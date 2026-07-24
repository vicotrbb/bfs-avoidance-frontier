/-
BFS reading words of increasing trees: core definitions.

A "realization" of a word as the BFS word of an increasing unary-binary
(resp. full binary) tree is presented level by level:

* `Feas P C`  : the children block `C` splits into consecutive groups of
  size ≤ 2, one group per parent of `P` in order, each child larger than
  its parent.  This is exactly "the nodes listed in `C` can be the next
  BFS level below the level `P` in an increasing unary-binary tree".
* `FeasB P C` : same with group sizes 0 or 2 (full binary trees).
* `Chain P ls` / `ChainB P ls` : successive levels `ls` below level `P`.
* `UBWord w` / `BWord w` : `w` is the BFS word of an increasing
  unary-binary (resp. full binary) tree.

Patterns are stated via `List.Sublist`:
* `Has312 w` : some subsequence `[a,b,c]` of `w` has `b < c < a`.
* `Has231 w` : some subsequence `[a,b,c]` of `w` has `c < a < b`.
-/

namespace BfsWords

/-- Children `C` split into consecutive groups (≤ 2 each), one group per
parent in order; every child exceeds its parent. -/
inductive Feas : List Nat → List Nat → Prop
  | nil : Feas [] []
  | cons {p : Nat} {P g C : List Nat} :
      g.length ≤ 2 → (∀ c ∈ g, p < c) → Feas P C → Feas (p :: P) (g ++ C)

/-- Full-binary variant: every group has size 0 or 2. -/
inductive FeasB : List Nat → List Nat → Prop
  | nil : FeasB [] []
  | cons {p : Nat} {P g C : List Nat} :
      (g.length = 0 ∨ g.length = 2) → (∀ c ∈ g, p < c) → FeasB P C →
      FeasB (p :: P) (g ++ C)

/-- Successive nonempty levels `ls` hanging below the level `P`. -/
inductive Chain : List Nat → List (List Nat) → Prop
  | nil {P} : Chain P []
  | cons {P L ls} : L ≠ [] → Feas P L → Chain L ls → Chain P (L :: ls)

/-- Full-binary chains. -/
inductive ChainB : List Nat → List (List Nat) → Prop
  | nil {P} : ChainB P []
  | cons {P L ls} : L ≠ [] → FeasB P L → ChainB L ls → ChainB P (L :: ls)

/-- `w` is the BFS word of an increasing unary-binary tree. -/
def UBWord (w : List Nat) : Prop :=
  ∃ h ls, w = h :: ls.flatten ∧ Chain [h] ls

/-- `w` is the BFS word of an increasing full binary tree. -/
def BWord (w : List Nat) : Prop :=
  ∃ h ls, w = h :: ls.flatten ∧ ChainB [h] ls

/-- `w` contains the classical pattern 312. -/
def Has312 (w : List Nat) : Prop :=
  ∃ a b c : Nat, [a, b, c].Sublist w ∧ b < c ∧ c < a

/-- `w` contains the classical pattern 231. -/
def Has231 (w : List Nat) : Prop :=
  ∃ a b c : Nat, [a, b, c].Sublist w ∧ c < a ∧ a < b

/-- Binary-heap condition, 0-indexed: the parent of position `i ≥ 1` is
position `(i-1)/2`. -/
def HeapCond (w : List Nat) : Prop :=
  ∀ i, 0 < i → (h : i < w.length) → w[(i - 1) / 2]'(by omega) < w[i]

end BfsWords
