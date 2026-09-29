/-
Closing the semantic gap: actual rooted plane trees.

`UBWord`/`BWord` (Defs.lean) encode realizability via level blocks and
matchings.  Here we define honest trees ; an inductive type with labels and
ordered children lists ; together with:

* `Inc t`  : every child's label exceeds its parent's label (increasing);
* `UB t`   : every node has at most 2 children (unary-binary);
* `FB t`   : every node has 0 or 2 children (full binary);
* `levelOrder F` : the reading word of a forest, level by level, left to
  right ; verbatim the definition in OEIS A245898–A245903 ("reading the
  tree left to right by levels, starting with the root").

Main results (proved below):

* `ubword_iff_tree : UBWord w ↔ ∃ t, Inc t ∧ UB t ∧ levelOrder [t] = w`
* `bword_iff_tree  : BWord w  ↔ ∃ t, Inc t ∧ FB t ∧ levelOrder [t] = w`

Hence the theorems `theoremA`/`theoremB` are statements about genuine
increasing trees, not merely about the encoded chains.
-/
import BfsWords.TheoremB

namespace BfsWords

/-- Rooted plane trees with natural-number labels. -/
inductive LTree where
  | node : Nat → List LTree → LTree

namespace LTree

def label : LTree → Nat
  | node x _ => x

def children : LTree → List LTree
  | node _ c => c

/-- Increasing: every child's label exceeds its parent's, recursively. -/
inductive Inc : LTree → Prop
  | mk (x : Nat) (c : List LTree) :
      (∀ t ∈ c, x < t.label) → (∀ t ∈ c, Inc t) → Inc (node x c)

/-- Unary-binary: every node has at most two children. -/
inductive UB : LTree → Prop
  | mk (x : Nat) (c : List LTree) :
      c.length ≤ 2 → (∀ t ∈ c, UB t) → UB (node x c)

/-- Full binary: every node has zero or two children. -/
inductive FB : LTree → Prop
  | mk (x : Nat) (c : List LTree) :
      (c.length = 0 ∨ c.length = 2) → (∀ t ∈ c, FB t) → FB (node x c)

end LTree

open LTree

theorem FeasB.length_le {P C : List Nat} (h : FeasB P C) :
    C.length ≤ 2 * P.length := by
  induction h with
  | nil => simp
  | @cons p P g C hg hgt hrec ih => simp; omega

mutual
  def sz : LTree → Nat
    | .node _ c => 1 + szF c
  def szF : List LTree → Nat
    | [] => 0
    | t :: ts => sz t + szF ts
end

theorem szF_append (F G : List LTree) : szF (F ++ G) = szF F + szF G := by
  induction F with
  | nil => simp [szF]
  | cons t ts ih => simp [szF, ih]; omega

theorem sz_pos (t : LTree) : 1 ≤ sz t := by
  cases t with
  | node x c => simp [sz]

theorem szF_children_lt : ∀ (F : List LTree), F ≠ [] →
    szF (F.flatMap children) < szF F := by
  intro F hne
  induction F with
  | nil => exact absurd rfl hne
  | cons t ts ih =>
      cases t with
      | node x c =>
          rw [List.flatMap_cons, szF_append]
          have h1 : szF (ts.flatMap children) ≤ szF ts := by
            cases ts with
            | nil => simp [szF]
            | cons u us => exact Nat.le_of_lt (ih (by simp))
          simp only [szF, sz, children]
          omega

/-- Level-order reading word of a forest. -/
def levelOrder : List LTree → List Nat
  | [] => []
  | t :: ts =>
      (t :: ts).map label ++ levelOrder ((t :: ts).flatMap children)
  termination_by F => szF F
  decreasing_by exact szF_children_lt _ (by simp)

/-- Level decomposition of a forest. -/
def levelsOf : List LTree → List (List Nat)
  | [] => []
  | t :: ts =>
      (t :: ts).map label :: levelsOf ((t :: ts).flatMap children)
  termination_by F => szF F
  decreasing_by exact szF_children_lt _ (by simp)

theorem levelOrder_eq_flatten : ∀ (n : Nat) (F : List LTree), szF F ≤ n →
    (levelsOf F).flatten = levelOrder F := by
  intro n
  induction n with
  | zero =>
      intro F hsz
      cases F with
      | nil => simp [levelsOf, levelOrder]
      | cons t ts =>
          exfalso
          have := sz_pos t
          simp [szF] at hsz
          omega
  | succ n ih =>
      intro F hsz
      cases F with
      | nil => simp [levelsOf, levelOrder]
      | cons t ts =>
          simp only [levelsOf, levelOrder, List.flatten_cons]
          rw [ih ((t :: ts).flatMap children)
            (by have := szF_children_lt (t :: ts) (by simp); omega)]

/-- From a forest to a chain: one `Feas` step between consecutive levels. -/
theorem feas_of_forest : ∀ (F : List LTree),
    (∀ t ∈ F, Inc t) → (∀ t ∈ F, UB t) →
    Feas (F.map label) ((F.flatMap children).map label) := by
  intro F
  induction F with
  | nil => simpa using Feas.nil
  | cons t ts ih =>
      intro hinc hub
      cases t with
      | node x c =>
          have hI : Inc (.node x c) := hinc _ (by simp)
          have hU : UB (.node x c) := hub _ (by simp)
          cases hI with
          | mk _ _ hlab hIc =>
              cases hU with
              | mk _ _ hlen hUc =>
                  have hrec := ih (fun u hu => hinc u (by simp [hu]))
                    (fun u hu => hub u (by simp [hu]))
                  have : Feas (x :: ts.map label)
                      ((c.map label) ++ ((ts.flatMap children).map label)) :=
                    Feas.cons (by simpa using hlen)
                      (by
                        intro y hy
                        simp at hy
                        obtain ⟨u, hu, rfl⟩ := hy
                        exact hlab u hu) hrec
                  simpa [children] using this

/-- Full-binary variant. -/
theorem feasB_of_forest : ∀ (F : List LTree),
    (∀ t ∈ F, Inc t) → (∀ t ∈ F, FB t) →
    FeasB (F.map label) ((F.flatMap children).map label) := by
  intro F
  induction F with
  | nil => simpa using FeasB.nil
  | cons t ts ih =>
      intro hinc hfb
      cases t with
      | node x c =>
          have hI : Inc (.node x c) := hinc _ (by simp)
          have hU : FB (.node x c) := hfb _ (by simp)
          cases hI with
          | mk _ _ hlab hIc =>
              cases hU with
              | mk _ _ hlen hUc =>
                  have hrec := ih (fun u hu => hinc u (by simp [hu]))
                    (fun u hu => hfb u (by simp [hu]))
                  have : FeasB (x :: ts.map label)
                      ((c.map label) ++ ((ts.flatMap children).map label)) :=
                    FeasB.cons (by simpa using hlen)
                      (by
                        intro y hy
                        simp at hy
                        obtain ⟨u, hu, rfl⟩ := hy
                        exact hlab u hu) hrec
                  simpa [children] using this

/-- Subtree conditions propagate to the child forest. -/
theorem forest_conds_children {F : List LTree}
    (hinc : ∀ t ∈ F, Inc t) (hub : ∀ t ∈ F, UB t) :
    (∀ t ∈ F.flatMap children, Inc t) ∧ (∀ t ∈ F.flatMap children, UB t) := by
  constructor
  · intro u hu
    simp [List.mem_flatMap] at hu
    obtain ⟨t, ht, hu⟩ := hu
    have := hinc t ht
    cases this with
    | mk x c hlab hIc => exact hIc u (by simpa [children] using hu)
  · intro u hu
    simp [List.mem_flatMap] at hu
    obtain ⟨t, ht, hu⟩ := hu
    have := hub t ht
    cases this with
    | mk x c hlen hUc => exact hUc u (by simpa [children] using hu)

theorem forest_conds_childrenB {F : List LTree}
    (hinc : ∀ t ∈ F, Inc t) (hfb : ∀ t ∈ F, FB t) :
    (∀ t ∈ F.flatMap children, Inc t) ∧ (∀ t ∈ F.flatMap children, FB t) := by
  constructor
  · intro u hu
    simp [List.mem_flatMap] at hu
    obtain ⟨t, ht, hu⟩ := hu
    have := hinc t ht
    cases this with
    | mk x c hlab hIc => exact hIc u (by simpa [children] using hu)
  · intro u hu
    simp [List.mem_flatMap] at hu
    obtain ⟨t, ht, hu⟩ := hu
    have := hfb t ht
    cases this with
    | mk x c hlen hUc => exact hUc u (by simpa [children] using hu)

/-- Forest ⇒ chain. -/
theorem chain_of_forest : ∀ (n : Nat) (F : List LTree), szF F ≤ n →
    (∀ t ∈ F, Inc t) → (∀ t ∈ F, UB t) →
    Chain (F.map label) (levelsOf (F.flatMap children)) := by
  intro n
  induction n with
  | zero =>
      intro F hsz _ _
      have hF : F = [] := by
        cases F with
        | nil => rfl
        | cons t ts =>
            exfalso
            have := sz_pos t
            simp [szF] at hsz
            omega
      subst hF
      simp only [List.flatMap_nil, levelsOf]
      exact Chain.nil
  | succ n ih =>
      intro F hsz hinc hub
      cases hC : F.flatMap children with
      | nil => simp only [levelsOf]; exact Chain.nil
      | cons u us =>
          simp only [levelsOf]
          have hconds := forest_conds_children hinc hub
          refine Chain.cons (by simp) ?_ ?_
          · have h := feas_of_forest F hinc hub
            rw [hC] at h
            exact h
          · have hlt : szF (F.flatMap children) < szF F := by
              apply szF_children_lt
              cases F with
              | nil => simp at hC
              | cons t ts => simp
            have h := ih (F.flatMap children) (by omega)
              hconds.1 hconds.2
            rw [hC] at h
            exact h

/-- Full-binary forest ⇒ chain. -/
theorem chainB_of_forest : ∀ (n : Nat) (F : List LTree), szF F ≤ n →
    (∀ t ∈ F, Inc t) → (∀ t ∈ F, FB t) →
    ChainB (F.map label) (levelsOf (F.flatMap children)) := by
  intro n
  induction n with
  | zero =>
      intro F hsz _ _
      have hF : F = [] := by
        cases F with
        | nil => rfl
        | cons t ts =>
            exfalso
            have := sz_pos t
            simp [szF] at hsz
            omega
      subst hF
      simp only [List.flatMap_nil, levelsOf]
      exact ChainB.nil
  | succ n ih =>
      intro F hsz hinc hfb
      cases hC : F.flatMap children with
      | nil => simp only [levelsOf]; exact ChainB.nil
      | cons u us =>
          simp only [levelsOf]
          have hconds := forest_conds_childrenB hinc hfb
          refine ChainB.cons (by simp) ?_ ?_
          · have h := feasB_of_forest F hinc hfb
            rw [hC] at h
            exact h
          · have hlt : szF (F.flatMap children) < szF F := by
              apply szF_children_lt
              cases F with
              | nil => simp at hC
              | cons t ts => simp
            have h := ih (F.flatMap children) (by omega)
              hconds.1 hconds.2
            rw [hC] at h
            exact h

/-- Rebuild a parent forest from a feasibility certificate and the child
forest. -/
theorem forest_of_feas : ∀ {P C : List Nat} (_ : Feas P C)
    (F' : List LTree), F'.map label = C →
    (∀ t ∈ F', Inc t) → (∀ t ∈ F', UB t) →
    ∃ F : List LTree, F.map label = P ∧ (∀ t ∈ F, Inc t) ∧
      (∀ t ∈ F, UB t) ∧ F.flatMap children = F' := by
  intro P C h
  induction h with
  | nil =>
      intro F' hmap _ _
      have hF' : F' = [] := by
        cases F' with
        | nil => rfl
        | cons a b => simp at hmap
      exact ⟨[], by simp, by simp, by simp, by simp [hF']⟩
  | @cons p P g C hg hgt hrec ih =>
      intro F' hmap hinc hub
      -- split F' along |g|
      have hlen : F'.length = g.length + C.length := by
        have := congrArg List.length hmap
        simpa using this
      have hsplit : F' = F'.take g.length ++ F'.drop g.length :=
        (List.take_append_drop _ _).symm
      have hmap₁ : (F'.take g.length).map label = g := by
        have h1 : (F'.take g.length).map label = (F'.map label).take g.length :=
          (List.map_take ..)
        rw [h1, hmap]
        exact List.take_left' rfl
      have hmap₂ : (F'.drop g.length).map label = C := by
        have h1 : (F'.drop g.length).map label = (F'.map label).drop g.length :=
          (List.map_drop ..)
        rw [h1, hmap]
        exact List.drop_left' rfl
      obtain ⟨F, hFmap, hFinc, hFub, hFch⟩ := ih (F'.drop g.length) hmap₂
        (fun t ht => hinc t (List.mem_of_mem_drop ht))
        (fun t ht => hub t (List.mem_of_mem_drop ht))
      refine ⟨.node p (F'.take g.length) :: F, ?_, ?_, ?_, ?_⟩
      · simp [label, hFmap]
      · intro t ht
        simp at ht
        rcases ht with rfl | ht
        · exact Inc.mk p _ (by
            intro u hu
            have : u.label ∈ g := by
              rw [← hmap₁]; exact List.mem_map_of_mem hu
            exact hgt _ this)
            (fun u hu => hinc u (List.mem_of_mem_take hu))
        · exact hFinc t ht
      · intro t ht
        simp at ht
        rcases ht with rfl | ht
        · refine UB.mk p _ ?_ (fun u hu => hub u (List.mem_of_mem_take hu))
          have hlen1 : (F'.take g.length).length = g.length := by
            have := congrArg List.length hmap₁
            simpa using this
          rw [hlen1]
          exact hg
        · exact hFub t ht
      · simp [children, hFch]

/-- Full-binary variant. -/
theorem forest_of_feasB : ∀ {P C : List Nat} (_ : FeasB P C)
    (F' : List LTree), F'.map label = C →
    (∀ t ∈ F', Inc t) → (∀ t ∈ F', FB t) →
    ∃ F : List LTree, F.map label = P ∧ (∀ t ∈ F, Inc t) ∧
      (∀ t ∈ F, FB t) ∧ F.flatMap children = F' := by
  intro P C h
  induction h with
  | nil =>
      intro F' hmap _ _
      have hF' : F' = [] := by
        cases F' with
        | nil => rfl
        | cons a b => simp at hmap
      exact ⟨[], by simp, by simp, by simp, by simp [hF']⟩
  | @cons p P g C hg hgt hrec ih =>
      intro F' hmap hinc hfb
      have hlen : F'.length = g.length + C.length := by
        have := congrArg List.length hmap
        simpa using this
      have hmap₁ : (F'.take g.length).map label = g := by
        have h1 : (F'.take g.length).map label = (F'.map label).take g.length :=
          (List.map_take ..)
        rw [h1, hmap]
        exact List.take_left' rfl
      have hmap₂ : (F'.drop g.length).map label = C := by
        have h1 : (F'.drop g.length).map label = (F'.map label).drop g.length :=
          (List.map_drop ..)
        rw [h1, hmap]
        exact List.drop_left' rfl
      obtain ⟨F, hFmap, hFinc, hFfb, hFch⟩ := ih (F'.drop g.length) hmap₂
        (fun t ht => hinc t (List.mem_of_mem_drop ht))
        (fun t ht => hfb t (List.mem_of_mem_drop ht))
      refine ⟨.node p (F'.take g.length) :: F, ?_, ?_, ?_, ?_⟩
      · simp [label, hFmap]
      · intro t ht
        simp at ht
        rcases ht with rfl | ht
        · exact Inc.mk p _ (by
            intro u hu
            have : u.label ∈ g := by
              rw [← hmap₁]; exact List.mem_map_of_mem hu
            exact hgt _ this)
            (fun u hu => hinc u (List.mem_of_mem_take hu))
        · exact hFinc t ht
      · intro t ht
        simp at ht
        rcases ht with rfl | ht
        · refine FB.mk p _ ?_ (fun u hu => hfb u (List.mem_of_mem_take hu))
          have hlen1 : (F'.take g.length).length = g.length := by
            have := congrArg List.length hmap₁
            simpa using this
          rw [hlen1]
          exact hg
        · exact hFfb t ht
      · simp [children, hFch]

theorem map_label_leaves : ∀ (l : List Nat),
    List.map (label ∘ fun x => LTree.node x []) l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, Function.comp_apply, ih]
      rfl

theorem flatMap_children_leaves : ∀ (l : List Nat),
    ((l.map (fun x => LTree.node x [])).flatMap children) = [] := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih => simp [children, ih]

theorem levelOrder_leaves : ∀ (l : List Nat),
    levelOrder (l.map (fun x => LTree.node x [])) = l := by
  intro l
  cases l with
  | nil => simp [levelOrder]
  | cons a t =>
      simp only [List.map_cons, levelOrder]
      have h1 := flatMap_children_leaves (a :: t)
      simp only [List.map_cons] at h1
      rw [h1]
      simp only [levelOrder, List.append_nil, label]
      rw [List.map_map]
      rw [map_label_leaves t]

/-- Chain ⇒ forest. -/
theorem forest_of_chain : ∀ (ls : List (List Nat)) (prev : List Nat),
    Chain prev ls →
    ∃ F : List LTree, F.map label = prev ∧ (∀ t ∈ F, Inc t) ∧
      (∀ t ∈ F, UB t) ∧ levelOrder F = prev ++ ls.flatten := by
  intro ls
  induction ls with
  | nil =>
      intro prev _
      refine ⟨prev.map (fun x => .node x []),
        by rw [List.map_map]; exact map_label_leaves prev,
        ?_, ?_, ?_⟩
      · intro t ht
        simp at ht
        obtain ⟨x, _, rfl⟩ := ht
        exact Inc.mk x [] (by simp) (by simp)
      · intro t ht
        simp at ht
        obtain ⟨x, _, rfl⟩ := ht
        exact UB.mk x [] (by simp) (by simp)
      · rw [levelOrder_leaves]
        simp
  | cons L ls₀ ih =>
      intro prev hc
      cases hc with
      | cons hLne hfeas hchain =>
          obtain ⟨F', hmap', hinc', hub', hlo'⟩ := ih L hchain
          obtain ⟨F, hmap, hinc, hub, hch⟩ := forest_of_feas hfeas F' hmap'
            hinc' hub'
          refine ⟨F, hmap, hinc, hub, ?_⟩
          have hFne : F ≠ [] := by
            intro hcon
            rw [hcon] at hmap
            simp at hmap
            -- prev = [] forces L = [] via capacity, contradicting hLne
            have := hfeas.length_le
            rw [hmap] at this
            simp at this
            exact hLne (by
              cases L with
              | nil => rfl
              | cons a b => simp at this)
          cases hF : F with
          | nil => exact absurd hF hFne
          | cons f fs =>
              rw [← hF]
              have : levelOrder F = F.map label ++
                  levelOrder (F.flatMap children) := by
                rw [hF]; rw [levelOrder]
              rw [this, hch, hmap, hlo']
              simp [List.flatten_cons]

/-- Full-binary chain ⇒ forest. -/
theorem forest_of_chainB : ∀ (ls : List (List Nat)) (prev : List Nat),
    ChainB prev ls →
    ∃ F : List LTree, F.map label = prev ∧ (∀ t ∈ F, Inc t) ∧
      (∀ t ∈ F, FB t) ∧ levelOrder F = prev ++ ls.flatten := by
  intro ls
  induction ls with
  | nil =>
      intro prev _
      refine ⟨prev.map (fun x => .node x []),
        by rw [List.map_map]; exact map_label_leaves prev,
        ?_, ?_, ?_⟩
      · intro t ht
        simp at ht
        obtain ⟨x, _, rfl⟩ := ht
        exact Inc.mk x [] (by simp) (by simp)
      · intro t ht
        simp at ht
        obtain ⟨x, _, rfl⟩ := ht
        exact FB.mk x [] (by simp) (by simp)
      · rw [levelOrder_leaves]
        simp
  | cons L ls₀ ih =>
      intro prev hc
      cases hc with
      | cons hLne hfeas hchain =>
          obtain ⟨F', hmap', hinc', hfb', hlo'⟩ := ih L hchain
          obtain ⟨F, hmap, hinc, hfb, hch⟩ := forest_of_feasB hfeas F' hmap'
            hinc' hfb'
          refine ⟨F, hmap, hinc, hfb, ?_⟩
          have hFne : F ≠ [] := by
            intro hcon
            rw [hcon] at hmap
            simp at hmap
            have := hfeas.length_le
            rw [hmap] at this
            simp at this
            exact hLne (by
              cases L with
              | nil => rfl
              | cons a b => simp at this)
          cases hF : F with
          | nil => exact absurd hF hFne
          | cons f fs =>
              rw [← hF]
              have : levelOrder F = F.map label ++
                  levelOrder (F.flatMap children) := by
                rw [hF]; rw [levelOrder]
              rw [this, hch, hmap, hlo']
              simp [List.flatten_cons]

/-- **Semantic bridge, unary-binary**: the encoded predicate `UBWord` says
exactly "level-order reading word of an increasing unary-binary tree". -/
theorem ubword_iff_tree {w : List Nat} :
    UBWord w ↔ ∃ t : LTree, Inc t ∧ UB t ∧ levelOrder [t] = w := by
  constructor
  · rintro ⟨hd, ls, hw, hc⟩
    obtain ⟨F, hmap, hinc, hub, hlo⟩ := forest_of_chain ls [hd] hc
    cases F with
    | nil => simp at hmap
    | cons t fs =>
        cases fs with
        | nil =>
            refine ⟨t, hinc t (by simp), hub t (by simp), ?_⟩
            rw [hlo, hw]
            rfl
        | cons u us => simp at hmap
  · rintro ⟨t, hinc, hub, hlo⟩
    cases t with
    | node x c =>
        refine ⟨x, levelsOf c, ?_, ?_⟩
        · rw [← hlo]
          have h1 : levelOrder [LTree.node x c] =
              x :: levelOrder c := by
            rw [levelOrder]
            simp [label, children]
          rw [h1, levelOrder_eq_flatten (szF c) c (Nat.le_refl _)]
        · have h := chain_of_forest (szF [LTree.node x c]) [LTree.node x c]
            (Nat.le_refl _) (by simpa using hinc) (by simpa using hub)
          have hch : ([LTree.node x c] : List LTree).flatMap children = c := by
            simp [children]
          rw [hch] at h
          simpa [label] using h

/-- **Semantic bridge, full binary**. -/
theorem bword_iff_tree {w : List Nat} :
    BWord w ↔ ∃ t : LTree, Inc t ∧ FB t ∧ levelOrder [t] = w := by
  constructor
  · rintro ⟨hd, ls, hw, hc⟩
    obtain ⟨F, hmap, hinc, hfb, hlo⟩ := forest_of_chainB ls [hd] hc
    cases F with
    | nil => simp at hmap
    | cons t fs =>
        cases fs with
        | nil =>
            refine ⟨t, hinc t (by simp), hfb t (by simp), ?_⟩
            rw [hlo, hw]
            rfl
        | cons u us => simp at hmap
  · rintro ⟨t, hinc, hfb, hlo⟩
    cases t with
    | node x c =>
        refine ⟨x, levelsOf c, ?_, ?_⟩
        · rw [← hlo]
          have h1 : levelOrder [LTree.node x c] =
              x :: levelOrder c := by
            rw [levelOrder]
            simp [label, children]
          rw [h1, levelOrder_eq_flatten (szF c) c (Nat.le_refl _)]
        · have h := chainB_of_forest (szF [LTree.node x c]) [LTree.node x c]
            (Nat.le_refl _) (by simpa using hinc) (by simpa using hfb)
          have hch : ([LTree.node x c] : List LTree).flatMap children = c := by
            simp [children]
          rw [hch] at h
          simpa [label] using h

/-- **Theorem A, stated on genuine trees.** -/
theorem theoremA_trees {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has312 w)
    (hne : w ≠ []) :
    (∃ t : LTree, Inc t ∧ UB t ∧ levelOrder [t] = w) ↔ HeapCond w := by
  rw [← ubword_iff_tree]
  exact theoremA hnd hav hne

/-- **Theorem B, stated on genuine trees.** -/
theorem theoremB_trees {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has231 w)
    (hodd : w.length % 2 = 1)
    (h : ∃ t : LTree, Inc t ∧ UB t ∧ levelOrder [t] = w) :
    ∃ t : LTree, Inc t ∧ FB t ∧ levelOrder [t] = w := by
  rw [← ubword_iff_tree] at h
  rw [← bword_iff_tree]
  exact theoremB hnd hav hodd h

end BfsWords
