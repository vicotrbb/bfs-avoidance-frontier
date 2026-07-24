/-
Theorem B: an odd-length 231-avoiding BFS word of an increasing
unary-binary tree is the BFS word of an increasing *full binary* tree.

Assembly: evenize the chain level by level (Lemma B3 grows odd levels by
one, the promotion cascade `chain_plus` repairs the suffix, and the depth
measure strictly decreases), then regroup every level with Lemma B4.
-/
import BfsWords.B231

namespace BfsWords

/-- Every chain can be replaced by a flatten-equal chain whose levels all
have even size, provided the total suffix length is even. -/
theorem evenize : ∀ (fuel : Nat) (prev : List Nat) (ls : List (List Nat)),
    depth ls ≤ fuel →
    ¬ Has231 (prev ++ ls.flatten) → (prev ++ ls.flatten).Nodup →
    ls.flatten.length % 2 = 0 →
    Chain prev ls →
    ∃ ls', Chain prev ls' ∧ ls'.flatten = ls.flatten ∧
      ∀ L ∈ ls', L.length % 2 = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev ls hdep _ _ _ hc
      cases hc with
      | nil => exact ⟨[], .nil, rfl, by simp⟩
      | @cons _ L ls₀ hLne hfeas hchain =>
          exfalso
          have h1 : 1 ≤ L.length := by
            cases L with
            | nil => exact absurd rfl hLne
            | cons a t => simp
          have : 1 ≤ depth (L :: ls₀) := by
            simp only [depth, List.flatten_cons]
            simp
            omega
          omega
  | succ n ih =>
      intro prev ls hdep hav hnd hpar hc
      cases hc with
      | nil => exact ⟨[], .nil, rfl, by simp⟩
      | @cons _ L ls₀ hLne hfeas hchain =>
          have hL1 : 1 ≤ L.length := by
            cases L with
            | nil => exact absurd rfl hLne
            | cons a t => simp
          have hflatlen : (L :: ls₀).flatten.length =
              L.length + ls₀.flatten.length := by
            rw [List.flatten_cons]; simp
          by_cases hLev : L.length % 2 = 0
          · -- even level: keep it, recurse below
            have hsub : (L ++ ls₀.flatten).Sublist
                (prev ++ (L :: ls₀).flatten) := by
              rw [List.flatten_cons]
              exact List.sublist_append_right _ _
            have hres := ih L ls₀
              (by
                have : depth (L :: ls₀) =
                    (L :: ls₀).flatten.length + depth ls₀ := rfl
                omega)
              (not_has231_sublist hsub hav)
              (List.Nodup.sublist hsub hnd)
              (by omega)
              hchain
            obtain ⟨ls₀', hchain', hflat', heven'⟩ := hres
            refine ⟨L :: ls₀', Chain.cons hLne hfeas hchain', ?_, ?_⟩
            · rw [List.flatten_cons, List.flatten_cons, hflat']
            · intro M hM
              simp at hM
              rcases hM with rfl | hM
              · exact hLev
              · exact heven' M hM
          · -- odd level: grow it by the next element, then recurse
            have hLodd : L.length % 2 = 1 := by omega
            have hfl0 : ls₀.flatten.length % 2 = 1 := by omega
            cases hfl : ls₀.flatten with
            | nil => rw [hfl] at hfl0; simp at hfl0
            | cons x rest =>
                -- Lemma B3: Feas prev (L ++ [x])
                have hsub3 : ((prev ++ L) ++ [x]).Sublist
                    (prev ++ (L :: ls₀).flatten) := by
                  rw [List.flatten_cons, hfl]
                  have h1 : ([x] : List Nat).Sublist (x :: rest) :=
                    List.singleton_sublist.mpr (by simp)
                  have h := (List.Sublist.refl prev).append
                    ((List.Sublist.refl L).append h1)
                  simpa [List.append_assoc] using h
                have hfeas' : Feas prev (L ++ [x]) :=
                  feas_snoc_odd (prev.length + L.length) prev L x
                    (Nat.le_refl _)
                    (not_has231_sublist hsub3 hav)
                    (List.Nodup.sublist hsub3 hnd)
                    hfeas hLodd
                -- promotion cascade below
                obtain ⟨ls₁, hchain₁, hflat₁, hdep₁⟩ := chain_plus hchain hfl
                have hLxne : L ++ [x] ≠ [] := by simp
                have hchain₂ : Chain prev ((L ++ [x]) :: ls₁) :=
                  Chain.cons hLxne hfeas' hchain₁
                have hflat₂ : ((L ++ [x]) :: ls₁).flatten =
                    (L :: ls₀).flatten := by
                  rw [List.flatten_cons, List.flatten_cons, hflat₁, hfl]
                  simp [List.append_assoc]
                have hdep₂ : depth ((L ++ [x]) :: ls₁) ≤ n := by
                  have e₁ : depth ((L ++ [x]) :: ls₁) =
                      ((L ++ [x]) :: ls₁).flatten.length + depth ls₁ := rfl
                  have e₂ : depth (L :: ls₀) =
                      (L :: ls₀).flatten.length + depth ls₀ := rfl
                  have e₃ : ((L ++ [x]) :: ls₁).flatten.length =
                      (L :: ls₀).flatten.length := by rw [hflat₂]
                  omega
                have hres := ih prev ((L ++ [x]) :: ls₁) hdep₂
                  (by rw [hflat₂]; exact hav)
                  (by rw [hflat₂]; exact hnd)
                  (by rw [hflat₂]; exact hpar)
                  hchain₂
                obtain ⟨ls', hchain', hflat', heven'⟩ := hres
                exact ⟨ls', hchain', by rw [hflat', hflat₂], heven'⟩

/-- All-even chains regroup into full-binary chains (Lemma B4 levelwise). -/
theorem chainB_of_even : ∀ (ls : List (List Nat)) (prev : List Nat),
    Chain prev ls → (∀ L ∈ ls, L.length % 2 = 0) →
    ¬ Has231 (prev ++ ls.flatten) → (prev ++ ls.flatten).Nodup →
    ChainB prev ls := by
  intro ls
  induction ls with
  | nil => intro prev _ _ _ _; exact .nil
  | cons L ls₀ ih =>
      intro prev hc heven hav hnd
      cases hc with
      | cons hLne hfeas hchain =>
          have hsubPL : (prev ++ L).Sublist (prev ++ (L :: ls₀).flatten) := by
            rw [List.flatten_cons]
            exact (List.Sublist.refl prev).append (List.sublist_append_left _ _)
          have hfeasB : FeasB prev L :=
            feasB_of_feas (prev.length + L.length) prev L (Nat.le_refl _)
              (not_has231_sublist hsubPL hav)
              (List.Nodup.sublist hsubPL hnd)
              hfeas (heven L (by simp))
          have hsub0 : (L ++ ls₀.flatten).Sublist
              (prev ++ (L :: ls₀).flatten) := by
            rw [List.flatten_cons]
            exact List.sublist_append_right _ _
          exact ChainB.cons hLne hfeasB
            (ih L hchain (fun M hM => heven M (by simp [hM]))
              (not_has231_sublist hsub0 hav)
              (List.Nodup.sublist hsub0 hnd))

/-- **Theorem B**: an odd-length 231-avoiding word with distinct letters
that is a BFS word of an increasing unary-binary tree is a BFS word of an
increasing full binary tree. -/
theorem theoremB {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has231 w)
    (hodd : w.length % 2 = 1) (h : UBWord w) : BWord w := by
  obtain ⟨hd, ls, hw, hc⟩ := h
  have hpf : [hd] ++ ls.flatten = w := by rw [hw]; rfl
  have hlen : w.length = 1 + ls.flatten.length := by rw [hw]; simp; omega
  have hres := evenize (depth ls) [hd] ls (Nat.le_refl _)
    (by rw [hpf]; exact hav)
    (by rw [hpf]; exact hnd)
    (by omega)
    hc
  obtain ⟨ls', hchain', hflat', heven'⟩ := hres
  have hpf' : [hd] ++ ls'.flatten = w := by rw [hflat']; exact hpf
  have hcB : ChainB [hd] ls' :=
    chainB_of_even ls' [hd] hchain' heven'
      (by rw [hpf']; exact hav)
      (by rw [hpf']; exact hnd)
  exact ⟨hd, ls', by rw [hw, ← hflat'], hcB⟩

end BfsWords
