/-
Lemma A1 (balanced matching): in a 312-avoiding context, any feasible
parent/child pair satisfies the *balanced* inequalities `P[j/2] < C[j]`.
-/
import BfsWords.Basic

namespace BfsWords

/-- Values in different halves of a Nodup concatenation differ. -/
theorem ne_of_nodup_append {X Y : List Nat} (h : (X ++ Y).Nodup)
    {x y : Nat} (hx : x ∈ X) (hy : y ∈ Y) : x ≠ y := by
  intro rfl
  rw [List.nodup_append] at h
  exact h.2.2 x hx x hy rfl

/-- Lemma A1. -/
theorem Feas.balanced {P C : List Nat}
    (hav : ¬ Has312 (P ++ C)) (hnd : (P ++ C).Nodup)
    (h : Feas P C) :
    ∀ j, (hj : j < C.length) → (hp : j / 2 < P.length) →
      P[j / 2]'hp < C[j]'hj := by
  induction h with
  | nil => intro j hj; simp at hj
  | @cons p P g C hg hgt hrec ih =>
      intro j hj hp
      by_cases hjg : j < g.length
      · -- child inside the first group: its parent is `p`, and j/2 = 0
        have hj0 : j / 2 = 0 := by omega
        simp only [hj0, List.getElem_cons_zero]
        rw [List.getElem_append_left hjg]
        exact hgt _ (List.getElem_mem _)
      · -- child inside `C`
        have hjg2 : g.length ≤ j := Nat.le_of_not_lt hjg
        have hjC : j - g.length < C.length := by
          have := List.length_append (as := g) (bs := C)
          omega
        have hCval : (g ++ C)[j]'hj = C[j - g.length]'hjC := by
          rw [List.getElem_append_right hjg2]
        -- sub-context for the inductive hypothesis
        have hsub : (P ++ C).Sublist ((p :: P) ++ (g ++ C)) := by
          refine List.Sublist.append ?_ ?_
          · exact (List.sublist_cons_self p P)
          · exact List.sublist_append_right g C
        have hav' := not_has312_sublist hsub hav
        have hnd' : (P ++ C).Nodup := List.Nodup.sublist hsub hnd
        have hcap : C.length ≤ 2 * P.length := hrec.length_le
        have hp' : (j - g.length) / 2 < P.length := by omega
        have hIH := ih hav' hnd' (j - g.length) hjC hp'
        -- compare target parent index with the IH parent index
        have hle : j / 2 ≤ (j - g.length) / 2 + 1 := by omega
        by_cases heq : j / 2 = (j - g.length) / 2 + 1
        · -- indices agree: the IH inequality is the goal
          have hgoal : (p :: P)[j / 2]'hp = P[(j - g.length) / 2]'hp' := by
            simp only [heq]
            exact List.getElem_cons_succ p P ((j - g.length) / 2) (by simp; omega)
          rw [hgoal, hCval]
          exact hIH
        · -- target parent strictly earlier: 312 pattern closes the gap
          have hlt : j / 2 < (j - g.length) / 2 + 1 := by omega
          have ht : True := trivial
          have ht' : True := trivial
          have hpt' : (j - g.length) / 2 + 1 < (p :: P).length := by simp; omega
          -- A = (p::P)[j/2], B = (p::P)[t'] = P[(j-g.length)/2], c = C[j-g.length]
          have hBval : (p :: P)[(j - g.length) / 2 + 1]'hpt' = P[(j - g.length) / 2]'hp' :=
            List.getElem_cons_succ p P ((j - g.length) / 2) hpt'
          have hBc : (p :: P)[(j - g.length) / 2 + 1]'hpt' < C[j - g.length]'hjC := by
            rw [hBval]; exact hIH
          rw [hCval]
          -- either the goal holds, or we derive a 312 pattern
          cases Nat.lt_or_ge ((p :: P)[j / 2]'hp) (C[j - g.length]'hjC) with
          | inl hwin => exact hwin
          | inr hcon2 =>
          exfalso
          -- c ≤ A; first c ≠ A from Nodup, so c < A
          have hmemA : (p :: P)[j / 2]'hp ∈ (p :: P) := List.getElem_mem _
          have hmemc : C[j - g.length]'hjC ∈ g ++ C := by
            have : C[j - g.length]'hjC ∈ C := List.getElem_mem _
            exact List.mem_append_right g this
          have hne : (p :: P)[j / 2]'hp ≠ C[j - g.length]'hjC :=
            ne_of_nodup_append hnd hmemA hmemc
          have hcA : C[j - g.length]'hjC < (p :: P)[j / 2]'hp := by omega
          -- build the 312 occurrence [A, B, c]
          have hpair : [(p :: P)[j / 2]'hp, (p :: P)[(j - g.length) / 2 + 1]'hpt'].Sublist (p :: P) :=
            pair_sublist _ (j / 2) ((j - g.length) / 2 + 1) hlt hpt'
          have hsing : [C[j - g.length]'hjC].Sublist (g ++ C) :=
            List.singleton_sublist.mpr hmemc
          have htrip :
              [(p :: P)[j / 2]'hp, (p :: P)[(j - g.length) / 2 + 1]'hpt',
                C[j - g.length]'hjC].Sublist ((p :: P) ++ (g ++ C)) := by
            have := List.Sublist.append hpair hsing
            simpa using this
          exact hav ⟨_, _, _, htrip, hBc, hcA⟩

end BfsWords
