/-
The two 231-specific lemmas of Theorem B:
* `feas_snoc_odd`  (Lemma B3): an odd feasible level absorbs the next element;
* `feasB_of_feas`  (Lemma B4): an even feasible level has a full-binary
  regrouping.
Both proofs run by strong induction on `|P| + |C|`; the pattern 231 enters
through exactly two forced inequalities.
-/
import BfsWords.Cascade

namespace BfsWords

/-- Lemma B3: if `(P, C)` is feasible, `|C|` is odd, and the word
`P ++ C ++ [x]` avoids 231 with distinct letters, then `(P, C ++ [x])`
is feasible. -/
theorem feas_snoc_odd : ∀ (n : Nat) (P C : List Nat) (x : Nat),
    P.length + C.length ≤ n →
    ¬ Has231 ((P ++ C) ++ [x]) → ((P ++ C) ++ [x]).Nodup →
    Feas P C → C.length % 2 = 1 → Feas P (C ++ [x]) := by
  intro n
  induction n with
  | zero =>
      intro P C x hn _ _ _ hodd
      omega
  | succ n ih =>
      intro P C x hn hav hnd h hodd
      cases h with
      | nil => simp at hodd
      | @cons p P' g C' hg hgt hrec =>
          have hgC : (g ++ C').length = g.length + C'.length := by simp
          cases g with
          | nil =>
              -- empty group: recurse on (P', C')
              have hsub : ((P' ++ C') ++ [x]).Sublist
                  (((p :: P') ++ ([] ++ C')) ++ [x]) := by
                refine List.Sublist.append (List.Sublist.append ?_ ?_) ?_
                · exact List.sublist_cons_self p P'
                · simp
                · simp
              have hres := ih P' C' x (by simp at hn ⊢; omega)
                (not_has231_sublist hsub hav)
                (List.Nodup.sublist hsub hnd) hrec (by simpa using hodd)
              have : Feas (p :: P') ([] ++ (C' ++ [x])) :=
                Feas.cons (by simp) (by simp) hres
              simpa using this
          | cons c g₁ =>
              cases g₁ with
              | nil =>
                  -- group [c]
                  have hpc : p < c := hgt c (by simp)
                  cases C' with
                  | nil =>
                      -- C = [c]; attach x to p; x > p forced by 231
                      have hnd' : ((p :: P') ++ [c] ++ [x]).Nodup := by
                        simpa using hnd
                      have hpx : p ≠ x :=
                        ne_of_nodup_append (X := (p :: P') ++ [c]) (Y := [x])
                          (by simpa [List.append_assoc] using hnd')
                          (by simp) (by simp)
                      have hxp : p < x := by
                        cases Nat.lt_or_ge p x with
                        | inl hlt => exact hlt
                        | inr hge =>
                            exfalso
                            have hxlt : x < p := by omega
                            -- triple [p, c, x] is a 231
                            have htrip : [p, c, x].Sublist
                                (((p :: P') ++ ([c] ++ [])) ++ [x]) := by
                              have h1 : [p].Sublist (p :: P') :=
                                List.singleton_sublist.mpr (by simp)
                              have h2 : [c].Sublist ([c] ++ []) := by simp
                              have h3 : [x].Sublist [x] := List.Sublist.refl _
                              have h := (h1.append h2).append h3
                              simpa using h
                            exact hav ⟨p, c, x, htrip, hxlt, hpc⟩
                      have : Feas (p :: P') ([c, x] ++ []) :=
                        Feas.cons (by simp) (by
                          intro y hy
                          simp at hy
                          rcases hy with rfl | rfl
                          · exact hpc
                          · exact hxp) (Feas.empty P')
                      simpa using this
                  | cons c' C'' =>
                      -- group [c], more children: steal c' into p's group
                      have hndPC : ((p :: P') ++ ([c] ++ (c' :: C''))).Nodup := by
                        have hsub : ((p :: P') ++ ([c] ++ (c' :: C''))).Sublist
                            (((p :: P') ++ ([c] ++ (c' :: C''))) ++ [x]) :=
                          List.sublist_append_left _ _
                        exact List.Nodup.sublist hsub hnd
                      have havPC : ¬ Has231 ((p :: P') ++ ([c] ++ (c' :: C''))) :=
                        not_has231_sublist (List.sublist_append_left _ _) hav
                      have hpc' : p ≠ c' :=
                        ne_of_nodup_append (X := p :: P')
                          (Y := [c] ++ (c' :: C'')) hndPC (by simp) (by simp)
                      have hc'p : p < c' := by
                        cases Nat.lt_or_ge p c' with
                        | inl hlt => exact hlt
                        | inr hge =>
                            exfalso
                            have hlt : c' < p := by omega
                            have htrip : [p, c, c'].Sublist
                                ((p :: P') ++ ([c] ++ (c' :: C''))) := by
                              have h1 : [p].Sublist (p :: P') :=
                                List.singleton_sublist.mpr (by simp)
                              have h2 : [c].Sublist [c] := List.Sublist.refl _
                              have h3 : [c'].Sublist (c' :: C'') :=
                                List.singleton_sublist.mpr (by simp)
                              have h := h1.append (h2.append h3)
                              simpa using h
                            exact havPC ⟨p, c, c', htrip, hlt, hpc⟩
                      -- recurse on (P', C'')
                      have hrec' : Feas P' C'' := hrec.dropHead
                      have hsub : ((P' ++ C'') ++ [x]).Sublist
                          (((p :: P') ++ ([c] ++ (c' :: C''))) ++ [x]) := by
                        refine List.Sublist.append
                          (List.Sublist.append ?_ ?_) ?_
                        · exact List.sublist_cons_self p P'
                        · exact ((List.sublist_cons_self c' C'').trans
                            (List.sublist_append_right [c] _))
                        · simp
                      have hres := ih P' C'' x
                        (by simp at hn ⊢; omega)
                        (not_has231_sublist hsub hav)
                        (List.Nodup.sublist hsub hnd) hrec'
                        (by simp at hodd ⊢; omega)
                      have : Feas (p :: P') ([c, c'] ++ (C'' ++ [x])) :=
                        Feas.cons (by simp) (by
                          intro y hy
                          simp at hy
                          rcases hy with rfl | rfl
                          · exact hpc
                          · exact hc'p) hres
                      simpa [List.append_assoc] using this
              | cons c₂ g₂ =>
                  cases g₂ with
                  | nil =>
                      -- group [c, c₂]: recurse on (P', C')
                      have hsub : ((P' ++ C') ++ [x]).Sublist
                          (((p :: P') ++ ([c, c₂] ++ C')) ++ [x]) := by
                        refine List.Sublist.append
                          (List.Sublist.append ?_ ?_) ?_
                        · exact List.sublist_cons_self p P'
                        · exact List.sublist_append_right [c, c₂] C'
                        · simp
                      have hres := ih P' C' x (by simp at hn ⊢; omega)
                        (not_has231_sublist hsub hav)
                        (List.Nodup.sublist hsub hnd) hrec
                        (by simp at hodd ⊢; omega)
                      have : Feas (p :: P') ([c, c₂] ++ (C' ++ [x])) :=
                        Feas.cons hg hgt hres
                      simpa [List.append_assoc] using this
                  | cons _ _ => simp at hg

/-- Lemma B4: an even feasible pair admits a full-binary regrouping. -/
theorem feasB_of_feas : ∀ (n : Nat) (P C : List Nat),
    P.length + C.length ≤ n →
    ¬ Has231 (P ++ C) → (P ++ C).Nodup →
    Feas P C → C.length % 2 = 0 → FeasB P C := by
  intro n
  induction n with
  | zero =>
      intro P C hn _ _ h _
      cases h with
      | nil => exact .nil
      | cons hg hgt hrec => simp at hn
  | succ n ih =>
      intro P C hn hav hnd h heven
      cases h with
      | nil => exact .nil
      | @cons p P' g C' hg hgt hrec =>
          cases g with
          | nil =>
              have hsub : (P' ++ C').Sublist ((p :: P') ++ ([] ++ C')) := by
                refine List.Sublist.append ?_ ?_
                · exact List.sublist_cons_self p P'
                · simp
              have hres := ih P' C' (by simp at hn ⊢; omega)
                (not_has231_sublist hsub hav)
                (List.Nodup.sublist hsub hnd) hrec (by simpa using heven)
              have : FeasB (p :: P') ([] ++ C') :=
                FeasB.cons (Or.inl rfl) (by simp) hres
              simpa using this
          | cons c g₁ =>
              cases g₁ with
              | nil =>
                  -- group [c]: C' must be odd, hence nonempty; steal its head
                  have hpc : p < c := hgt c (by simp)
                  cases C' with
                  | nil => simp at heven
                  | cons c' C'' =>
                      have hpc' : p ≠ c' :=
                        ne_of_nodup_append (X := p :: P')
                          (Y := [c] ++ (c' :: C'')) hnd (by simp) (by simp)
                      have hc'p : p < c' := by
                        cases Nat.lt_or_ge p c' with
                        | inl hlt => exact hlt
                        | inr hge =>
                            exfalso
                            have hlt : c' < p := by omega
                            have htrip : [p, c, c'].Sublist
                                ((p :: P') ++ ([c] ++ (c' :: C''))) := by
                              have h1 : [p].Sublist (p :: P') :=
                                List.singleton_sublist.mpr (by simp)
                              have h2 : [c].Sublist [c] := List.Sublist.refl _
                              have h3 : [c'].Sublist (c' :: C'') :=
                                List.singleton_sublist.mpr (by simp)
                              have h := h1.append (h2.append h3)
                              simpa using h
                            exact hav ⟨p, c, c', htrip, hlt, hpc⟩
                      have hrec' : Feas P' C'' := hrec.dropHead
                      have hsub : (P' ++ C'').Sublist
                          ((p :: P') ++ ([c] ++ (c' :: C''))) := by
                        refine List.Sublist.append ?_ ?_
                        · exact List.sublist_cons_self p P'
                        · exact ((List.sublist_cons_self c' C'').trans
                            (List.sublist_append_right [c] _))
                      have hres := ih P' C'' (by simp at hn ⊢; omega)
                        (not_has231_sublist hsub hav)
                        (List.Nodup.sublist hsub hnd) hrec'
                        (by simp at heven ⊢; omega)
                      have : FeasB (p :: P') ([c, c'] ++ C'') :=
                        FeasB.cons (Or.inr rfl) (by
                          intro y hy
                          simp at hy
                          rcases hy with rfl | rfl
                          · exact hpc
                          · exact hc'p) hres
                      simpa using this
              | cons c₂ g₂ =>
                  cases g₂ with
                  | nil =>
                      have hsub : (P' ++ C').Sublist
                          ((p :: P') ++ ([c, c₂] ++ C')) := by
                        refine List.Sublist.append ?_ ?_
                        · exact List.sublist_cons_self p P'
                        · exact List.sublist_append_right [c, c₂] C'
                      have hres := ih P' C' (by simp at hn ⊢; omega)
                        (not_has231_sublist hsub hav)
                        (List.Nodup.sublist hsub hnd) hrec
                        (by simp at heven ⊢; omega)
                      exact FeasB.cons (Or.inr rfl) hgt hres
                  | cons _ _ => simp at hg

end BfsWords
