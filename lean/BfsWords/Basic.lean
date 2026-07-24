/- Basic lemmas about `Feas`, patterns and sublists. -/
import BfsWords.Defs

namespace BfsWords

/-- Every parent list admits the empty child block (all groups empty). -/
theorem Feas.empty (P : List Nat) : Feas P [] := by
  induction P with
  | nil => exact .nil
  | cons p P ih =>
      simpa using Feas.cons (p := p) (P := P) (g := []) (C := [])
        (by simp) (by simp) ih

/-- Concatenate two feasible pairs. -/
theorem Feas.append {P₁ C₁ P₂ C₂ : List Nat}
    (h₁ : Feas P₁ C₁) (h₂ : Feas P₂ C₂) : Feas (P₁ ++ P₂) (C₁ ++ C₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons p P g C hg hgt hrec ih =>
      simpa [List.append_assoc] using
        Feas.cons (p := p) (P := P ++ P₂) (g := g) (C := C ++ C₂) hg hgt ih

/-- Dropping the first child preserves feasibility. -/
theorem Feas.dropHead {P c C} (h : Feas P (c :: C)) : Feas P C := by
  generalize hC : c :: C = C₀ at h
  induction h generalizing c C with
  | nil => cases hC
  | @cons p P g C' hg hgt hrec ih =>
      cases g with
      | nil =>
          have hC' : c :: C = C' := by simpa using hC
          have h' := ih (hC := hC')
          simpa using Feas.cons (p := p) (P := P) (g := []) (C := C)
            (by simp) (by simp) h'
      | cons a g' =>
          have hC' : c = a ∧ C = g' ++ C' := by simpa using hC
          obtain ⟨rfl, rfl⟩ := hC'
          exact Feas.cons (p := p) (P := P) (g := g') (C := C')
            (by simp at hg; omega) (fun x hx => hgt x (by simp [hx])) hrec

/-- Append one more parent at the end together with its group. -/
theorem Feas.snoc {P C x g} (h : Feas P C) (hg : g.length ≤ 2)
    (hgt : ∀ c ∈ g, x < c) : Feas (P ++ [x]) (C ++ g) := by
  refine Feas.append h ?_
  simpa using Feas.cons (p := x) (P := []) (g := g) (C := []) hg hgt .nil

/-- Capacity: at most two children per parent. -/
theorem Feas.length_le {P C} (h : Feas P C) : C.length ≤ 2 * P.length := by
  induction h with
  | nil => simp
  | @cons p P g C hg hgt hrec ih => simp; omega

/-- `[l[i], l[j]] <+ l` for `i < j`. -/
theorem pair_sublist {α : Type} (l : List α) (i j : Nat) (hij : i < j)
    (hj : j < l.length) :
    [l[i]'(by omega), l[j]'hj].Sublist l := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j' =>
              simp only [List.getElem_cons_zero, List.getElem_cons_succ]
              exact .cons₂ x (List.singleton_sublist.mpr (List.getElem_mem _))
      | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
              simp only [List.getElem_cons_succ]
              exact .cons x (ih i' j' (by omega) (by simpa using hj))

/-- A sublist of a 312-avoiding word avoids 312. -/
theorem not_has312_sublist {u w : List Nat} (hs : u.Sublist w)
    (h : ¬ Has312 w) : ¬ Has312 u := by
  rintro ⟨a, b, c, hsub, h₁, h₂⟩
  exact h ⟨a, b, c, hsub.trans hs, h₁, h₂⟩

theorem not_has231_sublist {u w : List Nat} (hs : u.Sublist w)
    (h : ¬ Has231 w) : ¬ Has231 u := by
  rintro ⟨a, b, c, hsub, h₁, h₂⟩
  exact h ⟨a, b, c, hsub.trans hs, h₁, h₂⟩

/-- Distinct positions in a `Nodup` list carry distinct values. -/
theorem nodup_getElem_ne {l : List Nat} (h : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[i]'hi ≠ l[j]'hj := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x t ih =>
      have hx : x ∉ t := by
        simp [List.nodup_cons] at h; exact h.1
      have ht : t.Nodup := by
        simp [List.nodup_cons] at h; exact h.2
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j' =>
              simp only [List.getElem_cons_zero, List.getElem_cons_succ]
              intro hEq
              exact hx (hEq ▸ List.getElem_mem _)
      | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
              simp only [List.getElem_cons_succ]
              exact ih ht (by simpa using hi) (by simpa using hj) (by omega)

end BfsWords
