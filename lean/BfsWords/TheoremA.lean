/-
Theorem A: a 312-avoiding word (with distinct letters) is the BFS word of
an increasing unary-binary tree iff it satisfies the binary-heap condition.
-/
import BfsWords.Balanced

namespace BfsWords

/-- `[l[i], l[j], l[k]] <+ l` for `i < j < k`. -/
theorem triple_sublist {α : Type} (l : List α) (i j k : Nat)
    (hij : i < j) (hjk : j < k) (hk : k < l.length) :
    [l[i]'(by omega), l[j]'(by omega), l[k]'hk].Sublist l := by
  induction l generalizing i j k with
  | nil => simp at hk
  | cons x t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j' =>
              cases k with
              | zero => omega
              | succ k' =>
                  simp only [List.getElem_cons_zero, List.getElem_cons_succ]
                  exact .cons₂ x (pair_sublist t j' k' (by omega) (by simpa using hk))
      | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
              cases k with
              | zero => omega
              | succ k' =>
                  simp only [List.getElem_cons_succ]
                  exact .cons x (ih i' j' k' (by omega) (by omega) (by simpa using hk))

theorem getElem_eq_of_getElem? {l : List Nat} {i v : Nat}
    (h : l[i]? = some v) (hi : i < l.length) : l[i]'hi = v := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- Change the index of a `getElem` along an equality. -/
theorem getElem_idx {l : List Nat} {i j : Nat} (hij : i = j)
    (hi : i < l.length) : l[i]'hi = l[j]'(hij ▸ hi) := by
  subst hij; rfl

/-- Change the list of a `getElem` along an equality. -/
theorem getElem_of_eq {w X : List Nat} (h : w = X) {i : Nat}
    (hi : i < w.length) : w[i]'hi = X[i]'(h ▸ hi) := by
  subst h; rfl

/-- Read a value of the middle block of a 3-block concatenation. -/
theorem getElem_mid {pre mid post : List Nat} (k : Nat) (hk : k < mid.length)
    (h : pre.length + k < (pre ++ mid ++ post).length) :
    (pre ++ mid ++ post)[pre.length + k]'h = mid[k]'hk := by
  apply getElem_eq_of_getElem?
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  have hidx : pre.length + k - pre.length = k := by omega
  rw [hidx, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

/-- Key induction for Theorem A (⇒): below any chain, every position
satisfies the heap inequality.  The invariant `|prev| ≤ |pre| + 1`
propagates down the chain. -/
theorem chain_heap_aux {w : List Nat} (hav : ¬ Has312 w) (hnd : w.Nodup) :
    ∀ (ls : List (List Nat)) (pre prev : List Nat),
      w = pre ++ prev ++ ls.flatten →
      prev.length ≤ pre.length + 1 →
      1 ≤ prev.length →
      Chain prev ls →
      ∀ k, (hk : k < ls.flatten.length) →
        ∀ (hi : pre.length + prev.length + k < w.length),
        w[(pre.length + prev.length + k - 1) / 2]'(by omega) <
          w[pre.length + prev.length + k]'hi := by
  intro ls
  induction ls with
  | nil => intro pre prev hw hinv hne hc k hk; simp at hk
  | cons L ls ih =>
      intro pre prev hw hinv hne hc k hk hi
      cases hc with
      | cons hLne hfeas hchain =>
      have hflat : (L :: ls).flatten = L ++ ls.flatten := List.flatten_cons
      have hcap : L.length ≤ 2 * prev.length := hfeas.length_le
      by_cases hkL : k < L.length
      · -- position inside the first level `L`
        have hwX : w = (pre ++ prev) ++ L ++ ls.flatten := by
          rw [hw, hflat]; simp [List.append_assoc]
        have hwY : w = pre ++ prev ++ (L ++ ls.flatten) := by
          rw [hw, hflat]
        -- A1 on the pair (prev, L)
        have hsubPL : (prev ++ L).Sublist w := by
          rw [hwY]
          have h₁ : (prev ++ L).Sublist ((prev ++ L) ++ ls.flatten) :=
            List.sublist_append_left _ _
          have h₂ : ((prev ++ L) ++ ls.flatten).Sublist
              (pre ++ ((prev ++ L) ++ ls.flatten)) :=
            List.sublist_append_right _ _
          have h₃ := h₁.trans h₂
          simpa [List.append_assoc] using h₃
        have havPL := not_has312_sublist hsubPL hav
        have hndPL : (prev ++ L).Nodup := List.Nodup.sublist hsubPL hnd
        have hp2 : k / 2 < prev.length := by omega
        have hbalv := hfeas.balanced havPL hndPL k hkL hp2
        -- value transfers into w
        have hchild : w[pre.length + prev.length + k]'hi = L[k]'hkL := by
          have e₁ := getElem_of_eq hwX hi
          have hidx : pre.length + prev.length + k = (pre ++ prev).length + k := by
            simp
          have e₂ := getElem_idx (l := (pre ++ prev) ++ L ++ ls.flatten) hidx
            (hwX ▸ hi)
          have e₃ := getElem_mid (pre := pre ++ prev) (mid := L)
            (post := ls.flatten) k hkL (by simp; omega)
          rw [e₁, e₂, e₃]
        have hparbound : pre.length + k / 2 < w.length := by
          rw [hwY]; simp; omega
        have hpar : w[pre.length + k / 2]'hparbound = prev[k / 2]'hp2 := by
          have e₁ := getElem_of_eq hwY hparbound
          have e₃ := getElem_mid (pre := pre) (mid := prev)
            (post := L ++ ls.flatten) (k / 2) hp2 (by simp; omega)
          rw [e₁, e₃]
        -- heap parent index vs balanced parent index
        have hble : (pre.length + prev.length + k - 1) / 2 ≤ pre.length + k / 2 := by
          omega
        by_cases hbeq : (pre.length + prev.length + k - 1) / 2 = pre.length + k / 2
        · -- heap parent = balanced parent
          have e := getElem_idx (l := w) hbeq (by omega)
          rw [e, hpar, hchild]
          exact hbalv
        · -- heap parent strictly before balanced parent: 312 closes the gap
          have hblt : (pre.length + prev.length + k - 1) / 2 <
              pre.length + k / 2 := by omega
          have hbpos : pre.length + k / 2 < pre.length + prev.length + k := by
            omega
          have hBc : w[pre.length + k / 2]'hparbound <
              w[pre.length + prev.length + k]'hi := by
            rw [hpar, hchild]; exact hbalv
          cases Nat.lt_or_ge
              (w[(pre.length + prev.length + k - 1) / 2]'(by omega))
              (w[pre.length + prev.length + k]'hi) with
          | inl hwin => exact hwin
          | inr hcon =>
              exfalso
              have hneq : w[(pre.length + prev.length + k - 1) / 2]'(by omega) ≠
                  w[pre.length + prev.length + k]'hi :=
                nodup_getElem_ne hnd (by omega) hi (by omega)
              have hstrict : w[pre.length + prev.length + k]'hi <
                  w[(pre.length + prev.length + k - 1) / 2]'(by omega) := by
                omega
              have htrip := triple_sublist w
                ((pre.length + prev.length + k - 1) / 2)
                (pre.length + k / 2)
                (pre.length + prev.length + k) hblt hbpos hi
              exact hav ⟨_, _, _, htrip, hBc, hstrict⟩
      · -- position strictly below `L`: inductive step
        have hkL2 : L.length ≤ k := Nat.le_of_not_lt hkL
        have hk2 : k < L.length + ls.flatten.length := by
          rw [hflat] at hk
          simpa using hk
        have hk' : k - L.length < ls.flatten.length := by omega
        have hw' : w = (pre ++ prev) ++ L ++ ls.flatten := by
          rw [hw, hflat]; simp [List.append_assoc]
        have hinv' : L.length ≤ (pre ++ prev).length + 1 := by simp; omega
        have hne' : 1 ≤ L.length := by
          cases L with
          | nil => exact absurd rfl hLne
          | cons a t => simp
        have hibound : (pre ++ prev).length + L.length + (k - L.length) <
            w.length := by simp; omega
        have h := ih (pre ++ prev) L hw' hinv' hne' hchain (k - L.length) hk'
          hibound
        have harith : (pre ++ prev).length + L.length + (k - L.length) =
            pre.length + prev.length + k := by simp; omega
        have e₁ := getElem_idx (l := w) harith hibound
        have e₂ := getElem_idx (l := w)
          (show ((pre ++ prev).length + L.length + (k - L.length) - 1) / 2 =
            (pre.length + prev.length + k - 1) / 2 by simp; omega)
          (by omega)
        rw [e₁, e₂] at h
        exact h

/-- Theorem A, forward direction. -/
theorem heap_of_ubword {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has312 w)
    (h : UBWord w) : HeapCond w := by
  obtain ⟨hd, ls, hw, hc⟩ := h
  intro i hi hilen
  have hw' : w = [] ++ [hd] ++ ls.flatten := by simpa using hw
  have hlen : w.length = 1 + ls.flatten.length := by rw [hw]; simp; omega
  have hk : i - 1 < ls.flatten.length := by omega
  have hibound : ([] : List Nat).length + [hd].length + (i - 1) < w.length := by
    simp; omega
  have h := chain_heap_aux hav hnd ls [] [hd] hw' (by simp) (by simp) hc
    (i - 1) hk hibound
  have harith : ([] : List Nat).length + [hd].length + (i - 1) = i := by
    simp; omega
  have e₁ := getElem_idx (l := w) harith hibound
  have e₂ := getElem_idx (l := w)
    (show (([] : List Nat).length + [hd].length + (i - 1) - 1) / 2 =
        (i - 1) / 2 by simp) (by omega)
  rw [e₁, e₂] at h
  exact h

/-- Balanced inequalities imply feasibility (converse construction). -/
theorem feas_of_balanced :
    ∀ (P C : List Nat), C.length ≤ 2 * P.length →
      (∀ j, (hj : j < C.length) → (hp : j / 2 < P.length) →
        P[j / 2]'hp < C[j]'hj) →
      Feas P C := by
  intro P
  induction P with
  | nil =>
      intro C hcap _
      have : C = [] := by
        cases C with
        | nil => rfl
        | cons a t => simp at hcap
      rw [this]; exact .nil
  | cons p P ih =>
      intro C hcap hbal
      have hplen : (p :: P).length = P.length + 1 := rfl
      have hsplit : C = C.take 2 ++ C.drop 2 := (List.take_append_drop 2 C).symm
      rw [hsplit]
      have htlen : (C.take 2).length = min 2 C.length := List.length_take
      refine Feas.cons (by omega) ?_ ?_
      · -- both members of the first group exceed p
        intro c hc
        rw [List.mem_iff_getElem] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        have hjC : j < C.length := by omega
        have hval : (C.take 2)[j]'hj = C[j]'hjC := List.getElem_take
        rw [hval]
        have hj0 : j / 2 = 0 := by omega
        have h := hbal j hjC (by simp; omega)
        have e := getElem_idx (l := p :: P) hj0 (by simp; omega)
        rw [e] at h
        simpa using h
      · -- recurse on the remaining children
        have hdlen : (C.drop 2).length = C.length - 2 := List.length_drop
        refine ih (C.drop 2) (by omega) ?_
        intro j hj hp
        have hjC : 2 + j < C.length := by omega
        have hval : (C.drop 2)[j]'hj = C[2 + j]'hjC := List.getElem_drop
        rw [hval]
        have hidx : (2 + j) / 2 = j / 2 + 1 := by omega
        have h := hbal (2 + j) hjC (by simp; omega)
        have e := getElem_idx (l := p :: P) hidx (by simp; omega)
        rw [e] at h
        have e₂ : (p :: P)[j / 2 + 1]'(by simp; omega) = P[j / 2]'hp :=
          List.getElem_cons_succ p P (j / 2) (by simp; omega)
        rw [e₂] at h
        exact h

/-- Build the dyadic chain below a level of length `m + 1` (fuel-indexed). -/
def build (fuel m : Nat) (rest : List Nat) : List (List Nat) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match rest with
      | [] => []
      | r =>
          r.take (2 * (m + 1)) ::
            build fuel ((r.take (2 * (m + 1))).length - 1)
              (r.drop (2 * (m + 1)))

theorem flatten_build : ∀ (fuel m : Nat) (rest : List Nat),
    rest.length ≤ fuel → (build fuel m rest).flatten = rest := by
  intro fuel
  induction fuel with
  | zero =>
      intro m rest h
      have : rest = [] := by
        cases rest with
        | nil => rfl
        | cons a t => simp at h
      simp [this, build]
  | succ fuel ih =>
      intro m rest h
      cases rest with
      | nil => simp [build]
      | cons a t =>
          simp only [build, List.flatten_cons]
          rw [ih _ _ (by
            have hd : ((a :: t).drop (2 * (m + 1))).length =
                (a :: t).length - 2 * (m + 1) := List.length_drop
            simp at h ⊢
            omega)]
          exact List.take_append_drop _ _

/-- From the heap condition, the dyadic chain is valid. -/
theorem chain_of_heap_aux {w : List Nat} (hheap : HeapCond w) :
    ∀ (fuel : Nat) (rest pre prev : List Nat),
      rest.length ≤ fuel →
      w = pre ++ prev ++ rest →
      prev.length = pre.length + 1 →
      Chain prev (build fuel (prev.length - 1) rest) := by
  intro fuel
  induction fuel with
  | zero =>
      intro rest pre prev hf hw hinv
      have : rest = [] := by
        cases rest with
        | nil => rfl
        | cons a t => simp at hf
      rw [this]; exact .nil
  | succ fuel ih =>
      intro rest pre prev hf hw hinv
      cases rest with
      | nil => exact .nil
      | cons a t =>
          have hprevpos : 1 ≤ prev.length := by omega
          have hm : prev.length - 1 + 1 = prev.length := by omega
          have hclen : (a :: t).length = t.length + 1 := rfl
          simp only [build, hm]
          have hLlen : ((a :: t).take (2 * prev.length)).length =
              min (2 * prev.length) (a :: t).length := List.length_take
          have hLne : (a :: t).take (2 * prev.length) ≠ [] := by
            intro hcon
            have := congrArg List.length hcon
            rw [hLlen] at this
            simp at this
            omega
          have hfeas : Feas prev ((a :: t).take (2 * prev.length)) := by
            refine feas_of_balanced prev _ (by rw [hLlen]; omega) ?_
            intro j hj hp
            have hjr : j < (a :: t).length := by rw [hLlen] at hj; omega
            have hval : ((a :: t).take (2 * prev.length))[j]'hj =
                (a :: t)[j]'hjr := List.getElem_take
            rw [hval]
            have hglobal : pre.length + prev.length + j < w.length := by
              rw [hw]; simp; omega
            have hheapj := hheap (pre.length + prev.length + j) (by omega)
              hglobal
            -- child value
            have hwX : w = (pre ++ prev) ++ (a :: t) ++ [] := by
              rw [hw]; simp [List.append_assoc]
            have hchild : w[pre.length + prev.length + j]'hglobal =
                (a :: t)[j]'hjr := by
              have e₁ := getElem_of_eq hwX hglobal
              have hidx : pre.length + prev.length + j =
                  (pre ++ prev).length + j := by simp
              have e₂ := getElem_idx (l := (pre ++ prev) ++ (a :: t) ++ [])
                hidx (hwX ▸ hglobal)
              have e₃ := getElem_mid (pre := pre ++ prev) (mid := a :: t)
                (post := []) j hjr (by simp; omega)
              rw [e₁, e₂, e₃]
            -- parent value
            have hpidx : (pre.length + prev.length + j - 1) / 2 =
                pre.length + j / 2 := by omega
            have hparbound : pre.length + j / 2 < w.length := by
              rw [hw]; simp; omega
            have hpar : w[pre.length + j / 2]'hparbound = prev[j / 2]'hp := by
              have e₁ := getElem_of_eq hw hparbound
              have e₃ := getElem_mid (pre := pre) (mid := prev)
                (post := a :: t) (j / 2) hp (by simp; omega)
              rw [e₁, e₃]
            have e := getElem_idx (l := w) hpidx (by omega)
            rw [e, hpar, hchild] at hheapj
            exact hheapj
          refine Chain.cons hLne hfeas ?_
          by_cases hshort : (a :: t).length ≤ 2 * prev.length
          · -- partial level: nothing remains below
            have hdrop : (a :: t).drop (2 * prev.length) = [] :=
              List.drop_eq_nil_of_le hshort
            rw [hdrop]
            cases fuel with
            | zero => exact .nil
            | succ f => simp only [build]; exact .nil
          · -- full level: recurse with the exact invariant
            have hfull : ((a :: t).take (2 * prev.length)).length =
                2 * prev.length := by rw [hLlen]; omega
            have hdl : ((a :: t).drop (2 * prev.length)).length =
                (a :: t).length - 2 * prev.length := List.length_drop
            have hih := ih ((a :: t).drop (2 * prev.length))
              (pre ++ prev) ((a :: t).take (2 * prev.length))
              (by simp at hf ⊢; omega)
              (by
                rw [hw]
                rw [show (pre ++ prev) ++ (a :: t).take (2 * prev.length) ++
                    (a :: t).drop (2 * prev.length) =
                    (pre ++ prev) ++ ((a :: t).take (2 * prev.length) ++
                    (a :: t).drop (2 * prev.length)) from by
                  simp [List.append_assoc]]
                rw [List.take_append_drop])
              (by rw [hfull]; simp; omega)
            exact hih

/-- Theorem A, backward direction. -/
theorem ubword_of_heap {w : List Nat} (hne : w ≠ []) (hheap : HeapCond w) :
    UBWord w := by
  cases w with
  | nil => exact absurd rfl hne
  | cons hd t =>
      refine ⟨hd, build t.length 0 t, ?_, ?_⟩
      · rw [flatten_build t.length 0 t (Nat.le_refl _)]
      · have h := chain_of_heap_aux hheap t.length t [] [hd]
          (Nat.le_refl _) (by simp) (by simp)
        exact h

/-- **Theorem A**: for a 312-avoiding word with distinct letters,
being a BFS word of an increasing unary-binary tree is equivalent to the
binary-heap condition. -/
theorem theoremA {w : List Nat} (hnd : w.Nodup) (hav : ¬ Has312 w)
    (hne : w ≠ []) : UBWord w ↔ HeapCond w :=
  ⟨heap_of_ubword hnd hav, ubword_of_heap hne⟩

end BfsWords
