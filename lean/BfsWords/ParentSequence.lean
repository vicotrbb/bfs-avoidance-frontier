/- General branching bounds in the global BFS parent representation. -/
import BfsWords.Basic

namespace BfsWords

/-- The child numbered `t` has word position `t + 1` and parent position
`p t`. Equal parents occupy consecutive intervals, so `capacity` says
precisely that every parent has at most `k` children. -/
structure ParentSequence (n k : Nat) (p : Nat → Nat) : Prop where
  before : ∀ t, t + 1 < n → p t ≤ t
  monotone : ∀ i j, i ≤ j → j + 1 < n → p i ≤ p j
  capacity : ∀ i j, i ≤ j → j + 1 < n → p i = p j → j < i + k

/-- Every edge respects the increasing labels of the word. -/
def ParentIncreasing (w : List Nat) (p : Nat → Nat) : Prop :=
  ∀ t, (ht : t + 1 < w.length) → (hp : p t < w.length) →
    w[p t]'hp < w[t + 1]'ht

/-- Three increasing positions give a three-element sublist. -/
theorem parent_triple_sublist (w : List Nat) (a b c : Nat)
    (hab : a < b) (hbc : b < c) (hc : c < w.length) :
    [w[a]'(by omega), w[b]'(by omega), w[c]'hc].Sublist w := by
  induction w generalizing a b c with
  | nil => simp at hc
  | cons x xs ih =>
    cases a with
    | zero =>
      cases b with
      | zero => omega
      | succ b =>
        cases c with
        | zero => omega
        | succ c =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          exact .cons₂ x (pair_sublist xs b c (by omega) (by simpa using hc))
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        cases c with
        | zero => omega
        | succ c =>
          simp only [List.getElem_cons_succ]
          exact .cons x (ih a b c (by omega) (by omega) (by simpa using hc))

/-- Capacity forces the complete-heap parent to precede every possible parent. -/
theorem ParentSequence.heap_parent_le {n k : Nat} {p : Nat → Nat}
    (h : ParentSequence n k p) (hk : 0 < k) (t : Nat) (ht : t + 1 < n) :
    t / k ≤ p t := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases hsmall : t < k
    · simp [Nat.div_eq_of_lt hsmall]
    · have hkt : k ≤ t := by omega
      have hprev : t - k < t := by omega
      have hmono := h.monotone (t - k) t (by omega) ht
      have hstrict : p (t - k) < p t := by
        by_cases hs : p (t - k) < p t
        · exact hs
        have heq : p (t - k) = p t := by omega
        have hcap := h.capacity (t - k) t (by omega) ht heq
        omega
      have hrec := ih (t - k) hprev (by omega)
      have hdiv : t / k = (t - k) / k + 1 := by
        have heq : t = (t - k) + k := by omega
        calc
          t / k = ((t - k) + k) / k := congrArg (fun x => x / k) heq
          _ = (t - k) / k + 1 := Nat.add_div_right (t - k) hk
      omega

/-- Complete `k`-ary heap inequalities, indexed by nonroot vertices. -/
def HeapCondK (w : List Nat) (k : Nat) : Prop :=
  ∀ t, (ht : t + 1 < w.length) →
    w[t / k]'(by have := Nat.div_le_self t k; omega) < w[t + 1]'ht

/-- Theorem A for every positive branching bound, in parent coordinates. -/
theorem parent_theoremA {w : List Nat} {p : Nat → Nat} {k : Nat}
    (hk : 0 < k) (hp : ParentSequence w.length k p)
    (hi : ParentIncreasing w p) (hd : w.Nodup) (ha : ¬ Has312 w) :
    HeapCondK w k := by
  intro t ht
  have hbefore := hp.before t ht
  have hq := hp.heap_parent_le hk t ht
  have hedge := hi t ht (by omega)
  by_cases heq : t / k = p t
  · simpa [heq] using hedge
  · have hlt : t / k < p t := by omega
    have hne := nodup_getElem_ne hd (i := t / k) (j := t + 1)
      (by omega) ht (by omega)
    by_cases hs : w[t / k] < w[t + 1]
    · exact hs
    exfalso
    have hbad : w[t + 1] < w[t / k] := by omega
    exact ha ⟨w[t / k], w[p t], w[t + 1],
      parent_triple_sublist w (t / k) (p t) (t + 1) hlt (by omega) ht,
      hedge, hbad⟩

/-- First nonroot index in the block containing `t`. -/
def blockStart (k t : Nat) : Nat := k * (t / k)

theorem blockStart_le (k t : Nat) : blockStart k t ≤ t := by
  have := Nat.div_add_mod t k
  unfold blockStart
  omega

theorem lt_blockStart_add {k : Nat} (hk : 0 < k) (t : Nat) :
    t < blockStart k t + k := by
  have := Nat.div_add_mod t k
  have := Nat.mod_lt t hk
  unfold blockStart
  omega

theorem blockStart_mono {i j : Nat} (k : Nat) (hij : i ≤ j) :
    blockStart k i ≤ blockStart k j :=
  Nat.mul_le_mul_left k (Nat.div_le_div_right hij)

theorem blockStart_gap {k i j : Nat} (hij : i / k < j / k) :
    blockStart k i + k ≤ blockStart k j := by
  have hm := Nat.mul_le_mul_left k (show i / k + 1 ≤ j / k by omega)
  simpa [blockStart, Nat.mul_add] using hm

/-- Regroup each complete block under its first vertex's former parent. -/
def regroupParent (k : Nat) (p : Nat → Nat) (t : Nat) : Nat :=
  p (blockStart k t)

theorem regroup_strict {n k : Nat} {p : Nat → Nat}
    (hp : ParentSequence n k p) {i j : Nat}
    (hij : i / k < j / k) (hj : j + 1 < n) :
    regroupParent k p i < regroupParent k p j := by
  have hgap := blockStart_gap hij
  have hle := blockStart_le k j
  have hm := hp.monotone (blockStart k i) (blockStart k j) (by omega) (by omega)
  unfold regroupParent
  by_cases hs : p (blockStart k i) < p (blockStart k j)
  · exact hs
  have heq : p (blockStart k i) = p (blockStart k j) := by omega
  have hc := hp.capacity (blockStart k i) (blockStart k j) (by omega) (by omega) heq
  omega

/-- Regrouping preserves the parent-sequence constraints. -/
theorem regroup_valid {n k : Nat} {p : Nat → Nat}
    (hk : 0 < k) (hp : ParentSequence n k p) :
    ParentSequence n k (regroupParent k p) := by
  constructor
  · intro t ht
    have hb := blockStart_le k t
    have hbefore := hp.before (blockStart k t) (by omega)
    exact Nat.le_trans hbefore hb
  · intro i j hij hj
    exact hp.monotone _ _ (blockStart_mono k hij)
      (by have := blockStart_le k j; omega)
  · intro i j hij hj heq
    have hdiv := Nat.div_le_div_right (c := k) hij
    have he : i / k = j / k := by
      by_cases he : i / k = j / k
      · exact he
      have hs := regroup_strict hp (show i / k < j / k by omega) hj
      omega
    have hi := blockStart_le k i
    have hj := lt_blockStart_add hk j
    have hb : blockStart k i = blockStart k j := by simp [blockStart, he]
    omega

/-- Avoidance of 231 ensures that every edge created by regrouping increases. -/
theorem regroup_increasing {w : List Nat} {k : Nat} {p : Nat → Nat}
    (hp : ParentSequence w.length k p) (hi : ParentIncreasing w p)
    (hd : w.Nodup) (ha : ¬ Has231 w) :
    ParentIncreasing w (regroupParent k p) := by
  intro t ht hr
  have hs := blockStart_le k t
  have hb := hp.before (blockStart k t) (by omega)
  have hedge := hi (blockStart k t) (by omega) (by omega)
  unfold regroupParent at hr ⊢
  by_cases he : blockStart k t = t
  · simpa [he] using hedge
  · have hlt : blockStart k t < t := by omega
    have hne := nodup_getElem_ne hd (i := p (blockStart k t)) (j := t + 1)
      (by omega) ht (by omega)
    by_cases hh : w[p (blockStart k t)] < w[t + 1]
    · exact hh
    exfalso
    have hbad : w[t + 1] < w[p (blockStart k t)] := by omega
    exact ha ⟨w[p (blockStart k t)], w[blockStart k t + 1], w[t + 1],
      parent_triple_sublist w _ _ _ (by omega) (by omega) ht, hbad, hedge⟩

/-- Exact fibers of the regrouped map are the consecutive blocks of `k`
nonroot vertices. When `n = k * m + 1`, all these blocks are complete. -/
theorem regroup_fibers {n k : Nat} {p : Nat → Nat}
    (hp : ParentSequence n k p) {i j : Nat}
    (hi : i + 1 < n) (hj : j + 1 < n) :
    regroupParent k p i = regroupParent k p j ↔ i / k = j / k := by
  constructor
  · intro heq
    by_cases he : i / k = j / k
    · exact he
    by_cases hij : i / k < j / k
    · have := regroup_strict hp hij hj; omega
    · have := regroup_strict hp (show j / k < i / k by omega) hi; omega
  · intro heq
    simp [regroupParent, blockStart, heq]

/-- A full sequence has exactly `m` distinct used parents. Parent block `b`
has exactly the `k` child indices `k * b + s`, with `s < k`. The fiber
condition rules out a parent being shared by different blocks. -/
def FullParentSequence (n k : Nat) (p : Nat → Nat) : Prop :=
  ∃ m, n = k * m + 1 ∧
    ∀ i j, i + 1 < n → j + 1 < n → (p i = p j ↔ i / k = j / k)

/-- Theorem B for every positive branching bound, in parent coordinates. -/
theorem parent_theoremB {w : List Nat} {k m : Nat} {p : Nat → Nat}
    (hk : 0 < k) (hlen : w.length = k * m + 1)
    (hp : ParentSequence w.length k p) (hi : ParentIncreasing w p)
    (hd : w.Nodup) (ha : ¬ Has231 w) :
    ParentSequence w.length k (regroupParent k p) ∧
    ParentIncreasing w (regroupParent k p) ∧
    FullParentSequence w.length k (regroupParent k p) := by
  exact ⟨regroup_valid hk hp, regroup_increasing hp hi hd ha,
    m, hlen, fun _ _ hi hj => regroup_fibers hp hi hj⟩

/-- The complete heap itself is a valid parent sequence. -/
theorem heap_parent_valid (n : Nat) {k : Nat} (hk : 0 < k) :
    ParentSequence n k (fun t => t / k) := by
  constructor
  · intro t _; exact Nat.div_le_self t k
  · intro i j hij _; exact Nat.div_le_div_right hij
  · intro i j _ _ heq
    have hi := blockStart_le k i
    have hj := lt_blockStart_add hk j
    have hb : blockStart k i = blockStart k j := by simp [blockStart, heq]
    omega

/-- The complete parent-sequence equivalence for the pattern 312. -/
theorem parent_theoremA_iff {w : List Nat} {k : Nat}
    (hk : 0 < k) (hd : w.Nodup) (ha : ¬ Has312 w) :
    (∃ p, ParentSequence w.length k p ∧ ParentIncreasing w p) ↔
    HeapCondK w k := by
  constructor
  · rintro ⟨p, hp, hi⟩
    exact parent_theoremA hk hp hi hd ha
  · intro hh
    exact ⟨fun t => t / k, heap_parent_valid w.length hk, fun t ht _ => hh t ht⟩

/-- The fiber of quotient `b` consists of exactly the `k` indices in its block. -/
theorem quotient_fiber {k t b : Nat} (hk : 0 < k) :
    t / k = b ↔ ∃ s, s < k ∧ t = k * b + s := by
  constructor
  · intro he
    refine ⟨t % k, Nat.mod_lt t hk, ?_⟩
    have hd := Nat.div_add_mod t k
    rw [he] at hd
    exact hd.symm
  · rintro ⟨s, hs, rfl⟩
    simp [Nat.mul_add_div hk, Nat.div_eq_of_lt hs]

/-- Every fiber in the full construction is precisely one complete block,
with its `k` members displayed explicitly. -/
theorem regroup_full_children {n k m : Nat} {p : Nat → Nat}
    (hk : 0 < k) (hn : n = k * m + 1) (hp : ParentSequence n k p)
    {b : Nat} (hb : b < m) (j : Nat) (hj : j + 1 < n) :
    regroupParent k p j = regroupParent k p (k * b) ↔
    ∃ s, s < k ∧ j = k * b + s := by
  have hbm := Nat.mul_lt_mul_of_pos_left hb hk
  have hbvalid : k * b + 1 < n := by omega
  rw [regroup_fibers hp hj hbvalid, Nat.mul_div_cancel_left b hk]
  exact quotient_fiber hk

/-- Every displayed member of a complete block lies in the nonroot domain. -/
theorem full_block_member {n k m b s : Nat}
    (hn : n = k * m + 1) (hb : b < m) (hs : s < k) :
    k * b + s + 1 < n := by
  have hmul := Nat.mul_le_mul_left k (show b + 1 ≤ m by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

end BfsWords
