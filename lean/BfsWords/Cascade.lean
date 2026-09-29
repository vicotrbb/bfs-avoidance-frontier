/-
The promotion cascade (Lemma B5 / "T+"), fully unconditional:
growing the previous level by the next element never destroys
realizability of the remaining suffix.
-/
import BfsWords.TheoremA

namespace BfsWords

/-- Total depth of a chain: `Σ_t (t+1)·|L_t|`, computed as the sum of
suffix-flatten lengths.  Strictly decreases under promotion. -/
def depth : List (List Nat) → Nat
  | [] => 0
  | L :: ls => (L :: ls).flatten.length + depth ls

/-- Split a feasibility certificate along a split of the parents. -/
theorem Feas.split {P₁ P₂ C : List Nat} (h : Feas (P₁ ++ P₂) C) :
    ∃ C₁ C₂, C = C₁ ++ C₂ ∧ Feas P₁ C₁ ∧ Feas P₂ C₂ := by
  induction P₁ generalizing C with
  | nil => exact ⟨[], C, by simp, .nil, by simpa using h⟩
  | cons p P₁ ih =>
      cases h with
      | cons hg hgt hrec =>
          rename_i g C'
          obtain ⟨C₁, C₂, rfl, h₁, h₂⟩ := ih hrec
          exact ⟨g ++ C₁, C₂, by simp [List.append_assoc],
            Feas.cons hg hgt h₁, h₂⟩

/-- Children of a singleton parent list all exceed that parent. -/
theorem Feas.singleton_gt {x : Nat} {g : List Nat} (h : Feas [x] g) :
    g.length ≤ 2 ∧ ∀ c ∈ g, x < c := by
  cases h with
  | cons hg hgt hrec =>
      cases hrec
      constructor
      · simpa using hg
      · intro c hc
        exact hgt c (by simpa using hc)

/-- A chain under an empty level is empty (as a word). -/
theorem Chain.nil_flatten {ls : List (List Nat)} (h : Chain [] ls) :
    ls = [] := by
  cases h with
  | nil => rfl
  | @cons _ L ls' hne hfeas hrest =>
      exfalso
      have hle := hfeas.length_le
      simp at hle
      cases L with
      | nil => exact hne rfl
      | cons a t => simp at hle

/-- The cascade auxiliary: below a level split as `J ++ D`, the promoted
head `J₂` (old children of `J`) can be surfaced.  No pattern hypothesis. -/
theorem chain_S : ∀ {ls : List (List Nat)} {J D : List Nat},
    Chain (J ++ D) ls →
    ∃ J₂ ls', ls.flatten = J₂ ++ ls'.flatten ∧ Feas J J₂ ∧
      Chain (D ++ J₂) ls' ∧ depth ls' ≤ depth ls := by
  intro ls
  induction ls with
  | nil =>
      intro J D _
      exact ⟨[], [], by simp, Feas.empty J, by simpa using Chain.nil, by simp⟩
  | cons L ls₀ ih =>
      intro J D hc
      cases hc with
      | cons hLne hfeas hchain =>
          obtain ⟨J₂, M, rfl, hJ₂, hM⟩ := hfeas.split
          obtain ⟨J₃, ls₁, hflat₁, hJ₃, hchain₁, hdep₁⟩ := ih (J := J₂) (D := M) hchain
          by_cases hMJ : M ++ J₃ = []
          · -- everything below is exhausted
            obtain ⟨hM0, hJ₃0⟩ := List.append_eq_nil_iff.mp hMJ
            have hls₁ : ls₁ = [] := by
              rw [hM0, hJ₃0] at hchain₁
              exact Chain.nil_flatten (by simpa using hchain₁)
            refine ⟨J₂, [], ?_, hJ₂, by simpa using Chain.nil, by simp [depth]⟩
            rw [hls₁, hJ₃0] at hflat₁
            simp at hflat₁
            simp [List.flatten_cons, hM0]
            exact hflat₁
          · -- surface the promoted heads one level up
            refine ⟨J₂, (M ++ J₃) :: ls₁, ?_, hJ₂, ?_, ?_⟩
            · rw [List.flatten_cons, List.flatten_cons, hflat₁]
              simp [List.append_assoc]
            · exact Chain.cons hMJ (Feas.append hM hJ₃) hchain₁
            · -- depth bookkeeping
              have hlen : ls₀.flatten.length = J₃.length + ls₁.flatten.length := by
                have := congrArg List.length hflat₁
                simpa using this
              simp only [depth, List.flatten_cons]
              simp only [List.length_append]
              omega

/-- **Promotion cascade (T+)**: if the suffix `x :: rest` is realizable
below `prev`, then `rest` is realizable below `prev ++ [x]`, with strictly
smaller total depth.  Holds for every word ; no pattern condition. -/
theorem chain_plus {prev : List Nat} {ls : List (List Nat)} {x : Nat}
    {rest : List Nat} (hc : Chain prev ls) (hflat : ls.flatten = x :: rest) :
    ∃ ls', Chain (prev ++ [x]) ls' ∧ ls'.flatten = rest ∧
      depth ls' < depth ls := by
  cases hc with
  | nil => simp at hflat
  | cons hLne hfeas hchain =>
      rename_i L ls₀
      -- L = x :: L₀
      cases L with
      | nil => exact absurd rfl hLne
      | cons y L₀ =>
          have hxy : y = x ∧ L₀ ++ ls₀.flatten = rest := by
            rw [List.flatten_cons] at hflat
            simpa using hflat
          obtain ⟨rfl, hrest⟩ := hxy
          have hprevL₀ : Feas prev L₀ := hfeas.dropHead
          have hSC : Chain ([y] ++ L₀) ls₀ := by simpa using hchain
          obtain ⟨J₂, ls₁, hflat₁, hJ₂, hchain₁, hdep₁⟩ := chain_S hSC
          obtain ⟨hJ₂len, hJ₂gt⟩ := hJ₂.singleton_gt
          by_cases hLJ : L₀ ++ J₂ = []
          · -- the whole suffix was just `[x]`
            obtain ⟨hL₀, hJ₂0⟩ := List.append_eq_nil_iff.mp hLJ
            have hls₁ : ls₁ = [] := by
              rw [hL₀, hJ₂0] at hchain₁
              exact Chain.nil_flatten (by simpa using hchain₁)
            have hflat₀ : ls₀.flatten = [] := by
              rw [hls₁, hJ₂0] at hflat₁
              simpa using hflat₁
            refine ⟨[], Chain.nil, ?_, ?_⟩
            · rw [← hrest, hL₀, hflat₀]; simp
            · simp only [depth, List.flatten_cons]
              simp only [List.length_append, List.length_cons]
              omega
          · refine ⟨(L₀ ++ J₂) :: ls₁, ?_, ?_, ?_⟩
            · exact Chain.cons hLJ (Feas.snoc hprevL₀ hJ₂len hJ₂gt) hchain₁
            · rw [List.flatten_cons, ← hrest, hflat₁]
              simp [List.append_assoc]
            · have hlen : ls₀.flatten.length =
                  J₂.length + ls₁.flatten.length := by
                have := congrArg List.length hflat₁
                simpa using this
              simp only [depth, List.flatten_cons]
              simp only [List.length_append, List.length_cons]
              omega

end BfsWords
