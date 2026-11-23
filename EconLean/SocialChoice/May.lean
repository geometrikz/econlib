/-
# May's theorem on majority rule

May (1952); MWG Prop. 21.B.1 (Ch. 21.B). A society of voters `I` chooses between two
alternatives `x` and `y`. A **profile** records each voter's preference as `1` (`x` strictly
preferred), `-1` (`y` strictly preferred) or `0` (indifferent). A **social decision rule**
`F` maps profiles to `1`, `0` or `-1` in the same way.

Axioms (MWG §21.B):
* **anonymity**: permuting the voters does not change the outcome;
* **neutrality**: reversing every voter's preference reverses the outcome, `F(−α) = −F(α)`;
* **positive responsiveness**: if `x` is weakly socially preferred at `α` and some voters move
  toward `x` (and nobody moves away), then `x` becomes strictly preferred.

Main result, `may_theorem`: a rule satisfies the three axioms iff it is **majority rule**,
`F(α) = sign(∑ᵢ αᵢ)`.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A **voting profile**: every voter's preference is `1`, `0` or `-1`. -/
def IsVoteProfile (α : I → ℤ) : Prop := ∀ i, α i = 1 ∨ α i = 0 ∨ α i = -1

/-- **Majority rule**: the sign of the vote total. -/
def majorityRule (α : I → ℤ) : ℤ := Int.sign (∑ i, α i)

/-- **Anonymity.** -/
def IsAnonymous (F : (I → ℤ) → ℤ) : Prop :=
  ∀ (σ : Equiv.Perm I) α, IsVoteProfile α → F (α ∘ σ) = F α

/-- **Neutrality** between the two alternatives. -/
def IsNeutral (F : (I → ℤ) → ℤ) : Prop := ∀ α, IsVoteProfile α → F (-α) = -F α

/-- **Positive responsiveness.** -/
def IsPositivelyResponsive (F : (I → ℤ) → ℤ) : Prop :=
  ∀ α α', IsVoteProfile α → IsVoteProfile α' → α ≤ α' → α ≠ α' → 0 ≤ F α → F α' = 1

omit [Fintype I] [DecidableEq I] in
lemma IsVoteProfile.neg {α : I → ℤ} (h : IsVoteProfile α) : IsVoteProfile (-α) := fun i => by
  rcases h i with h | h | h <;> simp [h]

omit [DecidableEq I] in
/-- The vote total counts supporters of `x` minus supporters of `y`. -/
lemma sum_eq_card_sub_card {α : I → ℤ} (h : IsVoteProfile α) :
    ∑ i, α i = (univ.filter fun i => α i = 1).card - (univ.filter fun i => α i = -1).card := by
  have : ∀ i, α i = (if α i = 1 then 1 else 0) - (if α i = -1 then 1 else 0) := fun i => by
    rcases h i with h | h | h <;> simp [h]
  rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, sum_boole, sum_boole]

omit [DecidableEq I] in
/-- **Anonymity depends only on vote counts.** -/
lemma IsAnonymous.eq_of_card {F : (I → ℤ) → ℤ} (hF : IsAnonymous F) {α β : I → ℤ}
    (hβ : IsVoteProfile β)
    (hc : ∀ v, (univ.filter fun i => α i = v).card = (univ.filter fun i => β i = v).card) :
    F α = F β := by
  classical
  have e : ∀ v, { a // α a = v } ≃ { b // β b = v } := fun v =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact hc v)
  set σ := Equiv.ofFiberEquiv e
  have : α = β ∘ σ := funext fun a => (Equiv.ofFiberEquiv_map e a).symm
  rw [this, hF σ β hβ]

/-- **May's theorem** (May 1952; MWG Prop. 21.B.1). A social decision rule on two alternatives
is anonymous, neutral and positively responsive iff it is majority rule on every profile. -/
theorem may_theorem (F : (I → ℤ) → ℤ) :
    IsAnonymous F ∧ IsNeutral F ∧ IsPositivelyResponsive F ↔
      ∀ α, IsVoteProfile α → F α = majorityRule α := by
  constructor
  · rintro ⟨hA, hN, hP⟩
    -- A tied profile gives indifference.
    have htie : ∀ α, IsVoteProfile α → ∑ i, α i = 0 → F α = 0 := by
      intro α hα hs
      have hcnt := sum_eq_card_sub_card hα
      rw [hs] at hcnt
      have hneg : F (-α) = F α := by
        refine hA.eq_of_card hα fun v => ?_
        have e : ∀ w : ℤ, (univ.filter fun i => (-α) i = w) = univ.filter fun i => α i = -w :=
          fun w => by ext i; simp only [mem_filter, mem_univ, true_and, Pi.neg_apply]; omega
        rw [e]
        by_cases hv : v = 1
        · subst hv; omega
        · by_cases hv' : v = -1
          · subst hv'; simp only [neg_neg]; omega
          · by_cases hv0 : v = 0
            · subst hv0; simp
            · have h1 : (univ.filter fun i => α i = -v) = ∅ := by
                ext i; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty,
                  iff_false]; rcases hα i with h | h | h <;> omega
              have h2 : (univ.filter fun i => α i = v) = ∅ := by
                ext i; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty,
                  iff_false]; rcases hα i with h | h | h <;> omega
              rw [h1, h2]
      have := hN α hα
      omega
    -- A strict majority for `x` makes `x` win.
    have hposw : ∀ α, IsVoteProfile α → 0 < ∑ i, α i → F α = 1 := by
      intro α hα hs
      classical
      have hcnt := sum_eq_card_sub_card hα
      have hd : (∑ i, α i).toNat ≤ (univ.filter fun i => α i = 1).card := by omega
      obtain ⟨T, hTP, hTc⟩ := exists_subset_card_eq hd
      set β : I → ℤ := fun i => if i ∈ T then 0 else α i
      have hβ : IsVoteProfile β := fun i => by
        simp only [β]; split_ifs
        · exact Or.inr (Or.inl rfl)
        · exact hα i
      have hβsum : ∑ i, β i = 0 := by
        have : ∀ i, β i = α i - if i ∈ T then 1 else 0 := fun i => by
          simp only [β]; split_ifs with h
          · have := (mem_filter.1 (hTP h)).2; omega
          · ring
        rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, sum_boole]
        simp only [filter_mem_eq_inter, univ_inter, hTc]
        omega
      have hle : β ≤ α := fun i => by
        simp only [β]; split_ifs with h
        · have := (mem_filter.1 (hTP h)).2; omega
        · exact le_rfl
      have hne : β ≠ α := by
        obtain ⟨i, hi⟩ : T.Nonempty := by
          rw [← card_pos, hTc]; omega
        intro heq
        have := congrFun heq i
        simp only [β, hi, ↓reduceIte] at this
        have := (mem_filter.1 (hTP hi)).2
        omega
      exact hP β α hβ hα hle hne (by rw [htie β hβ hβsum])
    intro α hα
    simp only [majorityRule]
    rcases lt_trichotomy (∑ i, α i) 0 with hs | hs | hs
    · have h1 := hposw (-α) hα.neg (by simp only [Pi.neg_apply, sum_neg_distrib]; omega)
      rw [hN α hα] at h1
      rw [Int.sign_eq_neg_one_of_neg hs]; omega
    · rw [hs, htie α hα hs]; rfl
    · rw [hposw α hα hs, Int.sign_eq_one_of_pos hs]
  · intro hF
    refine ⟨fun σ α hα => ?_, fun α hα => ?_, fun α α' hα hα' hle hne h0 => ?_⟩
    · have hσ : IsVoteProfile (α ∘ σ) := fun i => hα (σ i)
      rw [hF _ hσ, hF _ hα, majorityRule, majorityRule]
      simp only [Function.comp_apply, Equiv.sum_comp σ α]
    · rw [hF _ hα.neg, hF _ hα, majorityRule, majorityRule]
      simp only [Pi.neg_apply, sum_neg_distrib, Int.sign_neg]
    · rw [hF _ hα, majorityRule] at h0
      rw [hF _ hα', majorityRule]
      have hs0 : 0 ≤ ∑ i, α i := by
        by_contra h; push Not at h; rw [Int.sign_eq_neg_one_of_neg h] at h0; omega
      obtain ⟨i, hi⟩ : ∃ i, α i < α' i := by
        by_contra h; push Not at h
        exact hne (funext fun i => le_antisymm (hle i) (h i))
      have : ∑ i, α i < ∑ i, α' i :=
        sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ i, hi⟩
      exact Int.sign_eq_one_of_pos (by omega)

end Econ
