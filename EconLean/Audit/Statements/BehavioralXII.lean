/-
# Frozen statements: behavioral round 12

Headline statements of `BoundedRationality/Robinson.lean` and
`BoundedRationality/PoissonCH.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-12.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.Robinson
public import EconLean.BoundedRationality.PoissonCH

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXII

section Robinson
open Econ.Robinson Finset Filter Topology
variable {I J : Type*} [DecidableEq I] [DecidableEq J]
variable {A : I → J → ℝ} {I' : Finset I} {J' : Finset J} {U : ℕ → I → ℝ} {V : ℕ → J → ℝ} {i : ℕ → I} {j : ℕ → J} {T : ℕ} {a : ℝ}

theorem frozen_sum_identity (h : IsSystem A I' J' U V i j T) :
    ∑ τ ∈ range T, U T (i τ) - ∑ τ ∈ range T, V T (j τ) =
      ∑ τ ∈ range T, U 0 (i τ) - ∑ τ ∈ range T, V 0 (j τ) := by
  first
  | exact @Econ.Robinson.sum_identity ..
  | (apply @Econ.Robinson.sum_identity <;> assumption)

theorem frozen_gap_le_of_eligible (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a)
    (hI : I'.Nonempty) (hJ : J'.Nonempty) (hT : 0 < T)
    (hinit : I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0)) {n : ℕ} (hn : n ≤ T)
    (hrow : ∀ k ∈ I', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ U σ k = I'.sup' hI (U σ))
    (hcol : ∀ l ∈ J', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ V σ l = J'.inf' hJ (V σ)) :
    gap I' J' hI hJ U V T ≤ 4 * a * n := by
  first
  | exact @Econ.Robinson.gap_le_of_eligible ..
  | (apply @Econ.Robinson.gap_le_of_eligible <;> assumption)

theorem frozen_eventually_good (ha : ∀ k l, |A k l| ≤ a) :
    ∀ (N : ℕ) (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty) (hJ : J'.Nonempty),
      I'.card + J'.card = N → ∀ ε > 0, ∀ᶠ t in atTop, Good A I' J' hI hJ ε t := by
  first
  | exact @Econ.Robinson.eventually_good ..
  | (apply @Econ.Robinson.eventually_good <;> assumption)

end Robinson

section Robinson
open Econ.Robinson Finset Filter Topology
variable {I J : Type*} [DecidableEq I] [DecidableEq J] {A : I → J → ℝ} {i : ℕ → I} {j : ℕ → J}
variable [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

theorem frozen_exploit_nonneg (h : IsFPPath A i j) (t : ℕ) : 0 ≤ exploit A i j t := by
  first
  | exact @Econ.Robinson.exploit_nonneg ..
  | (apply @Econ.Robinson.exploit_nonneg <;> assumption)

theorem frozen_robinson (h : IsFPPath A i j) : Tendsto (exploit A i j) atTop (𝓝 0) := by
  first
  | exact @Econ.Robinson.robinson ..
  | (apply @Econ.Robinson.robinson <;> assumption)

theorem frozen_payoff_le_max (A : I → J → ℝ) (j : ℕ → J) {t : ℕ} (ht : 0 < t) {x : I → ℝ}
    (hx : x ∈ lotteries I) :
    matrixPayoff A x (colFreq j t) ≤ univ.sup' univ_nonempty (rowPay A j t) / t := by
  first
  | exact @Econ.Robinson.payoff_le_max ..
  | (apply @Econ.Robinson.payoff_le_max <;> assumption)

theorem frozen_min_le_payoff (A : I → J → ℝ) (i : ℕ → I) {t : ℕ} (ht : 0 < t) {y : J → ℝ}
    (hy : y ∈ lotteries J) :
    univ.inf' univ_nonempty (colPay A i t) / t ≤ matrixPayoff A (rowFreq i t) y := by
  first
  | exact @Econ.Robinson.min_le_payoff ..
  | (apply @Econ.Robinson.min_le_payoff <;> assumption)

theorem frozen_isEpsSaddle_freq (A : I → J → ℝ) (i : ℕ → I) (j : ℕ → J) {t : ℕ} (ht : 0 < t) :
    (∀ x ∈ lotteries I, matrixPayoff A x (colFreq j t) ≤
      matrixPayoff A (rowFreq i t) (colFreq j t) + exploit A i j t) ∧
    ∀ y ∈ lotteries J, matrixPayoff A (rowFreq i t) (colFreq j t) - exploit A i j t ≤
      matrixPayoff A (rowFreq i t) y := by
  first
  | exact @Econ.Robinson.isEpsSaddle_freq ..
  | (apply @Econ.Robinson.isEpsSaddle_freq <;> assumption)

theorem frozen_eventually_isEpsSaddle (h : IsFPPath A i j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, rowFreq i t ∈ lotteries I ∧ colFreq j t ∈ lotteries J ∧
      (∀ x ∈ lotteries I, matrixPayoff A x (colFreq j t) ≤
        matrixPayoff A (rowFreq i t) (colFreq j t) + ε) ∧
      ∀ y ∈ lotteries J, matrixPayoff A (rowFreq i t) (colFreq j t) - ε ≤
        matrixPayoff A (rowFreq i t) y := by
  first
  | exact @Econ.Robinson.eventually_isEpsSaddle ..
  | (apply @Econ.Robinson.eventually_isEpsSaddle <;> assumption)

theorem frozen_tendsto_payoff_value (h : IsFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => matrixPayoff A (rowFreq i t) (colFreq j t)) atTop (𝓝 v) := by
  first
  | exact @Econ.Robinson.tendsto_payoff_value ..
  | (apply @Econ.Robinson.tendsto_payoff_value <;> assumption)

theorem frozen_tendsto_max_min_value (h : IsFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => univ.sup' univ_nonempty (rowPay A j t) / t) atTop (𝓝 v) ∧
    Tendsto (fun t => univ.inf' univ_nonempty (colPay A i t) / t) atTop (𝓝 v) := by
  first
  | exact @Econ.Robinson.tendsto_max_min_value ..
  | (apply @Econ.Robinson.tendsto_max_min_value <;> assumption)

theorem frozen_isFPPath_fp (A : I → J → ℝ) : IsFPPath A (fpRow A) (fpCol A) := by
  first
  | exact @Econ.Robinson.isFPPath_fp ..
  | (apply @Econ.Robinson.isFPPath_fp <;> assumption)

end Robinson

section PoissonCH
open Econ.BoundedRationality Finset Filter Topology NNReal
variable {f : ℕ → ℝ}

theorem frozen_hasSum_poissonFreq (τ : ℝ≥0) : HasSum (poissonFreq τ) 1 := by
  first
  | exact @Econ.BoundedRationality.hasSum_poissonFreq ..
  | (apply @Econ.BoundedRationality.hasSum_poissonFreq <;> assumption)

theorem frozen_poissonFreq_succ (τ : ℝ≥0) (k : ℕ) :
    poissonFreq τ (k + 1) = τ / (k + 1) * poissonFreq τ k := by
  first
  | exact @Econ.BoundedRationality.poissonFreq_succ ..
  | (apply @Econ.BoundedRationality.poissonFreq_succ <;> assumption)

theorem frozen_hasSum_mean_poissonFreq (τ : ℝ≥0) : HasSum (fun k : ℕ => k * poissonFreq τ k) τ := by
  first
  | exact @Econ.BoundedRationality.hasSum_mean_poissonFreq ..
  | (apply @Econ.BoundedRationality.hasSum_mean_poissonFreq <;> assumption)

theorem frozen_sum_chBelief (hf : ∀ h, 0 < f h) {k : ℕ} (hk : 0 < k) :
    ∑ h ∈ range k, chBelief f k h = 1 := by
  first
  | exact @Econ.BoundedRationality.sum_chBelief ..
  | (apply @Econ.BoundedRationality.sum_chBelief <;> assumption)

theorem frozen_chBelief_ratio {k h h' : ℕ} (hh : h < k) (hh' : h' < k) :
    chBelief f k h * f h' = chBelief f k h' * f h := by
  first
  | exact @Econ.BoundedRationality.chBelief_ratio ..
  | (apply @Econ.BoundedRationality.chBelief_ratio <;> assumption)

theorem frozen_hasSum_abs_chBelief_sub (hf : ∀ h, 0 < f h) (hsum : HasSum f 1) {k : ℕ} (hk : 0 < k) :
    HasSum (fun h => |chBelief f k h - f h|) (2 * (1 - ∑ g ∈ range k, f g)) := by
  first
  | exact @Econ.BoundedRationality.hasSum_abs_chBelief_sub ..
  | (apply @Econ.BoundedRationality.hasSum_abs_chBelief_sub <;> assumption)

theorem frozen_l1_strictAnti (hf : ∀ h, 0 < f h) :
    StrictAnti (fun k => 2 * (1 - ∑ g ∈ range k, f g)) := by
  first
  | exact @Econ.BoundedRationality.l1_strictAnti ..
  | (apply @Econ.BoundedRationality.l1_strictAnti <;> assumption)

theorem frozen_tendsto_l1_chBelief (hf : ∀ h, 0 < f h) (hsum : HasSum f 1) :
    Tendsto (fun k => ∑' h, |chBelief f k h - f h|) atTop (𝓝 0) := by
  first
  | exact @Econ.BoundedRationality.tendsto_l1_chBelief ..
  | (apply @Econ.BoundedRationality.tendsto_l1_chBelief <;> assumption)

theorem frozen_tendsto_chBelief (hsum : HasSum f 1) (h : ℕ) :
    Tendsto (fun k => chBelief f k h) atTop (𝓝 (f h)) := by
  first
  | exact @Econ.BoundedRationality.tendsto_chBelief ..
  | (apply @Econ.BoundedRationality.tendsto_chBelief <;> assumption)

theorem frozen_poisson_hasSum_l1 {τ : ℝ≥0} (hτ : 0 < τ) {k : ℕ} (hk : 0 < k) :
    HasSum (fun h => |chBelief (poissonFreq τ) k h - poissonFreq τ h|)
      (2 * (1 - ∑ g ∈ range k, poissonFreq τ g)) := by
  first
  | exact @Econ.BoundedRationality.poisson_hasSum_l1 ..
  | (apply @Econ.BoundedRationality.poisson_hasSum_l1 <;> assumption)

theorem frozen_poisson_tendsto_l1 {τ : ℝ≥0} (hτ : 0 < τ) :
    Tendsto (fun k => ∑' h, |chBelief (poissonFreq τ) k h - poissonFreq τ h|) atTop (𝓝 0) := by
  first
  | exact @Econ.BoundedRationality.poisson_tendsto_l1 ..
  | (apply @Econ.BoundedRationality.poisson_tendsto_l1 <;> assumption)

theorem frozen_poisson_chGuess_strictAnti {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {τ : ℝ≥0} (hτ : 0 < τ) :
    StrictAnti (chGuess p (poissonFreq τ)) := by
  first
  | exact @Econ.BoundedRationality.poisson_chGuess_strictAnti ..
  | (apply @Econ.BoundedRationality.poisson_chGuess_strictAnti <;> assumption)

end PoissonCH

end Econ.Audit.BehavioralXII
