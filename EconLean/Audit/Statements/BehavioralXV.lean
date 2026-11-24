/-
# Frozen statements: behavioral round 15

Headline statements of `BoundedRationality/AlternatingFP.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-15.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.AlternatingFP

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXV

section AlternatingFP
open Econ.Robinson Finset Filter Topology
variable {I J : Type*} [DecidableEq I] [DecidableEq J] {A : I → J → ℝ} {I' : Finset I} {J' : Finset J} {U : ℕ → I → ℝ} {V : ℕ → J → ℝ} {i : ℕ → I} {j : ℕ → J} {T : ℕ} {a δ : ℝ}

theorem frozen_sum_identityS (h : IsSystemS A I' J' U V i j T δ) :
    ∑ τ ∈ range T, U T (i τ) - ∑ τ ∈ range T, V T (j τ) =
      ∑ τ ∈ range T, U 0 (i τ) - ∑ τ ∈ range T, V 0 (j τ) := by
  first
  | exact @Econ.Robinson.sum_identityS ..
  | (apply @Econ.Robinson.sum_identityS <;> assumption)

theorem frozen_gap_le_of_eligibleS (h : IsSystemS A I' J' U V i j T δ) (ha : ∀ k l, |A k l| ≤ a)
    (hI : I'.Nonempty) (hJ : J'.Nonempty) (hT : 0 < T)
    (hinit : I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0)) {n : ℕ} (hn : n ≤ T)
    (hrow : ∀ k ∈ I', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ I'.sup' hI (U σ) ≤ U σ k + δ)
    (hcol : ∀ l ∈ J', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ V σ l ≤ J'.inf' hJ (V σ) + δ) :
    gap I' J' hI hJ U V T ≤ 4 * a * n + 2 * δ := by
  first
  | exact @Econ.Robinson.gap_le_of_eligibleS ..
  | (apply @Econ.Robinson.gap_le_of_eligibleS <;> assumption)

theorem frozen_eventually_goodS (ha : ∀ k l, |A k l| ≤ a) (hδ : 0 ≤ δ) :
    ∀ (N : ℕ) (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty) (hJ : J'.Nonempty),
      I'.card + J'.card = N → ∀ ε > 0, ∀ᶠ t in atTop, GoodS A I' J' hI hJ δ ε t := by
  first
  | exact @Econ.Robinson.eventually_goodS ..
  | (apply @Econ.Robinson.eventually_goodS <;> assumption)

end AlternatingFP

section AlternatingFP
open Econ.Robinson Finset Filter Topology
variable {I J : Type*} [DecidableEq I] [DecidableEq J] {A : I → J → ℝ} {i : ℕ → I} {j : ℕ → J} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

theorem frozen_robinson_alt (h : IsAltFPPath A i j) : Tendsto (exploit A i j) atTop (𝓝 0) := by
  first
  | exact @Econ.Robinson.robinson_alt ..
  | (apply @Econ.Robinson.robinson_alt <;> assumption)

theorem frozen_eventually_isEpsSaddle_alt (h : IsAltFPPath A i j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, rowFreq i t ∈ lotteries I ∧ colFreq j t ∈ lotteries J ∧
      (∀ x ∈ lotteries I, matrixPayoff A x (colFreq j t) ≤
        matrixPayoff A (rowFreq i t) (colFreq j t) + ε) ∧
      ∀ y ∈ lotteries J, matrixPayoff A (rowFreq i t) (colFreq j t) - ε ≤
        matrixPayoff A (rowFreq i t) y := by
  first
  | exact @Econ.Robinson.eventually_isEpsSaddle_alt ..
  | (apply @Econ.Robinson.eventually_isEpsSaddle_alt <;> assumption)

theorem frozen_tendsto_payoff_value_alt (h : IsAltFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => matrixPayoff A (rowFreq i t) (colFreq j t)) atTop (𝓝 v) := by
  first
  | exact @Econ.Robinson.tendsto_payoff_value_alt ..
  | (apply @Econ.Robinson.tendsto_payoff_value_alt <;> assumption)

theorem frozen_tendsto_max_min_value_alt (h : IsAltFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => univ.sup' univ_nonempty (rowPay A j t) / t) atTop (𝓝 v) ∧
    Tendsto (fun t => univ.inf' univ_nonempty (colPay A i t) / t) atTop (𝓝 v) := by
  first
  | exact @Econ.Robinson.tendsto_max_min_value_alt ..
  | (apply @Econ.Robinson.tendsto_max_min_value_alt <;> assumption)

theorem frozen_isAltFPPath_alt (A : I → J → ℝ) : IsAltFPPath A (altRow A) (altCol A) := by
  first
  | exact @Econ.Robinson.isAltFPPath_alt ..
  | (apply @Econ.Robinson.isAltFPPath_alt <;> assumption)

end AlternatingFP

end Econ.Audit.BehavioralXV
