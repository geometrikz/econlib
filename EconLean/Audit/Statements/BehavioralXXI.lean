/-
# Frozen statements: behavioral round 21

Headline statements of `Behavioral/SalienceCommonRatio.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-21.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.SalienceCommonRatio

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXI

section SalienceCommonRatio
open Econ.Salience Finset


theorem frozen_piCA_isFullProb : IsFullProb piCA := by
  first
  | exact @Econ.Salience.piCA_isFullProb ..
  | (apply @Econ.Salience.piCA_isFullProb <;> assumption)

theorem frozen_piCB_isFullProb : IsFullProb piCB := by
  first
  | exact @Econ.Salience.piCB_isFullProb ..
  | (apply @Econ.Salience.piCB_isFullProb <;> assumption)

theorem frozen_crB_product : piCB = ![1 / 4 * (2 / 10), 1 / 4 * (8 / 10),
    3 / 4 * (2 / 10), 3 / 4 * (8 / 10)] := by
  first
  | exact @Econ.Salience.crB_product ..
  | (apply @Econ.Salience.crB_product <;> assumption)

theorem frozen_marginals_cr :
    (∑ s, if C1i s = 3 then piCB s else 0) = 1 / 4 ∧
    (∑ s, if C2i s = 4 then piCB s else 0) = 2 / 10 ∧
    (∀ s, C1i s = 0 ∨ C1i s = 3) ∧ (∀ s, C2i s = 0 ∨ C2i s = 4) ∧
    (∑ s, if C2 s = 4 then piCA s else 0) = 8 / 10 ∧
    (∀ s, C1 s = 3) ∧ (∀ s, C2 s = 0 ∨ C2 s = 4) := by
  first
  | exact @Econ.Salience.marginals_cr ..
  | (apply @Econ.Salience.marginals_cr <;> assumption)

theorem frozen_ranks_CA {θ : ℝ} (hθ0 : 0 < θ) :
    rank (salience θ C1 C2) 0 = 1 ∧ rank (salience θ C1 C2) 1 = 0 := by
  first
  | exact @Econ.Salience.ranks_CA ..
  | (apply @Econ.Salience.ranks_CA <;> assumption)

theorem frozen_ranks_CB {θ : ℝ} (hθ0 : 0 < θ) :
    rank (salience θ C1i C2i) 0 = 2 ∧ rank (salience θ C1i C2i) 1 = 1 ∧
      rank (salience θ C1i C2i) 2 = 0 ∧ rank (salience θ C1i C2i) 3 = 3 := by
  first
  | exact @Econ.Salience.ranks_CB ..
  | (apply @Econ.Salience.ranks_CB <;> assumption)

theorem frozen_crA_sum {θ : ℝ} (hθ0 : 0 < θ) (δ : ℝ) :
    ∑ s, piCA s * factor θ δ C1 C2 s * (C1 s - C2 s) = 6 / 10 - 8 / 10 * δ := by
  first
  | exact @Econ.Salience.crA_sum ..
  | (apply @Econ.Salience.crA_sum <;> assumption)

theorem frozen_crB_sum {θ : ℝ} (hθ0 : 0 < θ) (δ : ℝ) :
    ∑ s, piCB s * factor θ δ C1i C2i s * (C1i s - C2i s) =
      -(5 / 100) * δ ^ 2 + 6 / 10 * δ - 6 / 10 := by
  first
  | exact @Econ.Salience.crB_sum ..
  | (apply @Econ.Salience.crB_sum <;> assumption)

theorem frozen_crA_safe_iff {θ : ℝ} (hθ0 : 0 < θ) (δ : ℝ) :
    0 < ∑ s, piCA s * factor θ δ C1 C2 s * (C1 s - C2 s) ↔ δ < 3 / 4 := by
  first
  | exact @Econ.Salience.crA_safe_iff ..
  | (apply @Econ.Salience.crA_safe_iff <;> assumption)

theorem frozen_crB_risky {θ δ : ℝ} (hθ0 : 0 < θ) (hδ : δ ≤ 1) :
    ∑ s, piCB s * factor θ δ C1i C2i s * (C1i s - C2i s) < 0 := by
  first
  | exact @Econ.Salience.crB_risky ..
  | (apply @Econ.Salience.crB_risky <;> assumption)

theorem frozen_common_ratio {θ δ : ℝ} (hθ0 : 0 < θ) (hδ : δ < 3 / 4) :
    0 < ∑ s, piCA s * factor θ δ C1 C2 s * (C1 s - C2 s) ∧
      ∑ s, piCB s * factor θ δ C1i C2i s * (C1i s - C2i s) < 0 := by
  first
  | exact @Econ.Salience.common_ratio ..
  | (apply @Econ.Salience.common_ratio <;> assumption)

theorem frozen_crA_eu (θ : ℝ) : ∑ s, piCA s * factor θ 1 C1 C2 s * (C1 s - C2 s) < 0 := by
  first
  | exact @Econ.Salience.crA_eu ..
  | (apply @Econ.Salience.crA_eu <;> assumption)

theorem frozen_eu_no_common_ratio (u : ℝ → ℝ) :
    (∑ s, piCA s * u (C2 s) < ∑ s, piCA s * u (C1 s)) ↔
      (∑ s, piCB s * u (C2i s) < ∑ s, piCB s * u (C1i s)) := by
  first
  | exact @Econ.Salience.eu_no_common_ratio ..
  | (apply @Econ.Salience.eu_no_common_ratio <;> assumption)

theorem frozen_common_ratio_prefers {θ δ : ℝ} (hθ0 : 0 < θ) (_hδ0 : 0 < δ) (hδ : δ < 3 / 4) :
    (Prefers θ δ piCA C1 C2 ∧ ¬ Prefers θ δ piCA C2 C1) ∧
      (Prefers θ δ piCB C2i C1i ∧ ¬ Prefers θ δ piCB C1i C2i) := by
  first
  | exact @Econ.Salience.common_ratio_prefers ..
  | (apply @Econ.Salience.common_ratio_prefers <;> assumption)

end SalienceCommonRatio

end Econ.Audit.BehavioralXXI
