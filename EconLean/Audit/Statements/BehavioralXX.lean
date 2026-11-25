/-
# Frozen statements: behavioral round 20

Headline statements of `Behavioral/SalienceAllais.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-20.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.SalienceAllais

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXX

section SalienceAllais
open Econ.Salience Finset


theorem frozen_prefers_common_consequence {ι : Type*} [Fintype ι] [DecidableEq ι] (θ δ : ℝ)
    (π : ι → ℝ) {x y x' y' : ι → ℝ} (s₀ : ι)
    (hx : ∀ s, s ≠ s₀ → x s = x' s) (hy : ∀ s, s ≠ s₀ → y s = y' s)
    (h₀ : x s₀ = y s₀) (h₀' : x' s₀ = y' s₀) :
    Prefers θ δ π x y ↔ Prefers θ δ π x' y' := by
  first
  | exact @Econ.Salience.prefers_common_consequence ..
  | (apply @Econ.Salience.prefers_common_consequence <;> assumption)

theorem frozen_piA_isFullProb : IsFullProb piA := by
  first
  | exact @Econ.Salience.piA_isFullProb ..
  | (apply @Econ.Salience.piA_isFullProb <;> assumption)

theorem frozen_piB_isFullProb : IsFullProb piB := by
  first
  | exact @Econ.Salience.piB_isFullProb ..
  | (apply @Econ.Salience.piB_isFullProb <;> assumption)

theorem frozen_piB_product : piB = ![11 / 100 * (1 / 10), 11 / 100 * (9 / 10),
    89 / 100 * (1 / 10), 89 / 100 * (9 / 10)] := by
  first
  | exact @Econ.Salience.piB_product ..
  | (apply @Econ.Salience.piB_product <;> assumption)

theorem frozen_allaisA_sum {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (δ : ℝ) :
    ∑ s, piA s * factor θ δ L1 L2 s * (L1 s - L2 s) = 1 / 100 - 4 / 10 * δ := by
  first
  | exact @Econ.Salience.allaisA_sum ..
  | (apply @Econ.Salience.allaisA_sum <;> assumption)

theorem frozen_allaisB_sum {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (δ : ℝ) :
    ∑ s, piB s * factor θ δ L1i L2i s * (L1i s - L2i s) =
      -(44 / 1000) * δ ^ 2 + 99 / 1000 * δ - 445 / 1000 := by
  first
  | exact @Econ.Salience.allaisB_sum ..
  | (apply @Econ.Salience.allaisB_sum <;> assumption)

theorem frozen_allaisA_safe {θ δ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (hδ : δ < 1 / 40) :
    0 < ∑ s, piA s * factor θ δ L1 L2 s * (L1 s - L2 s) := by
  first
  | exact @Econ.Salience.allaisA_safe ..
  | (apply @Econ.Salience.allaisA_safe <;> assumption)

theorem frozen_allaisB_risky {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (δ : ℝ) :
    ∑ s, piB s * factor θ δ L1i L2i s * (L1i s - L2i s) < 0 := by
  first
  | exact @Econ.Salience.allaisB_risky ..
  | (apply @Econ.Salience.allaisB_risky <;> assumption)

theorem frozen_allais_paradox {θ δ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (hδ : δ < 1 / 40) :
    0 < ∑ s, piA s * factor θ δ L1 L2 s * (L1 s - L2 s) ∧
      ∑ s, piB s * factor θ δ L1i L2i s * (L1i s - L2i s) < 0 := by
  first
  | exact @Econ.Salience.allais_paradox ..
  | (apply @Econ.Salience.allais_paradox <;> assumption)

theorem frozen_allaisA_eu (θ : ℝ) : ∑ s, piA s * factor θ 1 L1 L2 s * (L1 s - L2 s) < 0 := by
  first
  | exact @Econ.Salience.allaisA_eu ..
  | (apply @Econ.Salience.allaisA_eu <;> assumption)

theorem frozen_eu_no_allais (u : ℝ → ℝ) :
    (∑ s, piA s * u (L2 s) < ∑ s, piA s * u (L1 s)) ↔
      (∑ s, piB s * u (L2i s) < ∑ s, piB s * u (L1i s)) := by
  first
  | exact @Econ.Salience.eu_no_allais ..
  | (apply @Econ.Salience.eu_no_allais <;> assumption)

theorem frozen_allaisB_correlated_iff (θ δ : ℝ) :
    Prefers θ δ piA L1c L2c ↔ Prefers θ δ piA L1 L2 := by
  first
  | exact @Econ.Salience.allaisB_correlated_iff ..
  | (apply @Econ.Salience.allaisB_correlated_iff <;> assumption)

theorem frozen_allaisB_correlated_iff' (θ δ : ℝ) :
    Prefers θ δ piA L2c L1c ↔ Prefers θ δ piA L2 L1 := by
  first
  | exact @Econ.Salience.allaisB_correlated_iff' ..
  | (apply @Econ.Salience.allaisB_correlated_iff' <;> assumption)

theorem frozen_marginals_B :
    (∑ s, if L1i s = 1 then piB s else 0) = 11 / 100 ∧
    (∑ s, if L2i s = 5 then piB s else 0) = 1 / 10 ∧
    (∀ s, L1i s = 0 ∨ L1i s = 1) ∧ (∀ s, L2i s = 0 ∨ L2i s = 5) ∧
    (∑ s, if L1c s = 1 then piA s else 0) = 11 / 100 ∧
    (∑ s, if L2c s = 5 then piA s else 0) = 1 / 10 ∧
    (∀ s, L1c s = 0 ∨ L1c s = 1) ∧ (∀ s, L2c s = 0 ∨ L2c s = 5) := by
  first
  | exact @Econ.Salience.marginals_B ..
  | (apply @Econ.Salience.marginals_B <;> assumption)

end SalienceAllais

end Econ.Audit.BehavioralXX
