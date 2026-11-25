/-
# Frozen statements: behavioral round 28

Headline statements of `Behavioral/GumbelLogit.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-28.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.GumbelLogit

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXVIII

section GumbelLogit
open Econ.GumbelLogit Real MeasureTheory Filter Topology Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem frozen_hasDerivAt_gumbelAnti (S x : ℝ) (hS : S ≠ 0) :
    HasDerivAt (fun x => exp (-(S * exp (-x))) / S) (exp (-x) * exp (-(S * exp (-x)))) x := by
  first
  | exact @Econ.GumbelLogit.hasDerivAt_gumbelAnti ..
  | (apply @Econ.GumbelLogit.hasDerivAt_gumbelAnti <;> assumption)

theorem frozen_tendsto_gumbelAnti_atBot {S : ℝ} (hS : 0 < S) :
    Tendsto (fun x => exp (-(S * exp (-x))) / S) atBot (𝓝 0) := by
  first
  | exact @Econ.GumbelLogit.tendsto_gumbelAnti_atBot ..
  | (apply @Econ.GumbelLogit.tendsto_gumbelAnti_atBot <;> assumption)

theorem frozen_tendsto_gumbelAnti_atTop (S : ℝ) :
    Tendsto (fun x => exp (-(S * exp (-x))) / S) atTop (𝓝 (1 / S)) := by
  first
  | exact @Econ.GumbelLogit.tendsto_gumbelAnti_atTop ..
  | (apply @Econ.GumbelLogit.tendsto_gumbelAnti_atTop <;> assumption)

theorem frozen_gumbelInt_nonneg (S x : ℝ) : 0 ≤ exp (-x) * exp (-(S * exp (-x))) := by
  first
  | exact @Econ.GumbelLogit.gumbelInt_nonneg ..
  | (apply @Econ.GumbelLogit.gumbelInt_nonneg <;> assumption)

theorem frozen_integrable_gumbelInt {S : ℝ} (hS : 0 < S) :
    Integrable fun x => exp (-x) * exp (-(S * exp (-x))) := by
  first
  | exact @Econ.GumbelLogit.integrable_gumbelInt ..
  | (apply @Econ.GumbelLogit.integrable_gumbelInt <;> assumption)

theorem frozen_integral_gumbelInt {S : ℝ} (hS : 0 < S) :
    ∫ x, exp (-x) * exp (-(S * exp (-x))) = 1 / S := by
  first
  | exact @Econ.GumbelLogit.integral_gumbelInt ..
  | (apply @Econ.GumbelLogit.integral_gumbelInt <;> assumption)

theorem frozen_gumbelPDF_eq (x : ℝ) : gumbelPDF x = exp (-x) * exp (-(1 * exp (-x))) := by
  first
  | exact @Econ.GumbelLogit.gumbelPDF_eq ..
  | (apply @Econ.GumbelLogit.gumbelPDF_eq <;> assumption)

theorem frozen_continuous_gumbelPDF : Continuous gumbelPDF := by
  first
  | exact @Econ.GumbelLogit.continuous_gumbelPDF ..
  | (apply @Econ.GumbelLogit.continuous_gumbelPDF <;> assumption)

theorem frozen_integrable_gumbelPDF : Integrable gumbelPDF := by
  first
  | exact @Econ.GumbelLogit.integrable_gumbelPDF ..
  | (apply @Econ.GumbelLogit.integrable_gumbelPDF <;> assumption)

theorem frozen_gumbel_Iic (a : ℝ) : gumbel (Iic a) = ENNReal.ofReal (gumbelCDF a) := by
  first
  | exact @Econ.GumbelLogit.gumbel_Iic ..
  | (apply @Econ.GumbelLogit.gumbel_Iic <;> assumption)

theorem frozen_measurableSet_chooses (v : ι → ℝ) (i : ι) : MeasurableSet (chooses v i) := by
  first
  | exact @Econ.GumbelLogit.measurableSet_chooses ..
  | (apply @Econ.GumbelLogit.measurableSet_chooses <;> assumption)

theorem frozen_gumbel_integrand (v : ι → ℝ) (i : ι) (t : ℝ) :
    gumbelPDF t * ∏ j : {j // ¬ j = i}, gumbelCDF (t + (v i - v j)) =
      exp (-t) * exp (-((∑ j, exp (v j - v i)) * exp (-t))) := by
  first
  | exact @Econ.GumbelLogit.gumbel_integrand ..
  | (apply @Econ.GumbelLogit.gumbel_integrand <;> assumption)

theorem frozen_gumbel_choice (v : ι → ℝ) (i : ι) :
    (Measure.pi fun _ : ι => gumbel) (chooses v i) = ENNReal.ofReal (Logit.softmax 1 v i) := by
  first
  | exact @Econ.GumbelLogit.gumbel_choice ..
  | (apply @Econ.GumbelLogit.gumbel_choice <;> assumption)

theorem frozen_gumbel_choice_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ε : ι → Ω → ℝ} (hmeas : ∀ j, Measurable (ε j))
    (hind : ProbabilityTheory.iIndepFun ε P) (hlaw : ∀ j, P.map (ε j) = gumbel)
    (v : ι → ℝ) (i : ι) :
    P {ω | ∀ j, v j + ε j ω ≤ v i + ε i ω} = ENNReal.ofReal (Logit.softmax 1 v i) := by
  first
  | exact @Econ.GumbelLogit.gumbel_choice_indep ..
  | (apply @Econ.GumbelLogit.gumbel_choice_indep <;> assumption)

theorem frozen_gumbel_choice_sum [Nonempty ι] (v : ι → ℝ) :
    ∑ i, (Measure.pi fun _ : ι => gumbel) (chooses v i) = 1 := by
  first
  | exact @Econ.GumbelLogit.gumbel_choice_sum ..
  | (apply @Econ.GumbelLogit.gumbel_choice_sum <;> assumption)

end GumbelLogit

end Econ.Audit.BehavioralXXVIII
