/-
# Logit from Gumbel random utility (McFadden 1974)

References. D. McFadden (1974), "Conditional Logit Analysis of Qualitative
Choice Behavior", in *Frontiers in Econometrics*; E. J. Gumbel (1958);
K. Train (2009), *Discrete Choice Methods with Simulation*, §3.10.

**Random utility.** Alternative `j` has utility `v j + ε j`, where the shocks
`ε j` are independent standard Gumbel: CDF `exp(−e^{−x})`, density
`e^{−x} exp(−e^{−x})` (`gumbelCDF`, `gumbelPDF`, `gumbel`, a probability
measure on `ℝ`). `chooses v i` is the event that `i` is a best alternative.

**Results.**
* `integral_gumbelInt`: `∫ e^{−x} exp(−S e^{−x}) dx = 1/S` for `S > 0`, with
  `gumbel_Iic` (the CDF) and the `IsProbabilityMeasure` instance.
* `gumbel_choice` (**McFadden**): under the product of standard Gumbel laws,
  `P(i is chosen) = e^{v i} / Σ_j e^{v j}`, the multinomial logit
  `Logit.softmax 1 v i`. Proof: condition on `ε i = t`; the others are below
  `t + v i − v j` with probability `Π_{j≠i} exp(−e^{−t} e^{v j − v i})`, and
  integrating against the density gives `1 / Σ_j e^{v j − v i}`.
* `gumbel_choice_indep`: the same for independent random variables with
  Gumbel laws on any probability space.
* `gumbel_choice_sum`: the choice probabilities sum to one (which implies
  that ties are null; that consequence is not stated separately).

**Scope.** Shocks have unit scale; scale `λ` gives `softmax λ` by rescaling `v`
(not stated separately). Nested logit / GEV models are not formalized.
-/
module

public import EconLean.Behavioral.Logit
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace Econ

namespace GumbelLogit

open Real MeasureTheory Filter Topology Set

/-- The antiderivative `exp(−S e^{−x}) / S`. -/
theorem hasDerivAt_gumbelAnti (S x : ℝ) (hS : S ≠ 0) :
    HasDerivAt (fun x => exp (-(S * exp (-x))) / S) (exp (-x) * exp (-(S * exp (-x)))) x := by
  have h1 : HasDerivAt (fun x => -(S * exp (-x))) (S * exp (-x)) x := by
    have := ((hasDerivAt_neg x).exp.const_mul S).neg
    convert this using 1; ring
  have := (h1.exp).div_const S
  convert this using 1
  field_simp

theorem tendsto_gumbelAnti_atBot {S : ℝ} (hS : 0 < S) :
    Tendsto (fun x => exp (-(S * exp (-x))) / S) atBot (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => exp (-x)) atBot atTop :=
    tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun x : ℝ => -(S * exp (-x))) atBot atBot :=
    tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hS)
  simpa using (tendsto_exp_atBot.comp h2).div_const S

theorem tendsto_gumbelAnti_atTop (S : ℝ) :
    Tendsto (fun x => exp (-(S * exp (-x))) / S) atTop (𝓝 (1 / S)) := by
  have h1 : Tendsto (fun x : ℝ => exp (-x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h2 : Tendsto (fun x : ℝ => exp (-(S * exp (-x))) / S) atTop (𝓝 (exp (-(S * 0)) / S)) :=
    ((continuous_exp.tendsto _).comp ((h1.const_mul S).neg)).div_const S
  simpa using h2

theorem gumbelInt_nonneg (S x : ℝ) : 0 ≤ exp (-x) * exp (-(S * exp (-x))) :=
  mul_nonneg (exp_pos _).le (exp_pos _).le

theorem integrable_gumbelInt {S : ℝ} (hS : 0 < S) :
    Integrable fun x => exp (-x) * exp (-(S * exp (-x))) := by
  have hc : Continuous fun x => exp (-x) * exp (-(S * exp (-x))) := by fun_prop
  refine integrable_of_intervalIntegral_norm_tendsto (a := fun i : ℝ => -i) (b := id)
    (l := atTop) (1 / S) (fun i => hc.integrableOn_Ioc) tendsto_neg_atTop_atBot tendsto_id ?_
  have hF : ∀ a b : ℝ, ∫ x in a..b, ‖exp (-x) * exp (-(S * exp (-x)))‖ =
      exp (-(S * exp (-b))) / S - exp (-(S * exp (-a))) / S := by
    intro a b
    rw [intervalIntegral.integral_congr (g := fun x => exp (-x) * exp (-(S * exp (-x))))
      (fun x _ => by simp only [Real.norm_eq_abs, abs_of_nonneg (gumbelInt_nonneg S x)])]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_gumbelAnti S x hS.ne') (hc.intervalIntegrable _ _)
  simp only [hF]
  have := (tendsto_gumbelAnti_atTop S).sub ((tendsto_gumbelAnti_atBot hS).comp
    (tendsto_neg_atTop_atBot))
  simpa using this

/-- `∫ e^{−x} exp(−S e^{−x}) dx = 1 / S`. -/
theorem integral_gumbelInt {S : ℝ} (hS : 0 < S) :
    ∫ x, exp (-x) * exp (-(S * exp (-x))) = 1 / S := by
  rw [integral_of_hasDerivAt_of_tendsto (fun x => hasDerivAt_gumbelAnti S x hS.ne')
    (integrable_gumbelInt hS) (tendsto_gumbelAnti_atBot hS) (tendsto_gumbelAnti_atTop S)]
  ring

/-! ### The Gumbel distribution -/

/-- Standard Gumbel CDF `exp(−e^{−x})`. -/
noncomputable def gumbelCDF (x : ℝ) : ℝ := exp (-exp (-x))

/-- Standard Gumbel density `e^{−x} exp(−e^{−x})`. -/
noncomputable def gumbelPDF (x : ℝ) : ℝ := exp (-x) * exp (-exp (-x))

/-- The standard Gumbel distribution on `ℝ`. -/
noncomputable def gumbel : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (gumbelPDF x)

theorem gumbelPDF_eq (x : ℝ) : gumbelPDF x = exp (-x) * exp (-(1 * exp (-x))) := by
  simp [gumbelPDF]

theorem continuous_gumbelPDF : Continuous gumbelPDF := by
  unfold gumbelPDF; fun_prop

theorem integrable_gumbelPDF : Integrable gumbelPDF := by
  have h := integrable_gumbelInt one_pos
  simp only [one_mul] at h
  exact h

/-- `P(Gumbel ≤ a) = exp(−e^{−a})`. -/
theorem gumbel_Iic (a : ℝ) : gumbel (Iic a) = ENNReal.ofReal (gumbelCDF a) := by
  rw [gumbel, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal integrable_gumbelPDF.integrableOn
      (ae_of_all _ fun x => gumbelInt_nonneg 1 x |>.trans_eq (gumbelPDF_eq x).symm)]
  congr 1
  have := integral_Iic_of_hasDerivAt_of_tendsto' (a := a)
    (fun x _ => hasDerivAt_gumbelAnti 1 x one_ne_zero) (integrable_gumbelInt one_pos).integrableOn
    (tendsto_gumbelAnti_atBot one_pos)
  simp only [gumbelPDF_eq]
  rw [this]; simp [gumbelCDF]

instance : IsProbabilityMeasure gumbel := by
  constructor
  rw [gumbel, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_gumbelPDF
      (ae_of_all _ fun x => gumbelInt_nonneg 1 x |>.trans_eq (gumbelPDF_eq x).symm)]
  simp only [gumbelPDF_eq, integral_gumbelInt one_pos]
  simp

/-! ### McFadden: iid Gumbel shocks give the logit -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The event that `i` is a best alternative under random utility `v j + ε j`. -/
def chooses (v : ι → ℝ) (i : ι) : Set (ι → ℝ) := {ε | ∀ j, v j + ε j ≤ v i + ε i}

omit [DecidableEq ι] in
theorem measurableSet_chooses (v : ι → ℝ) (i : ι) : MeasurableSet (chooses v i) := by
  have : chooses v i = ⋂ j, {ε : ι → ℝ | v j + ε j ≤ v i + ε i} := by ext; simp [chooses]
  rw [this]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le (measurable_const.add (measurable_pi_apply j))
      (measurable_const.add (measurable_pi_apply i))

/-- The real integrand: density of the winner's shock times the probability that
all others fall below. -/
theorem gumbel_integrand (v : ι → ℝ) (i : ι) (t : ℝ) :
    gumbelPDF t * ∏ j : {j // ¬ j = i}, gumbelCDF (t + (v i - v j)) =
      exp (-t) * exp (-((∑ j, exp (v j - v i)) * exp (-t))) := by
  have hsplit : ∑ j, exp (v j - v i) = 1 + ∑ j : {j // ¬ j = i}, exp (v j - v i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j = i) (fun j => exp (v j - v i))]
    congr 1
    have h1 : ∀ j : {j // j = i}, exp (v j - v i) = 1 := fun j => by
      rw [j.2, sub_self, exp_zero]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_subtype_eq, one_smul]
  have hprod : ∏ j : {j // ¬ j = i}, gumbelCDF (t + (v i - v j)) =
      exp (-((∑ j : {j // ¬ j = i}, exp (v j - v i)) * exp (-t))) := by
    unfold gumbelCDF
    rw [← exp_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← exp_add]
    congr 2
    ring
  unfold gumbelPDF
  rw [hprod, hsplit, mul_assoc, ← exp_add]
  congr 2
  ring

/-- **McFadden (1974): logit from Gumbel random utility.** With independent
standard Gumbel shocks (the product measure), the probability that `i`
maximizes `v j + ε j` is the multinomial logit `e^{v i} / Σ_j e^{v j}`. -/
theorem gumbel_choice (v : ι → ℝ) (i : ι) :
    (Measure.pi fun _ : ι => gumbel) (chooses v i) = ENNReal.ofReal (Logit.softmax 1 v i) := by
  let p : ι → Prop := fun j => j = i
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gumbel) p
  set B : Set (({j // p j} → ℝ) × ({j // ¬ p j} → ℝ)) :=
    {z | ∀ j : {j // ¬ p j}, z.2 j ≤ z.1 ⟨i, rfl⟩ + (v i - v j)} with hBdef
  have hA : chooses v i = MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p ⁻¹' B := by
    ext ε
    simp only [chooses, Set.mem_ofPred_eq, Set.mem_preimage, hBdef,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
    constructor
    · intro h j; have := h j; simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]; linarith
    · intro h j
      by_cases hj : j = i
      · subst hj; exact le_rfl
      · have := h ⟨j, hj⟩; simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk] at this; linarith
  have hB : MeasurableSet B := by
    have : B = ⋂ j : {j // ¬ p j}, {z | z.2 j ≤ z.1 ⟨i, rfl⟩ + (v i - v j)} := by
      ext; simp [hBdef]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le
      ((measurable_pi_apply j).comp measurable_snd)
      (((measurable_pi_apply _).comp measurable_fst).add measurable_const)
  rw [hA, hmp.measure_preimage hB.nullMeasurableSet, Measure.prod_apply hB]
  have hsec : ∀ x : {j // p j} → ℝ, Prod.mk x ⁻¹' B =
      Set.pi Set.univ fun j : {j // ¬ p j} => Iic (x ⟨i, rfl⟩ + (v i - v j)) := by
    intro x; ext y; simp [hBdef, Pi.le_def]
  simp_rw [hsec, Measure.pi_pi, gumbel_Iic]
  let _ : Unique {j // p j} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.2⟩
  set g : ℝ → ENNReal := fun t =>
    ∏ j : {j // ¬ p j}, ENNReal.ofReal (gumbelCDF (t + (v i - v j)))
  have hg : Measurable g := Finset.measurable_prod _ fun j _ =>
    (ENNReal.continuous_ofReal.comp (by unfold gumbelCDF; fun_prop)).measurable
  have hU := measurePreserving_piUnique (fun _ : {j // p j} => gumbel)
  have key : ∫⁻ x : {j // p j} → ℝ, ∏ j : {j // ¬ p j},
      ENNReal.ofReal (gumbelCDF (x ⟨i, rfl⟩ + (v i - v j))) ∂(Measure.pi fun _ => gumbel) =
      ∫⁻ t, g t ∂gumbel := by
    rw [← hU.lintegral_comp hg]
    exact lintegral_congr fun x => by simp only [g, MeasurableEquiv.piUnique_apply]; rfl
  refine (?_ : _ = ∫⁻ t, g t ∂gumbel).trans ?_
  · convert key
  rw [gumbel, lintegral_withDensity_eq_lintegral_mul _
    (f := fun x => ENNReal.ofReal (gumbelPDF x))
    (ENNReal.measurable_ofReal.comp continuous_gumbelPDF.measurable) hg]
  set S := ∑ j, exp (v j - v i)
  have hS : 0 < S := Finset.sum_pos (fun j _ => exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hfun : ∀ t, ((fun x => ENNReal.ofReal (gumbelPDF x)) * g) t =
      ENNReal.ofReal (exp (-t) * exp (-(S * exp (-t)))) := by
    intro t
    simp only [Pi.mul_apply, g]
    rw [← ENNReal.ofReal_prod_of_nonneg (f := fun j : {j // ¬ p j} => gumbelCDF (t + (v i - v j)))
      fun j _ => (exp_pos _).le,
      ← ENNReal.ofReal_mul (gumbelInt_nonneg 1 t |>.trans_eq (gumbelPDF_eq t).symm)]
    congr 1
    exact gumbel_integrand v i t
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gumbelInt hS)
    (ae_of_all _ fun t => gumbelInt_nonneg S t), integral_gumbelInt hS]
  congr 1
  simp only [Logit.softmax, div_one, S]
  have : ∑ j, exp (v j - v i) = (∑ j, exp (v j)) / exp (v i) := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by rw [exp_sub]
  rw [this, one_div_div]

/-- McFadden's theorem for independent Gumbel random variables on any
probability space. -/
theorem gumbel_choice_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ε : ι → Ω → ℝ} (hmeas : ∀ j, Measurable (ε j))
    (hind : ProbabilityTheory.iIndepFun ε P) (hlaw : ∀ j, P.map (ε j) = gumbel)
    (v : ι → ℝ) (i : ι) :
    P {ω | ∀ j, v j + ε j ω ≤ v i + ε i ω} = ENNReal.ofReal (Logit.softmax 1 v i) := by
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (hmeas j).aemeasurable)).1 hind
  simp_rw [hlaw] at hmap
  have hm : Measurable fun ω j => ε j ω := Measurable.of_eval hmeas
  rw [← gumbel_choice v i, ← hmap, Measure.map_apply hm (measurableSet_chooses v i)]
  rfl

/-- The Gumbel choice probabilities sum to one. -/
theorem gumbel_choice_sum [Nonempty ι] (v : ι → ℝ) :
    ∑ i, (Measure.pi fun _ : ι => gumbel) (chooses v i) = 1 := by
  simp_rw [gumbel_choice]
  rw [← ENNReal.ofReal_sum_of_nonneg (f := fun i => Logit.softmax 1 v i) fun i _ =>
    div_nonneg (exp_pos _).le (Finset.sum_nonneg fun j _ => (exp_pos _).le)]
  have hpos : 0 < ∑ j, exp (v j / 1) := Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty
  simp only [Logit.softmax, ← Finset.sum_div, div_self hpos.ne', ENNReal.ofReal_one]

end GumbelLogit

end Econ
