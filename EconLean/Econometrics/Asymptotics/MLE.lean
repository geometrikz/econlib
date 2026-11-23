/-
# Maximum likelihood with densities: the Kullback–Leibler gap

Newey and McFadden (1994), Lemma 2.2 and Thm 2.5; van der Vaart (1998), §5.5;
Hayashi (2000), Prop. 7.5.

**The result.** Let the model have densities `f_θ > 0` with respect to a
σ-finite measure `ν`, so `P_θ = f_θ · ν`. Then
`E_{θ₀}[log f_θ₀ − log f_θ] = KL(P_θ₀ ‖ P_θ)` (`integral_log_sub_eq_klDiv`), and
the divergence is finite when the log-densities are integrable. Hence the
expected log-likelihood `Q₀(θ) = E_{θ₀}[log f_θ]` satisfies the identity that
`Extremum.mle_unique_max` takes as a hypothesis, and in an identified model it
is uniquely maximised at `θ₀` (`expectedLogLik_unique_max`). With a uniform law
of large numbers for the average log-likelihood this gives consistency of the
MLE (`mle_consistent_of_density`).

**Encoding.** `f θ x` is real and positive; the measure is
`ν.withDensity (ofReal ∘ f θ)`, assumed a probability measure for each `θ`.
-/
module

public import EconLean.Econometrics.Asymptotics.Extremum
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {ν : Measure α} [SigmaFinite ν]

/-- The model measure with real density `f`. -/
noncomputable def densityMeasure (ν : Measure α) (f : α → ℝ) : Measure α :=
  ν.withDensity fun x => ENNReal.ofReal (f x)

/-- **Log-likelihood ratio of two density models**: `log(dP₀/dP₁) = log f₀ − log f₁`,
`P₀`-almost everywhere. -/
theorem llr_densityMeasure {f₀ f₁ : α → ℝ} (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hpos₀ : ∀ x, 0 < f₀ x) (hpos₁ : ∀ x, 0 < f₁ x) :
    llr (densityMeasure ν f₀) (densityMeasure ν f₁)
      =ᵐ[densityMeasure ν f₀] fun x => Real.log (f₀ x) - Real.log (f₁ x) := by
  set g₀ : α → ENNReal := fun x => ENNReal.ofReal (f₀ x)
  set g₁ : α → ENNReal := fun x => ENNReal.ofReal (f₁ x)
  have hg₀ : Measurable g₀ := ENNReal.measurable_ofReal.comp hf₀
  have hg₁ : Measurable g₁ := ENNReal.measurable_ofReal.comp hf₁
  have hσ : SigmaFinite (ν.withDensity g₀) :=
    SigmaFinite.withDensity_of_ne_top (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have h1 := Measure.rnDeriv_withDensity_right (ν.withDensity g₀) ν hg₁.aemeasurable
    (Eventually.of_forall fun x => by simp [g₁, hpos₁ x])
    (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have h2 := Measure.rnDeriv_withDensity ν hg₀
  have h3 : (ν.withDensity g₀).rnDeriv (ν.withDensity g₁) =ᵐ[ν] fun x => (g₁ x)⁻¹ * g₀ x := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have h4 := (withDensity_absolutelyContinuous ν g₀).ae_le h3
  unfold densityMeasure
  filter_upwards [h4] with x hx
  rw [llr_def]
  simp only
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hpos₁ x).le,
    ENNReal.toReal_ofReal (hpos₀ x).le, Real.log_mul (inv_ne_zero (hpos₁ x).ne') (hpos₀ x).ne',
    Real.log_inv]
  ring

omit [SigmaFinite ν] in
/-- `P₀ ≪ P₁` for density models with positive densities. -/
lemma densityMeasure_ac {f₀ f₁ : α → ℝ} (hf₁ : Measurable f₁) (hpos₁ : ∀ x, 0 < f₁ x) :
    densityMeasure ν f₀ ≪ densityMeasure ν f₁ :=
  (withDensity_absolutelyContinuous ν _).trans
    (withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hf₁).aemeasurable
      (Eventually.of_forall fun x => by simp [hpos₁ x]))

/-- **The Kullback–Leibler gap of the expected log-likelihood**: for probability
density models with integrable log-densities,
`E_{P₀}[log f₀] − E_{P₀}[log f₁] = KL(P₀ ‖ P₁)`, and the divergence is finite. -/
theorem integral_log_sub_eq_klDiv {f₀ f₁ : α → ℝ} (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hpos₀ : ∀ x, 0 < f₀ x) (hpos₁ : ∀ x, 0 < f₁ x)
    [IsProbabilityMeasure (densityMeasure ν f₀)] [IsProbabilityMeasure (densityMeasure ν f₁)]
    (hi₀ : Integrable (fun x => Real.log (f₀ x)) (densityMeasure ν f₀))
    (hi₁ : Integrable (fun x => Real.log (f₁ x)) (densityMeasure ν f₀)) :
    ∫ x, Real.log (f₀ x) ∂(densityMeasure ν f₀) - ∫ x, Real.log (f₁ x) ∂(densityMeasure ν f₀)
        = (klDiv (densityMeasure ν f₀) (densityMeasure ν f₁)).toReal ∧
      klDiv (densityMeasure ν f₀) (densityMeasure ν f₁) ≠ ⊤ := by
  have hllr := llr_densityMeasure (ν := ν) hf₀ hf₁ hpos₀ hpos₁
  have hac := densityMeasure_ac (ν := ν) (f₀ := f₀) hf₁ hpos₁
  have hint : Integrable (llr (densityMeasure ν f₀) (densityMeasure ν f₁)) (densityMeasure ν f₀) :=
    (hi₀.sub hi₁).congr hllr.symm
  refine ⟨?_, klDiv_ne_top hac hint⟩
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_congr_ae hllr, integral_sub hi₀ hi₁]

/-- The expected log-likelihood `Q₀(θ) = E_{θ₀}[log f_θ]`. -/
noncomputable def expectedLogLik {Θ : Type*} (ν : Measure α) (f : Θ → α → ℝ) (θ₀ θ : Θ) : ℝ :=
  ∫ x, Real.log (f θ x) ∂(densityMeasure ν (f θ₀))

/-- **The expected log-likelihood is uniquely maximised at the truth** (Newey–
McFadden Lemma 2.2) in an identified density model with integrable log-densities. -/
theorem expectedLogLik_unique_max {Θ : Type*} {f : Θ → α → ℝ} (hf : ∀ θ, Measurable (f θ))
    (hpos : ∀ θ x, 0 < f θ x) [hprob : ∀ θ, IsProbabilityMeasure (densityMeasure ν (f θ))]
    (hinj : Function.Injective fun θ => densityMeasure ν (f θ)) {θ₀ : Θ}
    (hint : ∀ θ, Integrable (fun x => Real.log (f θ x)) (densityMeasure ν (f θ₀))) :
    ∀ θ, θ ≠ θ₀ → expectedLogLik ν f θ₀ θ < expectedLogLik ν f θ₀ θ₀ := by
  have hgap := fun θ => integral_log_sub_eq_klDiv (ν := ν) (hf θ₀) (hf θ) (hpos θ₀) (hpos θ)
    (hint θ₀) (hint θ)
  exact mle_unique_max (Pθ := fun θ => densityMeasure ν (f θ)) hinj
    (Q₀ := expectedLogLik ν f θ₀) (fun θ => (hgap θ).1) (fun θ => (hgap θ).2)

/-- **Consistency of the MLE for density models** (Newey–McFadden Thm 2.5): compact
parameter space, identified model with positive densities and integrable
log-densities, continuous expected log-likelihood, and a uniform law of large
numbers for the sample criterion `Qₙ` (for the MLE, the average log-likelihood
`n⁻¹ Σ log f_θ(Xᵢ)`), maximised up to `rₙ →p 0`. The sample criterion is abstract: the uniform law and
continuity of `Q₀` are hypotheses, not derived from i.i.d. sampling and a
dominance condition. -/
theorem mle_consistent_of_density {Ω Θ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [MetricSpace Θ] [CompactSpace Θ] {f : Θ → α → ℝ} (hf : ∀ θ, Measurable (f θ))
    (hpos : ∀ θ x, 0 < f θ x) [∀ θ, IsProbabilityMeasure (densityMeasure ν (f θ))]
    (hinj : Function.Injective fun θ => densityMeasure ν (f θ)) {θ₀ : Θ}
    (hint : ∀ θ, Integrable (fun x => Real.log (f θ x)) (densityMeasure ν (f θ₀)))
    (hcont : Continuous (expectedLogLik ν f θ₀))
    {Q : ℕ → Ω → Θ → ℝ} {θhat : ℕ → Ω → Θ} {r : ℕ → Ω → ℝ}
    (hmax : ∀ n ω θ, Q n ω θ ≤ Q n ω (θhat n ω) + r n ω)
    (hr : TendstoInMeasure P r atTop (fun _ => 0))
    (hulln : ∀ δ > 0, Tendsto (fun n => P {ω | ∃ θ, δ ≤ |Q n ω θ - expectedLogLik ν f θ₀ θ|})
      atTop (𝓝 0)) :
    TendstoInMeasure P θhat atTop (fun _ => θ₀) :=
  extremum_consistent hcont (expectedLogLik_unique_max hf hpos hinj hint) hmax hr hulln

end Econ.Asymptotics
