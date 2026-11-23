/-
# Potential outcomes and randomized experiments

Rubin (1974); Imbens–Rubin, *Causal Inference* (2015), ch. 1–2 and §6;
Angrist–Pischke, *Mostly Harmless Econometrics* (2009), §2.1–2.2.

**The economics.** Each unit `ω` has two potential outcomes, `Y₀ ω` (untreated)
and `Y₁ ω` (treated), and a binary treatment `D ω`. We observe only
`Y = D·Y₁ + (1 − D)·Y₀` (the *switching equation*; writing it this way is the
SUTVA / no-interference assumption: a unit's outcome depends only on its own
treatment). The average treatment effect is `ATE = E[Y₁ − Y₀]`; the effect on
the treated is `ATT = E[Y₁ − Y₀ | D = 1]`.

* **Selection-bias decomposition** (Angrist–Pischke eq. 2.2.1): the naive
  comparison of means is the ATT plus selection bias:
  `E[Y | D=1] − E[Y | D=0] = ATT + (E[Y₀ | D=1] − E[Y₀ | D=0])`.
* **Randomization identifies the ATE** (Imbens–Rubin Thm 6.1 / §6.4): if `D` is
  independent of `(Y₀, Y₁)` and `0 < P(D=1) < 1`, then the difference in means
  equals the ATE, and also equals the ATT.

Independence is the canonical assumption `(Y₀, Y₁) ⫫ D`, stated with Mathlib's
`IndepFun` for the pair `ω ↦ (Y₀ ω, Y₁ ω)`.
-/
module

public import EconLean.Econometrics.Causal.Basic

@[expose] public section

namespace Econ.Causal

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The observed outcome given treatment `D` and potential outcomes `Y₀, Y₁`
(switching equation / SUTVA). -/
def observed (D : Ω → Bool) (Y₀ Y₁ : Ω → ℝ) (ω : Ω) : ℝ := if D ω then Y₁ ω else Y₀ ω

/-- The event "treated". -/
def treated (D : Ω → Bool) : Set Ω := {ω | D ω = true}

/-- The event "untreated". -/
def untreated (D : Ω → Bool) : Set Ω := {ω | D ω = false}

lemma measurableSet_treated {D : Ω → Bool} (hD : Measurable D) : MeasurableSet (treated D) :=
  hD (measurableSet_singleton true)

lemma measurableSet_untreated {D : Ω → Bool} (hD : Measurable D) :
    MeasurableSet (untreated D) :=
  hD (measurableSet_singleton false)

/-- Average treatment effect `E[Y₁ − Y₀]`. -/
noncomputable def ate (μ : Measure Ω) (Y₀ Y₁ : Ω → ℝ) : ℝ := ∫ ω, (Y₁ ω - Y₀ ω) ∂μ

/-- Average treatment effect on the treated `E[Y₁ − Y₀ | D = 1]`. -/
noncomputable def att (μ : Measure Ω) (D : Ω → Bool) (Y₀ Y₁ : Ω → ℝ) : ℝ :=
  condMean μ (fun ω => Y₁ ω - Y₀ ω) (treated D)

/-- The observed difference in means `E[Y | D=1] − E[Y | D=0]`. -/
noncomputable def diffInMeans (μ : Measure Ω) (D : Ω → Bool) (Y₀ Y₁ : Ω → ℝ) : ℝ :=
  condMean μ (observed D Y₀ Y₁) (treated D) - condMean μ (observed D Y₀ Y₁) (untreated D)

lemma condMean_observed_treated {D : Ω → Bool} (hD : Measurable D) (Y₀ Y₁ : Ω → ℝ) :
    condMean μ (observed D Y₀ Y₁) (treated D) = condMean μ Y₁ (treated D) :=
  condMean_congr (measurableSet_treated hD) fun ω h => by simp [observed, show D ω = true from h]

lemma condMean_observed_untreated {D : Ω → Bool} (hD : Measurable D) (Y₀ Y₁ : Ω → ℝ) :
    condMean μ (observed D Y₀ Y₁) (untreated D) = condMean μ Y₀ (untreated D) :=
  condMean_congr (measurableSet_untreated hD) fun ω h => by
    simp [observed, show D ω = false from h]

/-- **Selection-bias decomposition** (Angrist–Pischke eq. 2.2.1). The observed
difference in means equals the ATT plus the selection bias
`E[Y₀ | D=1] − E[Y₀ | D=0]`. No assumption beyond integrability. -/
theorem diffInMeans_eq_att_add_selectionBias {D : Ω → Bool} (hD : Measurable D)
    {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ) :
    diffInMeans μ D Y₀ Y₁
      = att μ D Y₀ Y₁ + (condMean μ Y₀ (treated D) - condMean μ Y₀ (untreated D)) := by
  rw [diffInMeans, att, condMean_observed_treated hD, condMean_observed_untreated hD,
    condMean_sub _ h₁ h₀]
  ring

/-- Under random assignment the conditional mean of any integrable function of
the potential outcomes equals its unconditional mean. -/
lemma condMean_of_randomized [IsProbabilityMeasure μ] {D : Ω → Bool} (hD : Measurable D)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hind : IndepFun (fun ω => (Y₀ ω, Y₁ ω)) D μ) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    {b : Bool} (hb : μ.real {ω | D ω = b} ≠ 0) :
    condMean μ (fun ω => g (Y₀ ω, Y₁ ω)) {ω | D ω = b} = ∫ ω, g (Y₀ ω, Y₁ ω) ∂μ := by
  have hi : IndepFun (fun ω => g (Y₀ ω, Y₁ ω)) D μ := by
    simpa [Function.comp_def] using hind.comp (φ := g) (ψ := id) hg measurable_id
  exact condMean_eq_integral_of_indepFun hi
    ((hg.comp (hY₀.prodMk hY₁)).aestronglyMeasurable) hD hb

/-- **Randomization identifies the ATE** (Imbens–Rubin §6.4; Angrist–Pischke
§2.2). If treatment is independent of the potential outcomes and both arms have
positive probability, the difference in means equals the ATE. -/
theorem diffInMeans_eq_ate [IsProbabilityMeasure μ] {D : Ω → Bool} (hD : Measurable D)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ)
    (hind : IndepFun (fun ω => (Y₀ ω, Y₁ ω)) D μ)
    (hp₁ : 0 < μ.real (treated D)) (hp₀ : 0 < μ.real (untreated D)) :
    diffInMeans μ D Y₀ Y₁ = ate μ Y₀ Y₁ := by
  rw [diffInMeans, condMean_observed_treated hD, condMean_observed_untreated hD, ate,
    integral_sub h₁ h₀]
  have e₁ := condMean_of_randomized hD hY₀ hY₁ hind (g := Prod.snd) measurable_snd
    (b := true) hp₁.ne'
  have e₀ := condMean_of_randomized hD hY₀ hY₁ hind (g := Prod.fst) measurable_fst
    (b := false) hp₀.ne'
  simp only at e₁ e₀
  rw [treated, untreated, e₁, e₀]

/-- Under randomization the ATT equals the ATE (there is no selection on gains).
No integrability is assumed: if `Y₁ − Y₀` is not integrable both sides are
Lean's junk value `0`. -/
theorem att_eq_ate [IsProbabilityMeasure μ] {D : Ω → Bool} (hD : Measurable D)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hind : IndepFun (fun ω => (Y₀ ω, Y₁ ω)) D μ) (hp₁ : 0 < μ.real (treated D)) :
    att μ D Y₀ Y₁ = ate μ Y₀ Y₁ := by
  have := condMean_of_randomized hD hY₀ hY₁ hind (g := fun p => p.2 - p.1)
    (measurable_snd.sub measurable_fst) (b := true) hp₁.ne'
  simpa [att, ate, treated] using this

end Econ.Causal
