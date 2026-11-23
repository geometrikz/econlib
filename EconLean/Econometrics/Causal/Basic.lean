/-
# Conditional means on events, and independence

Shared toolkit for the population-level identification results in
`Econometrics/Causal/`. Imbens–Rubin, *Causal Inference* (2015), ch. 1–3;
Angrist–Pischke, *Mostly Harmless Econometrics* (2009), ch. 2.

**The economics.** Identification arguments compare averages in subgroups:
"mean outcome among the treated", "mean outcome when the instrument is on".
For a binary (or discrete) conditioning variable these are elementary
conditional means `E[Y | A] = E[Y 1_A] / P(A)`, defined whenever `P(A) > 0`.
This avoids the a.e.-defined conditional-expectation operator, which is not
needed when we only ever condition on events of positive probability.

**The workhorse lemma** (`condMean_eq_integral_of_indepFun`): if `F` is
independent of a Bool-valued `Z` (random assignment), then the mean of `F` among
`Z = b` equals its unconditional mean. Random assignment, the IV independence
assumption and unconfoundedness all enter through this lemma.

**Lean encoding.** A probability space is `(Ω, μ)` with
`[IsProbabilityMeasure μ]`; random variables are functions `Ω → ℝ`; binary
variables (treatment, instrument, group) are `Ω → Bool`. `μ.real s` is the
probability of `s` as a real number.

**Junk-value warning.** `condMean μ Y s` is `(μ.real s)⁻¹ * ∫_s Y`, and Lean sets
`0⁻¹ = 0`, so on a null event it is `0`. Every theorem that interprets a
`condMean` as a conditional mean assumes the event has positive probability.
-/
module

public import Mathlib.Probability.Independence.Integration

@[expose] public section

namespace Econ.Causal

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real indicator of a Boolean: `1` if true, `0` if false. Turns a binary
treatment `D` into the regressor `1{D = 1}`. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

@[simp] lemma ind_true : ind true = 1 := rfl
@[simp] lemma ind_false : ind false = 0 := rfl

lemma measurable_ind : Measurable ind := measurable_from_top

/-- Conditional mean of `Y` on the event `s`: `E[Y | s] = E[Y 1_s] / P(s)`.
Meaningful only when `P(s) > 0` (see the junk-value warning). -/
noncomputable def condMean (μ : Measure Ω) (Y : Ω → ℝ) (s : Set Ω) : ℝ :=
  (μ.real s)⁻¹ * ∫ ω in s, Y ω ∂μ

variable {μ : Measure Ω}

/-- `E[Y | s] · P(s) = E[Y 1_s]` when `P(s) > 0`. -/
lemma condMean_mul_measureReal {Y : Ω → ℝ} {s : Set Ω} (hs : μ.real s ≠ 0) :
    condMean μ Y s * μ.real s = ∫ ω in s, Y ω ∂μ := by
  rw [condMean, mul_comm, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- Conditional means are additive (for integrable variables). -/
lemma condMean_add {Y₁ Y₂ : Ω → ℝ} (s : Set Ω) (h₁ : Integrable Y₁ μ) (h₂ : Integrable Y₂ μ) :
    condMean μ (fun ω => Y₁ ω + Y₂ ω) s = condMean μ Y₁ s + condMean μ Y₂ s := by
  unfold condMean
  rw [integral_add h₁.integrableOn h₂.integrableOn, mul_add]

/-- Conditional means are subtractive (for integrable variables). -/
lemma condMean_sub {Y₁ Y₂ : Ω → ℝ} (s : Set Ω) (h₁ : Integrable Y₁ μ) (h₂ : Integrable Y₂ μ) :
    condMean μ (fun ω => Y₁ ω - Y₂ ω) s = condMean μ Y₁ s - condMean μ Y₂ s := by
  unfold condMean
  rw [integral_sub h₁.integrableOn h₂.integrableOn, mul_sub]

/-- Conditional means only depend on the variable on the event itself. -/
lemma condMean_congr {Y₁ Y₂ : Ω → ℝ} {s : Set Ω} (hs : MeasurableSet s)
    (h : ∀ ω ∈ s, Y₁ ω = Y₂ ω) : condMean μ Y₁ s = condMean μ Y₂ s := by
  unfold condMean
  rw [setIntegral_congr_fun hs h]

/-- The conditional mean of a constant is that constant (on a non-null event). -/
lemma condMean_const (c : ℝ) {s : Set Ω} (hs : μ.real s ≠ 0) :
    condMean μ (fun _ => c) s = c := by
  rw [condMean, setIntegral_const, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- The conditional mean of an indicator `1{D}` on `s` is the conditional
probability of `{D}` given `s`. -/
lemma condMean_ind {D : Ω → Bool} (hD : Measurable D) (s : Set Ω) :
    condMean μ (fun ω => ind (D ω)) s = (μ.real s)⁻¹ * μ.real (s ∩ {ω | D ω = true}) := by
  unfold condMean
  congr 1
  have hmeas : MeasurableSet {ω | D ω = true} := hD (measurableSet_singleton true)
  have : (fun ω => ind (D ω)) = Set.indicator {ω | D ω = true} (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : D ω = true <;> simp [ind, h, Set.indicator]
  rw [this, integral_indicator hmeas, Measure.restrict_restrict hmeas, setIntegral_const,
    smul_eq_mul, mul_one, Set.inter_comm]

/-- The mean of `1{D}` is `P(D)`. -/
lemma integral_ind [IsProbabilityMeasure μ] {D : Ω → Bool} (hD : Measurable D) :
    ∫ ω, ind (D ω) ∂μ = μ.real {ω | D ω = true} := by
  have hmeas : MeasurableSet {ω | D ω = true} := hD (measurableSet_singleton true)
  have : (fun ω => ind (D ω)) = Set.indicator {ω | D ω = true} (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : D ω = true <;> simp [ind, h, Set.indicator]
  rw [this, integral_indicator hmeas, setIntegral_const, smul_eq_mul, mul_one]

/-- `ind (D ω)` is integrable on a probability space. -/
lemma integrable_ind [IsFiniteMeasure μ] {D : Ω → Bool} (hD : Measurable D) :
    Integrable (fun ω => ind (D ω)) μ := by
  refine Integrable.of_bound (C := 1) (measurable_ind.comp hD).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by cases D ω <;> simp [ind]

/-- The integral of `F` over the event `{Z = b}` factorises when `F` is
independent of `Z`: `E[F 1{Z = b}] = P(Z = b) E[F]`. -/
lemma setIntegral_eq_of_indepFun [IsProbabilityMeasure μ] {F : Ω → ℝ} {Z : Ω → Bool}
    (hFZ : IndepFun F Z μ) (hF : AEStronglyMeasurable F μ) (hZ : Measurable Z) (b : Bool) :
    ∫ ω in {ω | Z ω = b}, F ω ∂μ = μ.real {ω | Z ω = b} * ∫ ω, F ω ∂μ := by
  have hmeas : MeasurableSet {ω | Z ω = b} := hZ (measurableSet_singleton b)
  -- `φ` is the real indicator of `{b}`; any function out of `Bool` is measurable.
  set φ : Bool → ℝ := fun b' => if b' = b then 1 else 0 with hφ
  have hφm : Measurable φ := measurable_from_top
  have hind : IndepFun F (φ ∘ Z) μ := by
    simpa using hFZ.comp (φ := id) (ψ := φ) measurable_id hφm
  have hprod : ∫ ω in {ω | Z ω = b}, F ω ∂μ = ∫ ω, (φ ∘ Z) ω * F ω ∂μ := by
    rw [← integral_indicator hmeas]
    congr 1
    funext ω
    by_cases h : Z ω = b <;> simp [Set.indicator, hφ, h]
  rw [hprod, (hind.symm).integral_fun_mul_eq_mul_integral
    (hφm.comp hZ).aestronglyMeasurable hF]
  congr 1
  have : (φ ∘ Z) = Set.indicator {ω | Z ω = b} (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : Z ω = b <;> simp [Set.indicator, hφ, h]
  rw [this, integral_indicator hmeas, setIntegral_const, smul_eq_mul, mul_one]

/-- **Independence removes conditioning.** If `F` is independent of the binary
`Z` and `P(Z = b) > 0`, then `E[F | Z = b] = E[F]`. -/
theorem condMean_eq_integral_of_indepFun [IsProbabilityMeasure μ] {F : Ω → ℝ} {Z : Ω → Bool}
    (hFZ : IndepFun F Z μ) (hF : AEStronglyMeasurable F μ) (hZ : Measurable Z) {b : Bool}
    (hb : μ.real {ω | Z ω = b} ≠ 0) :
    condMean μ F {ω | Z ω = b} = ∫ ω, F ω ∂μ := by
  rw [condMean, setIntegral_eq_of_indepFun hFZ hF hZ b, ← mul_assoc, inv_mul_cancel₀ hb,
    one_mul]

end Econ.Causal
