/-
# Partial identification: Manski's worst-case bounds

Manski (1989), "Anatomy of the Selection Problem", *Journal of Human
Resources* 24; Manski (1990), "Nonparametric Bounds on Treatment Effects",
*American Economic Review P&P* 80; Manski, *Partial Identification of
Probability Distributions* (2003), ch. 1–2 and 7.

**The economics.** Without any assumption on how units select into treatment,
the mean of a potential outcome is not point identified, but if outcomes are
bounded it is *partially* identified. With `Y₁ ∈ [lo, hi]` observed only for the
treated (`D = 1`):

`E[Y₁] = E[Y₁ | D=1] P(D=1) + E[Y₁ | D=0] P(D=0)`,

and the unobserved `E[Y₁ | D=0]` can be anything in `[lo, hi]`. Hence

`E[Y₁] ∈ [E[Y 1{D=1}] + lo · P(D=0), E[Y 1{D=1}] + hi · P(D=0)]`

(Manski 1989). The bounds are **sharp**: every point of the interval is the
mean of some potential-outcome variable that agrees with the data and respects
the bounds. The ATE bounds (Manski 1990) always have width `hi − lo`, so with
no assumptions they always contain zero.

We write the identified part as the integral over the treated,
`∫_{D=1} Y₁ = E[Y | D=1] P(D=1)`: it only involves `Y₁` on `{D = 1}`, where it
is observed.
-/
module

public import EconLean.Econometrics.Causal.PotentialOutcomes

@[expose] public section

namespace Econ.Causal

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Manski lower bound on `E[Y₁]` from data on the treated. -/
noncomputable def manskiLower (μ : Measure Ω) (D : Ω → Bool) (Y₁ : Ω → ℝ) (lo : ℝ) : ℝ :=
  (∫ ω in treated D, Y₁ ω ∂μ) + lo * μ.real (untreated D)

/-- Manski upper bound on `E[Y₁]`. -/
noncomputable def manskiUpper (μ : Measure Ω) (D : Ω → Bool) (Y₁ : Ω → ℝ) (hi : ℝ) : ℝ :=
  (∫ ω in treated D, Y₁ ω ∂μ) + hi * μ.real (untreated D)

omit [MeasurableSpace Ω] in
lemma treated_compl (D : Ω → Bool) : (treated D)ᶜ = untreated D := by
  ext ω; simp [treated, untreated]

omit [IsProbabilityMeasure μ] in
/-- Split `E[Y₁]` into the observed and unobserved parts. -/
lemma integral_split {D : Ω → Bool} (hD : Measurable D) {Y : Ω → ℝ} (hY : Integrable Y μ) :
    ∫ ω, Y ω ∂μ = (∫ ω in treated D, Y ω ∂μ) + ∫ ω in untreated D, Y ω ∂μ := by
  rw [← treated_compl, integral_add_compl (measurableSet_treated hD) hY]

/-- **Manski (1989) worst-case bounds.** If `lo ≤ Y₁ ≤ hi`, then
`E[Y₁]` lies between the Manski lower and upper bounds. -/
theorem manski_bounds {D : Ω → Bool} (hD : Measurable D) {Y₁ : Ω → ℝ}
    (hY : Integrable Y₁ μ) {lo hi : ℝ} (hlo : ∀ ω, lo ≤ Y₁ ω) (hhi : ∀ ω, Y₁ ω ≤ hi) :
    manskiLower μ D Y₁ lo ≤ ∫ ω, Y₁ ω ∂μ ∧ ∫ ω, Y₁ ω ∂μ ≤ manskiUpper μ D Y₁ hi := by
  have hs := measurableSet_untreated hD
  rw [integral_split hD hY, manskiLower, manskiUpper]
  constructor
  · have : lo * μ.real (untreated D) ≤ ∫ ω in untreated D, Y₁ ω ∂μ := by
      rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
      exact setIntegral_mono_on (integrableOn_const) hY.integrableOn hs fun ω _ => hlo ω
    linarith
  · have : ∫ ω in untreated D, Y₁ ω ∂μ ≤ hi * μ.real (untreated D) := by
      rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
      exact setIntegral_mono_on hY.integrableOn (integrableOn_const) hs fun ω _ => hhi ω
    linarith

/-- **Sharpness of the Manski bounds.** Every value `v` between the bounds is
`E[Y₁']` for some potential outcome `Y₁'` that (i) respects the bounds,
(ii) coincides with `Y₁` on the treated, where it is observed, and (iii) is
integrable and measurable. So no value inside the interval can be ruled out
by the data and the bound assumption. -/
theorem manski_sharp {D : Ω → Bool} (hD : Measurable D) {Y₁ : Ω → ℝ} (hYm : Measurable Y₁)
    (hY : Integrable Y₁ μ) {lo hi : ℝ} (hlo : ∀ ω, lo ≤ Y₁ ω) (hhi : ∀ ω, Y₁ ω ≤ hi)
    {v : ℝ} (hv₁ : manskiLower μ D Y₁ lo ≤ v) (hv₂ : v ≤ manskiUpper μ D Y₁ hi) :
    ∃ Y₁' : Ω → ℝ, Measurable Y₁' ∧ Integrable Y₁' μ ∧ (∀ ω, lo ≤ Y₁' ω ∧ Y₁' ω ≤ hi) ∧
      (∀ ω ∈ treated D, Y₁' ω = Y₁ ω) ∧ ∫ ω, Y₁' ω ∂μ = v := by
  have hT := measurableSet_treated hD
  set p := μ.real (untreated D) with hp
  set A := ∫ ω in treated D, Y₁ ω ∂μ with hA
  -- Fill in the unobserved outcomes with a constant `k ∈ [lo, hi]`.
  classical
  simp only [manskiLower, manskiUpper] at hv₁ hv₂
  rw [← hp, ← hA] at hv₁ hv₂
  have hp_nonneg : 0 ≤ p := hp ▸ measureReal_nonneg
  clear_value p A
  have hk : ∃ k, lo ≤ k ∧ k ≤ hi ∧ A + k * p = v := by
    rcases hp_nonneg.lt_or_eq with hp0 | hp0
    · refine ⟨(v - A) / p, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ hp0]; linarith
      · rw [div_le_iff₀ hp0]; linarith
      · field_simp; ring
    · rw [← hp0] at hv₁ hv₂ ⊢
      refine ⟨lo, le_rfl, (have := nonempty_of_isProbabilityMeasure μ; (hlo (Classical.arbitrary Ω)).trans (hhi _)), ?_⟩
      linarith
  obtain ⟨k, hk₁, hk₂, hkv⟩ := hk
  refine ⟨(treated D).piecewise Y₁ (fun _ => k), hYm.piecewise hT measurable_const,
    Integrable.piecewise hT.nullMeasurableSet hY.integrableOn (integrable_const k).integrableOn, fun ω => ?_, fun ω h => by simp [h], ?_⟩
  · by_cases h : ω ∈ treated D <;> simp [h, hlo ω, hhi ω, hk₁, hk₂]
  · rw [integral_split hD (Integrable.piecewise hT.nullMeasurableSet hY.integrableOn (integrable_const k).integrableOn),
      setIntegral_congr_fun hT (fun ω h => by simp [h] : Set.EqOn _ Y₁ _),
      setIntegral_congr_fun (measurableSet_untreated hD)
        (fun ω (h : ω ∈ untreated D) => by
          have : ω ∉ treated D := by rw [← treated_compl] at h; exact h
          simp [this] : Set.EqOn _ (fun _ => k) _),
      setIntegral_const, smul_eq_mul, ← hkv, hA, hp, mul_comm]

/-- **Manski (1990) no-assumption ATE bounds.** If both potential outcomes lie in
`[lo, hi]`, `Y₁` is observed on the treated and `Y₀` on the untreated, then the
ATE lies in an interval computed from the data whose width is exactly
`hi − lo`. -/
theorem manski_ate_bounds {D : Ω → Bool} (hD : Measurable D) {Y₀ Y₁ : Ω → ℝ}
    (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ) {lo hi : ℝ}
    (hlo₀ : ∀ ω, lo ≤ Y₀ ω) (hhi₀ : ∀ ω, Y₀ ω ≤ hi)
    (hlo₁ : ∀ ω, lo ≤ Y₁ ω) (hhi₁ : ∀ ω, Y₁ ω ≤ hi) :
    let L := manskiLower μ D Y₁ lo - ((∫ ω in untreated D, Y₀ ω ∂μ) + hi * μ.real (treated D))
    let U := manskiUpper μ D Y₁ hi - ((∫ ω in untreated D, Y₀ ω ∂μ) + lo * μ.real (treated D))
    L ≤ ate μ Y₀ Y₁ ∧ ate μ Y₀ Y₁ ≤ U ∧ U - L = hi - lo := by
  intro L U
  -- Bounds for `E[Y₀]`, with the roles of treated and untreated swapped.
  have hT := measurableSet_treated hD
  have hsplit₀ : ∫ ω, Y₀ ω ∂μ = (∫ ω in untreated D, Y₀ ω ∂μ) + ∫ ω in treated D, Y₀ ω ∂μ := by
    rw [integral_split hD h₀, add_comm]
  have hlo' : lo * μ.real (treated D) ≤ ∫ ω in treated D, Y₀ ω ∂μ := by
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on integrableOn_const h₀.integrableOn hT fun ω _ => hlo₀ ω
  have hhi' : ∫ ω in treated D, Y₀ ω ∂μ ≤ hi * μ.real (treated D) := by
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on h₀.integrableOn integrableOn_const hT fun ω _ => hhi₀ ω
  obtain ⟨b₁, b₂⟩ := manski_bounds hD h₁ hlo₁ hhi₁
  have hsum : μ.real (treated D) + μ.real (untreated D) = 1 := by
    rw [← treated_compl, probReal_compl_eq_one_sub hT]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ate, integral_sub h₁ h₀]; simp only [L]; linarith
  · rw [ate, integral_sub h₁ h₀]; simp only [U]; linarith
  · simp only [L, U, manskiLower, manskiUpper]
    have : (hi - lo) * (μ.real (treated D) + μ.real (untreated D)) = hi - lo := by
      rw [hsum, mul_one]
    linarith

end Econ.Causal
