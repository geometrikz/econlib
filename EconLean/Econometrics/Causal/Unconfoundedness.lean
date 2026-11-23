/-
# Selection on observables: unconfoundedness, adjustment and IPW

Rosenbaum–Rubin (1983), "The central role of the propensity score in
observational studies for causal effects", *Biometrika* 70; Imbens (2004),
"Nonparametric estimation of average treatment effects under exogeneity",
*Review of Economics and Statistics* 86, §2; Imbens–Rubin (2015) ch. 12;
Horvitz–Thompson (1952) for inverse probability weighting.

**The economics.** Treatment `D` is not randomized, but it is "as good as
random" once we condition on observed covariates `X` (unconfoundedness), and
every covariate cell contains both treated and untreated units (overlap). Then

* **Adjustment formula**: `ATE = Σ_x P(X=x) (E[Y | D=1, X=x] − E[Y | D=0, X=x])`;
* **IPW identity**: `E[Y₁] = E[D Y / e(X)]` and `E[Y₀] = E[(1−D) Y / (1−e(X))]`,
  where `e(x) = P(D=1 | X=x)` is the propensity score.

**Encoding.** Covariates take finitely many values (`X : Ω → κ`, `κ` a finite
type with measurable singletons), so conditioning on `X = x` is conditioning on
an event. Rosenbaum–Rubin assume full conditional independence
`(Y₀, Y₁) ⫫ D | X`; we assume only **conditional mean independence**,
`E[Y_d | D=d', X=x] = E[Y_d | X=x]` (Imbens 2004, Assumption 2.1 discussion),
which is implied by it. Weaker hypothesis, stronger theorem.

**Overlap**: for every covariate value with positive probability, both
treatment arms have positive probability (Imbens 2004, Assumption 2.2).
-/
module

public import EconLean.Econometrics.Causal.PotentialOutcomes

@[expose] public section

namespace Econ.Causal

open MeasureTheory

variable {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

/-- The stratum `{X = x}`. -/
def stratum (X : Ω → κ) (x : κ) : Set Ω := {ω | X ω = x}

/-- The cell `{X = x, D = b}`. -/
def cell (X : Ω → κ) (D : Ω → Bool) (x : κ) (b : Bool) : Set Ω := {ω | X ω = x ∧ D ω = b}

/-- The probability of arm `b` given `X = x`, `P(D = b | X = x)`. For `b = true`
this is the propensity score `e(x)`, for `b = false` it is `1 − e(x)`. -/
noncomputable def armProb (μ : Measure Ω) (X : Ω → κ) (D : Ω → Bool) (x : κ) (b : Bool) : ℝ :=
  μ.real (cell X D x b) / μ.real (stratum X x)

/-- The propensity score `e(x) = P(D = 1 | X = x)`. -/
noncomputable def propensity (μ : Measure Ω) (X : Ω → κ) (D : Ω → Bool) (x : κ) : ℝ :=
  armProb μ X D x true

/-- Overlap: in every stratum of positive probability both arms have positive
probability. -/
def Overlap (μ : Measure Ω) (X : Ω → κ) (D : Ω → Bool) : Prop :=
  ∀ x b, μ.real (stratum X x) ≠ 0 → 0 < μ.real (cell X D x b)

/-- Conditional mean independence (unconfoundedness in mean):
`E[Y_d | D = b, X = x] = E[Y_d | X = x]` for both potential outcomes, on every
cell of positive probability (on a null cell the left side is undefined). -/
def MeanUnconfounded (μ : Measure Ω) (X : Ω → κ) (D : Ω → Bool) (Y₀ Y₁ : Ω → ℝ) : Prop :=
  ∀ x b, μ.real (cell X D x b) ≠ 0 →
    condMean μ Y₀ (cell X D x b) = condMean μ Y₀ (stratum X x) ∧
      condMean μ Y₁ (cell X D x b) = condMean μ Y₁ (stratum X x)

omit [Fintype κ] in
lemma measurableSet_stratum {X : Ω → κ} (hX : Measurable X) (x : κ) :
    MeasurableSet (stratum X x) :=
  hX (measurableSet_singleton x)

omit [Fintype κ] in
lemma measurableSet_cell {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X) (hD : Measurable D)
    (x : κ) (b : Bool) : MeasurableSet (cell X D x b) :=
  (hX (measurableSet_singleton x)).inter (hD (measurableSet_singleton b))

/-- A set integral over a null set vanishes. -/
lemma setIntegral_eq_zero_of_measureReal_eq_zero [IsFiniteMeasure μ] {s : Set Ω}
    (hs : μ.real s = 0) (Y : Ω → ℝ) : ∫ ω in s, Y ω ∂μ = 0 := by
  have : μ s = 0 := (measureReal_eq_zero_iff (measure_ne_top μ s)).mp hs
  rw [Measure.restrict_eq_zero.mpr this, integral_zero_measure]

/-- `∫_s Y = P(s) E[Y | s]`, also when `P(s) = 0`. -/
lemma setIntegral_eq_mul_condMean [IsFiniteMeasure μ] (s : Set Ω) (Y : Ω → ℝ) :
    ∫ ω in s, Y ω ∂μ = μ.real s * condMean μ Y s := by
  by_cases hs : μ.real s = 0
  · rw [setIntegral_eq_zero_of_measureReal_eq_zero hs, hs, zero_mul]
  · rw [mul_comm, condMean_mul_measureReal hs]

/-- Law of total expectation over a finite partition by `X`. -/
lemma integral_eq_sum_stratum {X : Ω → κ} (hX : Measurable X) {Y : Ω → ℝ}
    (hY : Integrable Y μ) : ∫ ω, Y ω ∂μ = ∑ x, ∫ ω in stratum X x, Y ω ∂μ := by
  classical
  have hsum : (fun ω => Y ω) = fun ω => ∑ x, (stratum X x).indicator Y ω := by
    funext ω
    rw [Finset.sum_eq_single (X ω)]
    · simp [stratum, Set.indicator]
    · intro x _ hx; simp [stratum, Set.indicator, Ne.symm hx]
    · simp
  conv_lhs => rw [hsum]
  rw [integral_finsetSum _ fun x _ => (hY.indicator (measurableSet_stratum hX x))]
  exact Finset.sum_congr rfl fun x _ => integral_indicator (measurableSet_stratum hX x)

omit [Fintype κ] in
/-- On the cell `{X = x, D = 1}` the observed outcome is `Y₁`. -/
lemma condMean_observed_cell {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X)
    (hD : Measurable D) (Y₀ Y₁ : Ω → ℝ) (x : κ) (b : Bool) :
    condMean μ (observed D Y₀ Y₁) (cell X D x b) = condMean μ (if b then Y₁ else Y₀) (cell X D x b) :=
  condMean_congr (measurableSet_cell hX hD x b) fun ω h => by
    obtain ⟨_, h⟩ := h
    cases b <;> simp [observed, h]

omit [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- Unconfoundedness for the potential outcome of arm `b`, on cell `(x, b)`. -/
lemma MeanUnconfounded.arm {X : Ω → κ} {D : Ω → Bool} {Y₀ Y₁ : Ω → ℝ}
    (hunc : MeanUnconfounded μ X D Y₀ Y₁) {x : κ} {b : Bool} (h : μ.real (cell X D x b) ≠ 0) :
    condMean μ (if b then Y₁ else Y₀) (cell X D x b)
      = condMean μ (if b then Y₁ else Y₀) (stratum X x) := by
  cases b
  · exact (hunc x false h).1
  · exact (hunc x true h).2

/-- `E[Y_b] = Σ_x P(X=x) E[Y | D=b, X=x]` under unconfoundedness and overlap. -/
theorem integral_potential_eq_adjustment [IsFiniteMeasure μ] {X : Ω → κ} {D : Ω → Bool}
    (hX : Measurable X) (hD : Measurable D) {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ)
    (h₁ : Integrable Y₁ μ) (hunc : MeanUnconfounded μ X D Y₀ Y₁) (hov : Overlap μ X D)
    (b : Bool) :
    ∫ ω, (if b then Y₁ else Y₀) ω ∂μ
      = ∑ x, μ.real (stratum X x) * condMean μ (observed D Y₀ Y₁) (cell X D x b) := by
  have hYb : Integrable (if b then Y₁ else Y₀) μ := by cases b <;> simpa
  rw [integral_eq_sum_stratum hX hYb]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [setIntegral_eq_mul_condMean, condMean_observed_cell hX hD]
  by_cases hs : μ.real (stratum X x) = 0
  · rw [hs, zero_mul, zero_mul]
  · rw [hunc.arm (hov x b hs).ne']

/-- **Adjustment formula** (Imbens 2004, eq. (2); Imbens–Rubin ch. 12). Under
unconfoundedness (in mean) and overlap, the ATE is the covariate-weighted
average of within-stratum differences in observed means. -/
theorem ate_eq_adjustment [IsFiniteMeasure μ] {X : Ω → κ} {D : Ω → Bool}
    (hX : Measurable X) (hD : Measurable D) {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ)
    (h₁ : Integrable Y₁ μ) (hunc : MeanUnconfounded μ X D Y₀ Y₁) (hov : Overlap μ X D) :
    ate μ Y₀ Y₁ = ∑ x, μ.real (stratum X x) *
      (condMean μ (observed D Y₀ Y₁) (cell X D x true)
        - condMean μ (observed D Y₀ Y₁) (cell X D x false)) := by
  have e₁ := integral_potential_eq_adjustment hX hD h₀ h₁ hunc hov true
  have e₀ := integral_potential_eq_adjustment hX hD h₀ h₁ hunc hov false
  simp only [ite_true, Bool.false_eq_true, ite_false] at e₁ e₀
  rw [ate, integral_sub h₁ h₀, e₁, e₀, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Inverse probability weighting** (Horvitz–Thompson; Rosenbaum–Rubin 1983;
Imbens 2004 §III.C). Under unconfoundedness (in mean) and overlap, weighting the
observed outcomes of arm `b` by the inverse of `P(D = b | X)` recovers the mean
potential outcome of that arm: `E[1{D=b} Y / P(D=b | X)] = E[Y_b]`. For
`b = true` this is `E[D Y / e(X)] = E[Y₁]`; for `b = false` it is
`E[(1−D) Y / (1−e(X))] = E[Y₀]`. -/
theorem ipw [IsFiniteMeasure μ] {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X)
    (hD : Measurable D) {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ)
    (hunc : MeanUnconfounded μ X D Y₀ Y₁) (hov : Overlap μ X D) (b : Bool) :
    ∫ ω, (if D ω = b then observed D Y₀ Y₁ ω / armProb μ X D (X ω) b else 0) ∂μ
      = ∫ ω, (if b then Y₁ else Y₀) ω ∂μ := by
  have hYb : Integrable (if b then Y₁ else Y₀) μ := by cases b <;> simpa
  -- The IPW integrand is `Σ_x 1{X = x, D = b} Y_b / P(D = b | X = x)`.
  have hfeq : (fun ω => if D ω = b then observed D Y₀ Y₁ ω / armProb μ X D (X ω) b else 0)
      = fun ω => ∑ x, (cell X D x b).indicator
          (fun ω => (if b then Y₁ else Y₀) ω / armProb μ X D x b) ω := by
    classical
    funext ω
    rw [Finset.sum_eq_single (X ω)]
    · by_cases hd : D ω = b
      · subst hd
        simp [cell, Set.indicator, observed, ite_apply]
      · simp [cell, Set.indicator, hd]
    · intro x _ hx; simp [cell, Set.indicator, Ne.symm hx]
    · simp
  rw [hfeq, integral_finsetSum _ fun x _ =>
      (hYb.div_const _).indicator (measurableSet_cell hX hD x b),
    integral_eq_sum_stratum hX hYb]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_indicator (measurableSet_cell hX hD x b)]
  simp only [div_eq_mul_inv]
  rw [integral_mul_const, setIntegral_eq_mul_condMean, setIntegral_eq_mul_condMean]
  by_cases hs : μ.real (stratum X x) = 0
  · have hc : μ.real (cell X D x b) = 0 := by
      refine le_antisymm ?_ measureReal_nonneg
      rw [← hs]
      exact measureReal_mono fun ω h => h.1
    rw [hs, hc]; ring
  · have hc := hov x b hs
    rw [hunc.arm hc.ne', armProb]
    field_simp

/-- **IPW for the ATE**: `ATE = E[D Y / e(X)] − E[(1−D) Y / (1−e(X))]`, written with
`P(D = b | X)` for the two arms. -/
theorem ate_eq_ipw [IsFiniteMeasure μ] {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X)
    (hD : Measurable D) {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ)
    (hunc : MeanUnconfounded μ X D Y₀ Y₁) (hov : Overlap μ X D) :
    ate μ Y₀ Y₁
      = (∫ ω, (if D ω = true then observed D Y₀ Y₁ ω / armProb μ X D (X ω) true else 0) ∂μ)
        - ∫ ω, (if D ω = false then observed D Y₀ Y₁ ω / armProb μ X D (X ω) false else 0) ∂μ := by
  rw [ipw hX hD h₀ h₁ hunc hov true, ipw hX hD h₀ h₁ hunc hov false, ate, integral_sub h₁ h₀]
  rfl

end Econ.Causal
