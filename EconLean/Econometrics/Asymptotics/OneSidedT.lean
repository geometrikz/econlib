/-
# The t-test as a Wald test, and the one-sided t-test

Hayashi, *Econometrics* (2000), §2.4; Davidson and MacKinnon (2004) §4.4–4.5;
Wooldridge, *Econometric Analysis of Cross Section and Panel Data* (2010), §4.2.

* **`t² = W`** (`tStat_sq_eq_waldStat`): for a single linear restriction `rᵀθ = c`, written as
  the `1 × k` restriction matrix `R = rᵀ`, the squared t statistic equals the Wald statistic
  whenever `rᵀV̂r ≥ 0`.
* **The one-sided t-test** (`t_one_sided`): under `H₀ : rᵀθ₀ = c`, the test rejecting when
  `tₙ > a` has asymptotic rejection probability `P(N(0,1) > a)`.
* **Behaviour away from `rᵀθ₀ = c`** (`t_one_sided_consistent`, `t_one_sided_wrong_side`):
  if `rᵀθ₀ > c` the upper-tailed test rejects with probability tending to `1` (consistency
  against `H₁ : rᵀθ > c`); if `rᵀθ₀ < c` (an interior point of the composite null `rᵀθ ≤ c`)
  it rejects with probability tending to `0`. Size over the composite null is pointwise, not
  uniform.
  (The lower-tailed test is the upper-tailed test for `(−r, −c)`; see `tStat_neg`.)

Conventions as in `TestPower`: `tₙ = 0` when `rᵀV̂ₙr ≤ 0`, and `Wₙ = 0` when `R V̂ₙ Rᵀ` is
singular.
-/
module

public import EconLean.Econometrics.Asymptotics.TestPower

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {k : Type*} [Fintype k]

/-- The `1 × k` restriction matrix `R = rᵀ` of a single linear restriction. -/
def rowMat (r : k → ℝ) : Matrix (Fin 1) k ℝ := Matrix.of fun _ => r

lemma rowMat_mul_mul_transpose (r : k → ℝ) (V : Matrix k k ℝ) :
    rowMat r * V * (rowMat r)ᵀ = Matrix.of fun _ _ => r ⬝ᵥ (V *ᵥ r) := by
  ext i j
  simp only [rowMat, Matrix.mul_apply, Matrix.of_apply, transpose_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma inv_fin_one_const (s : ℝ) :
    (Matrix.of fun _ _ => s : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = Matrix.of fun _ _ => s⁻¹ := by
  rw [Matrix.inv_def, adjugate_fin_one, det_fin_one, Ring.inverse_eq_inv]
  ext i j
  fin_cases i; fin_cases j
  simp

/-- **`t² = W` for a single restriction**: with `R = rᵀ` and `rᵀV̂r ≥ 0`, the squared t statistic
equals the Wald statistic. -/
theorem tStat_sq_eq_waldStat [DecidableEq k] (n : ℕ) (r : k → ℝ) (c : ℝ) (θ : k → ℝ)
    (V : k → k → ℝ) (hV : 0 ≤ r ⬝ᵥ (Matrix.of V *ᵥ r)) :
    tStat n r c θ V ^ 2 = waldStat n (rowMat r) (fun _ => c) θ V := by
  rw [waldStat, rowMat_mul_mul_transpose, inv_fin_one_const, tStat]
  have h1 : (rowMat r *ᵥ θ - fun _ => c) = fun _ => r ⬝ᵥ θ - c := by
    funext i; simp [rowMat, mulVec]
  rw [h1]
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
  simp only [dotProduct, mulVec, Matrix.of_apply] at hV
  rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hV]
  ring

/-- Negating the restriction negates the t statistic: `t(−r, −c) = −t(r, c)`. -/
lemma tStat_neg (n : ℕ) (r : k → ℝ) (c : ℝ) (θ : k → ℝ) (V : k → k → ℝ) :
    tStat n (-r) (-c) θ V = -tStat n r c θ V := by
  simp only [tStat, neg_dotProduct, mulVec_neg, dotProduct_neg, neg_neg]
  ring

/-- If `Xₙ →p x* < 0` and `bₙ ≥ 0` diverges, then for every `a`, `P(a < bₙ Xₙ) → 0`. -/
theorem tendsto_prob_lt_mul_of_neg [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {x : ℝ}
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) (hb0 : ∀ n, 0 ≤ b n)
    (hx : x < 0) (hX : TendstoInMeasure P X atTop (fun _ => x)) (a : ℝ) :
    Tendsto (fun n : ℕ => P {ω | a < b n * X n ω}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hX
  have hx2 : 0 < -x / 2 := by linarith
  have hB := hX (-x / 2) hx2
  have hev : ∀ᶠ n : ℕ in atTop, b n * (x / 2) < a :=
    (hb.atTop_mul_const_of_neg (by linarith : x / 2 < 0)).eventually_lt_atBot a
  have hup : ∀ᶠ n : ℕ in atTop,
      P {ω | a < b n * X n ω} ≤ P {ω | -x / 2 ≤ dist (X n ω) x} := by
    filter_upwards [hev] with n hn
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hcon
    push Not at hcon
    rw [Real.dist_eq, abs_lt] at hcon
    have h1 : X n ω < x / 2 := by linarith [hcon.2]
    have h2 : b n * X n ω ≤ b n * (x / 2) := mul_le_mul_of_nonneg_left h1.le (hb0 n)
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun _ => zero_le) hup

/-- **The one-sided t-test has asymptotic size `P(N(0,1) > a)`**: under `H₀ : rᵀθ₀ = c`, with
`√n (θ̂ₙ − θ₀) →d N(0, V)`, `V ⪰ 0`, `V̂ₙ →p V` and `rᵀVr > 0`, the test rejecting when `tₙ > a`
has rejection probability tending to `P(N(0,1) > a)`. -/
theorem t_one_sided [DecidableEq k] [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (r : k → ℝ) (c : ℝ) (hnull : r ⬝ᵥ θ₀ = c) (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hVpsd : V.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ₀)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp) (a : ℝ) :
    Tendsto (fun n => P {ω | a < tStat n r c (T n ω) (Vhat n ω)}) atTop
      (𝓝 (gaussianReal 0 1 {x | a < x})) := by
  have hlim := (t_normal r c hnull hpos hVpsd hT hV hVm hL hlaw).1
  have ht := t_tendsto r c hnull hpos hT hV hVm
  have hfr : gaussianReal 0 1 (frontier {x : ℝ | a < x}) = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [show {x : ℝ | a < x} = Set.Ioi a from rfl, frontier_Ioi]
    exact measure_singleton a
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht.tendsto
    (E := {x : ℝ | a < x}) (by simp [hlim, hfr])
  simp only [ProbabilityMeasure.coe_mk, hlim] at key
  refine key.congr fun n => ?_
  exact Measure.map_apply_of_aemeasurable (ht.forall_aemeasurable n)
    (measurableSet_Ioi (a := a))

/-- The scaled-estimate representation `tₙ = √n · ((rᵀθ̂ₙ − c) / √(rᵀV̂ₙr))` and its
probability limit, shared by the two fixed-alternative results. -/
lemma t_scaled_tendstoInMeasure [IsProbabilityMeasure P] {T : ℕ → Ω → k → ℝ}
    {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ} (r : k → ℝ) (c : ℝ)
    (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hT : TendstoInMeasure P T atTop (fun _ => θ₀))
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V)) :
    TendstoInMeasure P (fun n ω => (r ⬝ᵥ T n ω - c) * seInv r (Vhat n ω)) atTop
      (fun _ => (r ⬝ᵥ θ₀ - c) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) := by
  let F : (k → ℝ) × (k → k → ℝ) → ℝ := fun p => (r ⬝ᵥ p.1 - c) * seInv r p.2
  have hF : ContinuousAt F (θ₀, Matrix.of.symm V) := by
    have h1 : ContinuousAt (fun p : (k → ℝ) × (k → k → ℝ) => seInv r p.2)
        (θ₀, Matrix.of.symm V) :=
      ContinuousAt.comp (g := seInv r) (f := Prod.snd) (x := (θ₀, Matrix.of.symm V))
        (continuousAt_seInv r (by rwa [Equiv.apply_symm_apply])) continuousAt_snd
    exact ((by fun_prop : Continuous fun p : (k → ℝ) × (k → k → ℝ) =>
      r ⬝ᵥ p.1 - c).continuousAt).mul h1
  have hq := tendstoInMeasure_comp_continuousAt
    (tendstoInMeasure_prodMk (E := k → ℝ) (F := k → k → ℝ) hT hV) hF
  simpa only [F, seInv, Equiv.apply_symm_apply] using hq

lemma tStat_eq_scaled (n : ℕ) (r : k → ℝ) (c : ℝ) (θ : k → ℝ) (V : k → k → ℝ) :
    tStat n r c θ V = Real.sqrt n * ((r ⬝ᵥ θ - c) * seInv r V) := by
  rw [tStat, seInv, mul_assoc]

/-- **Consistency of the upper-tailed t-test**: if `rᵀθ₀ > c`, `θ̂ₙ →p θ₀`, `V̂ₙ →p V` and
`rᵀVr > 0`, then `P(tₙ > a) → 1` for every `a`. -/
theorem t_one_sided_consistent [IsProbabilityMeasure P] {T : ℕ → Ω → k → ℝ}
    {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ} (r : k → ℝ) (c : ℝ)
    (halt : c < r ⬝ᵥ θ₀) (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hT : TendstoInMeasure P T atTop (fun _ => θ₀))
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V)) (a : ℝ) :
    Tendsto (fun n => P {ω | a < tStat n r c (T n ω) (Vhat n ω)}) atTop (𝓝 1) := by
  have hx : 0 < (r ⬝ᵥ θ₀ - c) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹ :=
    mul_pos (sub_pos.mpr halt) (inv_pos.mpr (Real.sqrt_pos.mpr hpos))
  have hb : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [tStat_eq_scaled] using tendsto_prob_lt_mul_of_pos hb
    (fun n => Real.sqrt_nonneg _) hx (t_scaled_tendstoInMeasure r c hpos hT hV) a

/-- **The upper-tailed t-test at a point with `rᵀθ₀ < c`** (an interior point of the
composite null `rᵀθ ≤ c`, or a wrong-side alternative to `H₀ : rᵀθ = c`): if `rᵀθ₀ < c`,
`θ̂ₙ →p θ₀`, `V̂ₙ →p V` and `rᵀVr > 0`, then `P(tₙ > a) → 0` for every `a`. -/
theorem t_one_sided_wrong_side [IsProbabilityMeasure P] {T : ℕ → Ω → k → ℝ}
    {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ} (r : k → ℝ) (c : ℝ)
    (halt : r ⬝ᵥ θ₀ < c) (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hT : TendstoInMeasure P T atTop (fun _ => θ₀))
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V)) (a : ℝ) :
    Tendsto (fun n => P {ω | a < tStat n r c (T n ω) (Vhat n ω)}) atTop (𝓝 0) := by
  have hx : (r ⬝ᵥ θ₀ - c) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹ < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr halt) (inv_pos.mpr (Real.sqrt_pos.mpr hpos))
  have hb : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [tStat_eq_scaled] using tendsto_prob_lt_mul_of_neg hb
    (fun n => Real.sqrt_nonneg _) hx (t_scaled_tendstoInMeasure r c hpos hT hV) a

/-- **Non-vacuity.** Testing `θ₁ ≤ θ₂` against `θ₁ > θ₂` (`r = (1, −1)`, `c = 0`) with
`√n (θ̂ₙ − θ₀) ∼ N(0, I₂)` and `V̂ₙ = (1 + 1/(n+1)) I₂`: `rᵀV̂ₙr ≥ 0` so `tₙ² = Wₙ`; under the
null `θ₀ = 0` the upper-tailed test has asymptotic rejection probability `P(N(0,1) > a)`;
it rejects with probability tending to `1` at `θ₀ = (1, 0)` and to `0` at `θ₀ = (0, 1)`. -/
theorem one_sided_t_witness (a : ℝ) :
    let r : Fin 2 → ℝ := ![1, -1]
    let V : Matrix (Fin 2) (Fin 2) ℝ := 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 V).map ofLp
    let Vhat : ℕ → (Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
      fun n _ => Matrix.of.symm ((1 + 1 / ((n : ℝ) + 1)) • V)
    let θ₁ : Fin 2 → ℝ := ![1, 0]
    let θ₂ : Fin 2 → ℝ := ![0, 1]
    ∃ _ : IsProbabilityMeasure P,
      0 < r ⬝ᵥ (V *ᵥ r) ∧ V.PosSemidef ∧ 0 < r ⬝ᵥ θ₁ ∧ r ⬝ᵥ θ₂ < 0 ∧
      (∀ n ω, 0 ≤ r ⬝ᵥ (Matrix.of (Vhat n ω) *ᵥ r)) ∧
      TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V) ∧ (∀ n, AEMeasurable (Vhat n) P) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n • ((Real.sqrt n)⁻¹ • ω - (0 : Fin 2 → ℝ))) atTop id
        (fun _ => P) P ∧
      Measurable (id : (Fin 2 → ℝ) → Fin 2 → ℝ) ∧ P.map id = (multivariateGaussian 0 V).map ofLp ∧
      TendstoInMeasure P (fun (n : ℕ) ω => θ₁ + (Real.sqrt n)⁻¹ • ω) atTop (fun _ => θ₁) ∧
      TendstoInMeasure P (fun (n : ℕ) ω => θ₂ + (Real.sqrt n)⁻¹ • ω) atTop (fun _ => θ₂) ∧
      (∀ n ω, tStat n r 0 ((Real.sqrt n)⁻¹ • ω) (Vhat n ω) ^ 2
        = waldStat n (rowMat r) (fun _ => 0) ((Real.sqrt n)⁻¹ • ω) (Vhat n ω)) ∧
      Tendsto (fun n => P {ω | a < tStat n r 0 ((Real.sqrt n)⁻¹ • ω) (Vhat n ω)}) atTop
        (𝓝 (gaussianReal 0 1 {x | a < x})) ∧
      Tendsto (fun n => P {ω | a < tStat n r 0 (θ₁ + (Real.sqrt n)⁻¹ • ω) (Vhat n ω)})
        atTop (𝓝 1) ∧
      Tendsto (fun n => P {ω | a < tStat n r 0 (θ₂ + (Real.sqrt n)⁻¹ • ω) (Vhat n ω)})
        atTop (𝓝 0) := by
  intro r V P Vhat θ₁ θ₂
  obtain ⟨hP, hpos, -, -, -, -, hV, hVm, hT0, -, -, hT1, -, -, -⟩ := test_power_witness a
  have hr1 : 0 < r ⬝ᵥ θ₁ := by simp [r, θ₁, dotProduct, Fin.sum_univ_two]
  have hr2 : r ⬝ᵥ θ₂ < 0 := by simp [r, θ₂, dotProduct, Fin.sum_univ_two]
  have hnn : ∀ n ω, 0 ≤ r ⬝ᵥ (Matrix.of (Vhat n ω) *ᵥ r) := fun n ω => by
    simp only [Vhat, Equiv.apply_symm_apply, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (by positivity) hpos.le
  have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hT2 : TendstoInMeasure P (fun (n : ℕ) ω => θ₂ + (Real.sqrt n)⁻¹ • ω) atTop
      (fun _ => θ₂) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (by fun_prop :
      Measurable fun ω : Fin 2 → ℝ => θ₂ + (Real.sqrt n)⁻¹ • ω).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simpa using tendsto_const_nhds.add (hsq.smul_const ω)
  refine ⟨hP, hpos, PosSemidef.one, hr1, hr2, hnn, hV, hVm, hT0, measurable_id, Measure.map_id,
    hT1, hT2, fun n ω => tStat_sq_eq_waldStat n r 0 _ _ (hnn n ω), ?_,
    t_one_sided_consistent r 0 hr1 hpos hT1 hV a, t_one_sided_wrong_side r 0 hr2 hpos hT2 hV a⟩
  exact t_one_sided (θ₀ := 0) r 0 (dotProduct_zero r) hpos PosSemidef.one hT0 hV hVm
    measurable_id Measure.map_id a

end Econ.Asymptotics
