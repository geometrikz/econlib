/-
# Consistency of the Wald test and the t-test

Newey and McFadden (1994) §9; Hayashi, *Econometrics* (2000), Prop. 2.3 and §2.4;
Davidson and MacKinnon (2004) §4.5.

* **Consistency of the Wald test** (`wald_consistent`): under a fixed alternative
  `Rθ₀ ≠ c`, if `θ̂ₙ →p θ₀`, `V̂ₙ →p V` and `R V Rᵀ` is positive definite, then for every
  critical value `a` the rejection probability `P(Wₙ > a)` tends to `1`.
* **The t-test** (`t_tendsto`, `t_normal`): for a single linear restriction `rᵀθ₀ = c`,
  `tₙ = √n (rᵀθ̂ₙ − c) / √(rᵀV̂ₙr) →d N(0, 1)` when `√n (θ̂ₙ − θ₀) →d N(0, V)`, `V̂ₙ →p V`
  and `rᵀVr > 0`; the two-sided test rejecting when `|tₙ| > a` has asymptotic rejection
  probability `P(|N(0,1)| > a)`, and `tₙ` is consistent against fixed alternatives
  (`t_consistent`).

**Conventions.** Mathlib's `Real.sqrt` is `0` on negatives and `x⁻¹ = 0` at `0`, so `tₙ = 0`
when `rᵀV̂ₙr ≤ 0` (and when `n = 0`), and `Wₙ = 0` when `R V̂ₙ Rᵀ` is singular; under the
hypotheses these events have probability tending to zero, so the limits are unaffected.
-/
module

public import EconLean.Econometrics.Asymptotics.ChiSquaredTests

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  {k q : Type*} [Fintype k] [Fintype q] [DecidableEq q]

/-- If `Xₙ →p x* > 0` and `bₙ ≥ 0` diverges, then for every `a`, `P(a < bₙ Xₙ) → 1`. -/
theorem tendsto_prob_lt_mul_of_pos [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {x : ℝ}
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) (hb0 : ∀ n, 0 ≤ b n)
    (hx : 0 < x) (hX : TendstoInMeasure P X atTop (fun _ => x)) (a : ℝ) :
    Tendsto (fun n : ℕ => P {ω | a < b n * X n ω}) atTop (𝓝 1) := by
  rw [tendstoInMeasure_iff_dist] at hX
  have hB := hX (x / 2) (half_pos hx)
  have hev : ∀ᶠ n : ℕ in atTop, a < b n * (x / 2) :=
    (hb.atTop_mul_const (half_pos hx)).eventually_gt_atTop a
  have hlow : ∀ᶠ n : ℕ in atTop,
      1 - P {ω | x / 2 ≤ dist (X n ω) x} ≤ P {ω | a < b n * X n ω} := by
    filter_upwards [hev] with n hn
    have hsub : {ω | a < b n * X n ω}ᶜ ⊆ {ω | x / 2 ≤ dist (X n ω) x} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
      by_contra hcon
      push Not at hcon
      rw [Real.dist_eq, abs_lt] at hcon
      have h1 : x / 2 < X n ω := by linarith [hcon.1]
      have h2 : b n * (x / 2) ≤ b n * X n ω := mul_le_mul_of_nonneg_left h1.le (hb0 n)
      linarith
    have h1 : (1 : ENNReal) ≤ P {ω | a < b n * X n ω} + P {ω | x / 2 ≤ dist (X n ω) x} := by
      calc (1 : ENNReal) = P Set.univ := measure_univ.symm
        _ = P ({ω | a < b n * X n ω} ∪ {ω | a < b n * X n ω}ᶜ) := by rw [Set.union_compl_self]
        _ ≤ P {ω | a < b n * X n ω} + P {ω | a < b n * X n ω}ᶜ := measure_union_le _ _
        _ ≤ _ := by gcongr
    exact tsub_le_iff_right.mpr h1
  have hlim : Tendsto (fun n : ℕ => 1 - P {ω | x / 2 ≤ dist (X n ω) x}) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hB (Or.inl ENNReal.one_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow
    (Eventually.of_forall fun _ => prob_le_one)

/-- The Wald quadratic form `(Rθ − c)ᵀ (R V Rᵀ)⁻¹ (Rθ − c)` in function form. -/
noncomputable def waldForm (R : Matrix q k ℝ) (c : q → ℝ) (p : (k → ℝ) × (k → k → ℝ)) : ℝ :=
  (R *ᵥ p.1 - c) ⬝ᵥ (Matrix.of (waldWeight R p.2) *ᵥ (R *ᵥ p.1 - c))

lemma waldStat_eq_waldForm [DecidableEq k] (n : ℕ) (R : Matrix q k ℝ) (c : q → ℝ) (θ : k → ℝ)
    (V : k → k → ℝ) : waldStat n R c θ V = n * waldForm R c (θ, V) := by
  rw [waldStat, waldForm, of_waldWeight]

lemma continuousAt_waldForm [DecidableEq k] (R : Matrix q k ℝ) (c : q → ℝ) {θ : k → ℝ}
    {V : k → k → ℝ} (h : IsUnit (R * Matrix.of V * Rᵀ).det) :
    ContinuousAt (waldForm R c) (θ, V) := by
  have h1 : ContinuousAt (fun p : (k → ℝ) × (k → k → ℝ) => waldWeight R p.2) (θ, V) :=
    ContinuousAt.comp (g := waldWeight R) (f := Prod.snd) (x := (θ, V))
      (continuousAt_waldWeight R h) continuousAt_snd
  have h2 : ContinuousAt (fun p : (k → ℝ) × (k → k → ℝ) => (R *ᵥ p.1 - c, waldWeight R p.2))
      (θ, V) := ((by fun_prop : Continuous fun p : (k → ℝ) × (k → k → ℝ) =>
        R *ᵥ p.1 - c).continuousAt).prodMk h1
  have hg : Continuous (fun p : (q → ℝ) × (q → q → ℝ) => p.1 ⬝ᵥ (Matrix.of p.2 *ᵥ p.1)) := by
    fun_prop
  exact ContinuousAt.comp (g := fun p : (q → ℝ) × (q → q → ℝ) => p.1 ⬝ᵥ (Matrix.of p.2 *ᵥ p.1))
    (x := (θ, V)) hg.continuousAt h2

/-- **Consistency of the Wald test** (Newey and McFadden 1994 §9): under a fixed alternative
`Rθ₀ ≠ c`, with `θ̂ₙ →p θ₀`, `V̂ₙ →p V` and `R V Rᵀ` positive definite, the probability that
the Wald test rejects at any critical value `a` tends to one. -/
theorem wald_consistent [DecidableEq k] [IsProbabilityMeasure P] {T : ℕ → Ω → k → ℝ}
    {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ} (R : Matrix q k ℝ) (c : q → ℝ)
    (halt : R *ᵥ θ₀ ≠ c) (hRV : (R * V * Rᵀ).PosDef)
    (hT : TendstoInMeasure P T atTop (fun _ => θ₀))
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V)) (a : ℝ) :
    Tendsto (fun n => P {ω | a < waldStat n R c (T n ω) (Vhat n ω)}) atTop (𝓝 1) := by
  have hu : IsUnit (R * Matrix.of (Matrix.of.symm V) * Rᵀ).det := by
    rw [Equiv.apply_symm_apply]; exact (isUnit_iff_isUnit_det _).mp hRV.isUnit
  have hq := tendstoInMeasure_comp_continuousAt
    (tendstoInMeasure_prodMk (E := k → ℝ) (F := k → k → ℝ) hT hV)
    (continuousAt_waldForm R c (θ := θ₀) hu)
  have hpos : 0 < waldForm R c (θ₀, Matrix.of.symm V) := by
    have hd : R *ᵥ θ₀ - c ≠ 0 := sub_ne_zero.mpr halt
    have := hRV.inv.dotProduct_mulVec_pos hd
    rw [star_trivial] at this
    rw [waldForm, of_waldWeight, Equiv.apply_symm_apply]
    exact this
  have := tendsto_prob_lt_mul_of_pos tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n)
    hpos hq a
  simpa only [waldStat_eq_waldForm] using this

section TTest

/-- The t statistic for `H₀ : rᵀθ = c`: `√n (rᵀθ̂ − c) / √(rᵀ V̂ r)`. -/
noncomputable def tStat (n : ℕ) (r : k → ℝ) (c : ℝ) (θ : k → ℝ) (V : k → k → ℝ) : ℝ :=
  Real.sqrt n * (r ⬝ᵥ θ - c) * (Real.sqrt (r ⬝ᵥ (Matrix.of V *ᵥ r)))⁻¹

/-- The reciprocal standard error `1/√(rᵀVr)` in function form. -/
noncomputable def seInv (r : k → ℝ) (V : k → k → ℝ) : ℝ :=
  (Real.sqrt (r ⬝ᵥ (Matrix.of V *ᵥ r)))⁻¹

lemma continuous_quad (r : k → ℝ) : Continuous (fun V : k → k → ℝ => r ⬝ᵥ (Matrix.of V *ᵥ r)) := by
  unfold dotProduct mulVec; fun_prop

lemma continuousAt_seInv (r : k → ℝ) {V : k → k → ℝ} (h : 0 < r ⬝ᵥ (Matrix.of V *ᵥ r)) :
    ContinuousAt (seInv r) V :=
  ContinuousAt.comp (g := fun t : ℝ => (Real.sqrt t)⁻¹) (x := V)
    ((continuousAt_inv₀ (Real.sqrt_pos.mpr h).ne').comp Real.continuous_sqrt.continuousAt)
    (continuous_quad r).continuousAt

lemma measurable_seInv (r : k → ℝ) : Measurable (seInv r) := by
  unfold seInv
  exact (Real.continuous_sqrt.measurable.comp (continuous_quad r).measurable).inv

/-- **The t statistic converges in distribution**: under `H₀ : rᵀθ₀ = c`, with
`√n (θ̂ₙ − θ₀) →d L`, `V̂ₙ →p V` and `rᵀVr > 0`, `tₙ →d rᵀL / √(rᵀVr)`. -/
theorem t_tendsto [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (r : k → ℝ) (c : ℝ) (hnull : r ⬝ᵥ θ₀ = c) (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ₀)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P) :
    TendstoInDistribution (fun n ω => tStat n r c (T n ω) (Vhat n ω)) atTop
      (fun ω => (r ⬝ᵥ L ω) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) (fun _ => P) P' := by
  have hB : TendstoInMeasure P (fun n ω => seInv r (Vhat n ω)) atTop
      (fun _ => seInv r (Matrix.of.symm V)) :=
    tendstoInMeasure_comp_continuousAt hV (continuousAt_seInv r hpos)
  have hBm : ∀ n, AEMeasurable (fun ω => seInv r (Vhat n ω)) P := fun n =>
    (measurable_seInv r).comp_aemeasurable (hVm n)
  have hRT := hT.continuous_comp (g := fun x => r ⬝ᵥ x) (by fun_prop)
  have hS := hRT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hB hBm
  have heq : (fun (n : ℕ) ω => tStat n r c (T n ω) (Vhat n ω))
      = fun (n : ℕ) ω => (fun p : ℝ × ℝ => p.1 * p.2)
        (((fun x => r ⬝ᵥ x) ∘ fun ω => Real.sqrt n • (T n ω - θ₀)) ω, seInv r (Vhat n ω)) := by
    funext n ω
    simp only [Function.comp_apply, tStat, seInv, dotProduct_smul, dotProduct_sub, hnull,
      smul_eq_mul]
  rw [heq]
  exact hS

/-- The two-sided rejection region `{x : a < |x|}` has null boundary under `N(0, 1)`. -/
lemma gaussianReal_frontier_abs (a : ℝ) : gaussianReal 0 1 (frontier {x : ℝ | a < |x|}) = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hsub : frontier {x : ℝ | a < |x|} ⊆ {a, -a} := by
    intro x hx
    have h := frontier_lt_subset_eq continuous_const continuous_abs hx
    simp only [Set.mem_ofPred_eq] at h
    rcases abs_choice x with h' | h'
    · left; rw [← h', h]
    · right; rw [h, h', neg_neg]; rfl
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

/-- **The t-test is asymptotically standard normal**: if moreover `V ⪰ 0` and `L ∼ N(0, V)`,
the limit of `tₙ` is `N(0, 1)`, and the two-sided test rejecting when `|tₙ| > a` has
asymptotic rejection probability `P(|N(0,1)| > a)`. -/
theorem t_normal [DecidableEq k] [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (r : k → ℝ) (c : ℝ) (hnull : r ⬝ᵥ θ₀ = c) (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hVpsd : V.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ₀)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp) :
    P'.map (fun ω => (r ⬝ᵥ L ω) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) = gaussianReal 0 1 ∧
    ∀ a : ℝ, Tendsto (fun n => P {ω | a < |tStat n r c (T n ω) (Vhat n ω)|}) atTop
      (𝓝 (gaussianReal 0 1 {x | a < |x|})) := by
  classical
  set σ2 := r ⬝ᵥ (V *ᵥ r) with hσ2
  let A : Matrix (Fin 1) k ℝ := Matrix.of fun _ => r
  have hA := map_mulVec_of_gaussian hL hVpsd hlaw A
  have hApsd : (A * V * Aᵀ).PosSemidef := by
    have := hVpsd.mul_mul_conjTranspose_same A
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hAVA : (A * V * Aᵀ) 0 0 = σ2 := by
    simp only [A, Matrix.mul_apply, Matrix.of_apply, transpose_apply, hσ2, dotProduct, mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrL : P'.map (fun ω => r ⬝ᵥ L ω) = gaussianReal 0 σ2.toNNReal := by
    have hm : Measurable (fun ω => A *ᵥ L ω) :=
      (by fun_prop : Continuous fun x : k → ℝ => A *ᵥ x).measurable.comp hL
    have h1 : (fun ω => r ⬝ᵥ L ω) = (fun v : Fin 1 → ℝ => v 0) ∘ (fun ω => A *ᵥ L ω) := by
      funext ω; rfl
    rw [h1, ← Measure.map_map (measurable_pi_apply 0) hm, hA,
      Measure.map_map (measurable_pi_apply 0) (PiLp.continuous_ofLp 2 _).measurable]
    have := (measurePreserving_eval_multivariateGaussian (μ := 0) hApsd (i := 0)).map_eq
    rw [hAVA] at this
    exact this
  have hs : (Real.sqrt σ2)⁻¹ ^ 2 * σ2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hlim : P'.map (fun ω => (r ⬝ᵥ L ω) * (Real.sqrt σ2)⁻¹) = gaussianReal 0 1 := by
    have hm : Measurable (fun ω => r ⬝ᵥ L ω) :=
      (by fun_prop : Continuous fun x : k → ℝ => r ⬝ᵥ x).measurable.comp hL
    rw [show (fun ω => (r ⬝ᵥ L ω) * (Real.sqrt σ2)⁻¹)
        = (fun t => t * (Real.sqrt σ2)⁻¹) ∘ (fun ω => r ⬝ᵥ L ω) from rfl,
      ← Measure.map_map (by fun_prop) hm, hrL, gaussianReal_map_mul_const]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hpos.le, NNReal.coe_one]
      exact hs
  refine ⟨hlim, fun a => ?_⟩
  have ht := t_tendsto r c hnull hpos hT hV hVm
  rw [← hσ2] at ht
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht.tendsto
    (E := {x : ℝ | a < |x|}) (by simp [hlim, gaussianReal_frontier_abs])
  simp only [ProbabilityMeasure.coe_mk, hlim] at key
  refine key.congr fun n => ?_
  rw [Measure.map_apply_of_aemeasurable (ht.forall_aemeasurable n)
    (measurableSet_lt measurable_const continuous_abs.measurable)]
  rfl

/-- **Consistency of the t-test**: under a fixed alternative `rᵀθ₀ ≠ c`, with `θ̂ₙ →p θ₀`,
`V̂ₙ →p V` and `rᵀVr > 0`, `P(|tₙ| > a) → 1` for every `a`. -/
theorem t_consistent [IsProbabilityMeasure P] {T : ℕ → Ω → k → ℝ}
    {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ} (r : k → ℝ) (c : ℝ)
    (halt : r ⬝ᵥ θ₀ ≠ c) (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hT : TendstoInMeasure P T atTop (fun _ => θ₀))
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V)) (a : ℝ) :
    Tendsto (fun n => P {ω | a < |tStat n r c (T n ω) (Vhat n ω)|}) atTop (𝓝 1) := by
  let F : (k → ℝ) × (k → k → ℝ) → ℝ := fun p => |r ⬝ᵥ p.1 - c| * seInv r p.2
  have hF : ContinuousAt F (θ₀, Matrix.of.symm V) := by
    have h1 : ContinuousAt (fun p : (k → ℝ) × (k → k → ℝ) => seInv r p.2)
        (θ₀, Matrix.of.symm V) :=
      ContinuousAt.comp (g := seInv r) (f := Prod.snd) (x := (θ₀, Matrix.of.symm V))
        (continuousAt_seInv r hpos) continuousAt_snd
    exact ((by fun_prop : Continuous fun p : (k → ℝ) × (k → k → ℝ) =>
      |r ⬝ᵥ p.1 - c|).continuousAt).mul h1
  have hq := tendstoInMeasure_comp_continuousAt
    (tendstoInMeasure_prodMk (E := k → ℝ) (F := k → k → ℝ) hT hV) hF
  have hFpos : 0 < F (θ₀, Matrix.of.symm V) := by
    refine mul_pos (abs_pos.mpr (sub_ne_zero.mpr halt)) (inv_pos.mpr (Real.sqrt_pos.mpr ?_))
    show 0 < r ⬝ᵥ (Matrix.of (Matrix.of.symm V) *ᵥ r)
    rw [Equiv.apply_symm_apply]; exact hpos
  have hb : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have := tendsto_prob_lt_mul_of_pos hb (fun n => Real.sqrt_nonneg _) hFpos hq a
  refine this.congr fun n => ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, F, tStat, seInv, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_inv, mul_assoc]

/-- **Non-vacuity.** Testing `θ₁ = θ₂` (`r = (1, −1)`, `R = (1, −1)`, `c = 0`) with
`√n (θ̂ₙ − θ₀) ∼ N(0, I₂)` and `V̂ₙ = (1 + 1/(n+1)) I₂`:
under the null `θ₀ = 0` the two-sided t-test has asymptotic rejection probability
`P(|N(0,1)| > a)`; under the alternative `θ₀ = (1, 0)` both the t-test and the Wald test reject
with probability tending to one. -/
theorem test_power_witness (a : ℝ) :
    let r : Fin 2 → ℝ := ![1, -1]
    let R : Matrix (Fin 1) (Fin 2) ℝ := !![1, -1]
    let V : Matrix (Fin 2) (Fin 2) ℝ := 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 V).map ofLp
    let Vhat : ℕ → (Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
      fun n _ => Matrix.of.symm ((1 + 1 / ((n : ℝ) + 1)) • V)
    let θ₁ : Fin 2 → ℝ := ![1, 0]
    ∃ _ : IsProbabilityMeasure P,
      0 < r ⬝ᵥ (V *ᵥ r) ∧ V.PosSemidef ∧ (R * V * Rᵀ).PosDef ∧ r ⬝ᵥ θ₁ ≠ 0 ∧ R *ᵥ θ₁ ≠ 0 ∧
      TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V) ∧ (∀ n, AEMeasurable (Vhat n) P) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n • ((Real.sqrt n)⁻¹ • ω - (0 : Fin 2 → ℝ))) atTop id
        (fun _ => P) P ∧
      Measurable (id : (Fin 2 → ℝ) → Fin 2 → ℝ) ∧ P.map id = (multivariateGaussian 0 V).map ofLp ∧
      TendstoInMeasure P (fun (n : ℕ) ω => θ₁ + (Real.sqrt n)⁻¹ • ω) atTop (fun _ => θ₁) ∧
      Tendsto (fun n => P {ω | a < |tStat n r 0 ((Real.sqrt n)⁻¹ • ω) (Vhat n ω)|}) atTop
        (𝓝 (gaussianReal 0 1 {x | a < |x|})) ∧
      Tendsto (fun n => P {ω | a < |tStat n r 0 (θ₁ + (Real.sqrt n)⁻¹ • ω) (Vhat n ω)|})
        atTop (𝓝 1) ∧
      Tendsto (fun n => P {ω | a < waldStat n R 0 (θ₁ + (Real.sqrt n)⁻¹ • ω) (Vhat n ω)})
        atTop (𝓝 1) := by
  intro r R V P Vhat θ₁
  have hofLp : Measurable (ofLp : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff hofLp.aemeasurable).mpr inferInstance
  have hpos : 0 < r ⬝ᵥ (V *ᵥ r) := by
    simp [r, V, dotProduct, Fin.sum_univ_two]
  have hRV : (R * V * Rᵀ).PosDef := by
    have h2 : R * V * Rᵀ = !![2] := by
      ext i j
      fin_cases i; fin_cases j
      simp [R, V, Matrix.mul_apply, Fin.sum_univ_two]
      norm_num
    rw [h2]
    have : (!![2] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal (fun _ => 2) := by
      ext i j; fin_cases i; fin_cases j; rfl
    rw [this]
    exact PosDef.diagonal fun _ => by norm_num
  have hr1 : r ⬝ᵥ θ₁ ≠ 0 := by simp [r, θ₁, dotProduct, Fin.sum_univ_two]
  have hR1 : R *ᵥ θ₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [R, θ₁, mulVec, dotProduct, Fin.sum_univ_two] at this
  have hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V) := by
    refine tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => ?_)
    have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) • Matrix.of.symm V) atTop
        (𝓝 (Matrix.of.symm V)) := by
      simpa only [one_smul] using h1.smul_const (Matrix.of.symm V)
    exact h2
  have hVm : ∀ n, AEMeasurable (Vhat n) P := fun _ => aemeasurable_const
  have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hT1 : TendstoInMeasure P (fun (n : ℕ) ω => θ₁ + (Real.sqrt n)⁻¹ • ω) atTop
      (fun _ => θ₁) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (by fun_prop :
      Measurable fun ω : Fin 2 → ℝ => θ₁ + (Real.sqrt n)⁻¹ • ω).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simpa using tendsto_const_nhds.add (hsq.smul_const ω)
  have hT0 : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • ((Real.sqrt n)⁻¹ • ω - (0 : Fin 2 → ℝ))) atTop id
      (fun _ => P) P := by
    refine ⟨fun n => by fun_prop, by fun_prop, ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt n ≠ 0 := by
      rw [Real.sqrt_ne_zero']; exact_mod_cast hn
    apply Subtype.ext
    simp only [sub_zero, smul_smul, mul_inv_cancel₀ hs, one_smul]
    rfl
  refine ⟨hP, hpos, PosSemidef.one, hRV, hr1, hR1, hV, hVm, hT0, measurable_id, Measure.map_id,
    hT1, ?_, t_consistent r 0 hr1 hpos hT1 hV a,
    wald_consistent R 0 hR1 hRV hT1 hV a⟩
  exact (t_normal (θ₀ := 0) r 0 (dotProduct_zero r) hpos PosSemidef.one hT0 hV hVm
    measurable_id Measure.map_id).2 a

end TTest

end Econ.Asymptotics
