/-
# Local power of the t-test and the Wald test

Hayashi, *Econometrics* (2000), §2.4; Newey and McFadden (1994) §9.2;
van der Vaart, *Asymptotic Statistics* (1998), §14–15; Davidson and MacKinnon (2004) §4.8.

Under a sequence of **local (Pitman) alternatives** the true parameter `θₙ` drifts towards the null
at rate `1/√n`: `√n (rᵀθₙ − c) → h` (resp. `√n (Rθₙ − c) → h`). If `√n (θ̂ₙ − θₙ) →d L`,
`V̂ₙ →p V` and `rᵀVr > 0`:

* **t statistic** (`t_local_tendsto`, `t_local_normal`): `tₙ →d (rᵀL + h)/√(rᵀVr)`, which is
  `N(h/σ, 1)` with `σ = √(rᵀVr)` when `L ∼ N(0, V)`. Hence the asymptotic local power of the
  upper-tailed test is `P(N(h/σ, 1) > a)` and of the two-sided test `P(|N(h/σ, 1)| > a)`;
  `h = 0` recovers the asymptotic size.
* **Monotonicity of the local power function** (`gaussianReal_Ioi_mono`,
  `t_local_power_mono`): the one-sided local power `P(N(μ, 1) > a)` is nondecreasing in `μ`,
  so it is at least the size whenever `h ≥ 0`.
* **Wald statistic** (`wald_local_tendsto`): `Wₙ →d (RL + h)ᵀ (R V Rᵀ)⁻¹ (RL + h)`.
* **Noncentral χ²** (`ncChiSq`, `ncChiSq_zero`, `ncChiSq_singleton`): the law of
  `∑ᵢ (Zᵢ + μᵢ)²` for independent standard normals `Zᵢ`; it reduces to `χ²(q)` at `μ = 0` and,
  with at least one coordinate, has no atoms. With `M = R V Rᵀ` positive definite, `L ∼ N(0, V)` and `μ = M^{-1/2} h`, the local
  Wald limit is `ncChiSq μ` (`map_wald_local_limit`), with noncentrality
  `‖μ‖² = hᵀ M⁻¹ h` (`noncentrality_eq`), and the asymptotic local power of the Wald test is
  `P(ncChiSq μ > a)` (`wald_local_power`).

The drift `√n (rᵀθₙ − c) → h` is only assumed in the limit, which covers the textbook
`θₙ = θ₀ + δ/√n` with `rᵀθ₀ = c` and `h = rᵀδ`.
-/
module

public import EconLean.Econometrics.Asymptotics.OneSidedT

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {k q : Type*} [Fintype k] [Fintype q] [DecidableEq q]

/-- A deterministic (not necessarily constant) convergent sequence converges in probability. -/
lemma tendstoInMeasure_of_tendsto_const [IsFiniteMeasure P] {E : Type*} [PseudoMetricSpace E] {d : ℕ → E} {h : E}
    (hd : Tendsto d atTop (𝓝 h)) :
    TendstoInMeasure P (fun n (_ : Ω) => d n) atTop (fun _ => h) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall fun _ => hd)

/-- **The t statistic under local alternatives**: if `√n (θ̂ₙ − θₙ) →d L`,
`√n (rᵀθₙ − c) → h`, `V̂ₙ →p V` and `rᵀVr > 0`, then `tₙ →d (rᵀL + h)/√(rᵀVr)`. -/
theorem t_local_tendsto [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ : ℕ → k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (r : k → ℝ) (c h : ℝ)
    (hdrift : Tendsto (fun n : ℕ => Real.sqrt n * (r ⬝ᵥ θ n - c)) atTop (𝓝 h))
    (hpos : 0 < r ⬝ᵥ (V *ᵥ r))
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ n)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P) :
    TendstoInDistribution (fun n ω => tStat n r c (T n ω) (Vhat n ω)) atTop
      (fun ω => (r ⬝ᵥ L ω + h) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) (fun _ => P) P' := by
  have hB : TendstoInMeasure P (fun n ω => seInv r (Vhat n ω)) atTop
      (fun _ => seInv r (Matrix.of.symm V)) :=
    tendstoInMeasure_comp_continuousAt hV (continuousAt_seInv r (by rwa [Equiv.apply_symm_apply]))
  have hY := tendstoInMeasure_prodMk (E := ℝ) (F := ℝ)
    (tendstoInMeasure_of_tendsto_const (P := P) hdrift) hB
  have hYm : ∀ n : ℕ, AEMeasurable
      (fun ω => (Real.sqrt n * (r ⬝ᵥ θ n - c), seInv r (Vhat n ω))) P := fun (n : ℕ) =>
    aemeasurable_const.prodMk ((measurable_seInv r).comp_aemeasurable (hVm n))
  have hRT := hT.continuous_comp (g := fun x => r ⬝ᵥ x) (by fun_prop)
  have hS := hRT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × (ℝ × ℝ) => (p.1 + p.2.1) * p.2.2) (by fun_prop) hY hYm
  have heq : (fun (n : ℕ) ω => tStat n r c (T n ω) (Vhat n ω))
      = fun (n : ℕ) ω => (fun p : ℝ × (ℝ × ℝ) => (p.1 + p.2.1) * p.2.2)
        (((fun x => r ⬝ᵥ x) ∘ fun ω => Real.sqrt n • (T n ω - θ n)) ω,
          (Real.sqrt n * (r ⬝ᵥ θ n - c), seInv r (Vhat n ω))) := by
    funext n ω
    simp only [Function.comp_apply, tStat, seInv, dotProduct_smul, dotProduct_sub, smul_eq_mul]
    ring
  have hlim : (fun ω => (r ⬝ᵥ L ω + h) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹)
      = fun ω => (fun p : ℝ × (ℝ × ℝ) => (p.1 + p.2.1) * p.2.2)
        (((fun x => r ⬝ᵥ x) ∘ L) ω, (h, seInv r (Matrix.of.symm V))) := by
    funext ω
    simp only [Function.comp_apply, seInv, Equiv.apply_symm_apply]
  rw [heq, hlim]
  exact hS

/-- **The local limit of the t statistic is `N(h/σ, 1)`**: if moreover `V ⪰ 0` and `L ∼ N(0, V)`,
with `σ = √(rᵀVr)`, the limit is `N(h/σ, 1)`; the upper-tailed test has asymptotic local power
`P(N(h/σ, 1) > a)` and the two-sided test `P(|N(h/σ, 1)| > a)`. -/
theorem t_local_normal [DecidableEq k] [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ : ℕ → k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (r : k → ℝ) (c h : ℝ)
    (hdrift : Tendsto (fun n : ℕ => Real.sqrt n * (r ⬝ᵥ θ n - c)) atTop (𝓝 h))
    (hpos : 0 < r ⬝ᵥ (V *ᵥ r)) (hVpsd : V.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ n)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp) :
    P'.map (fun ω => (r ⬝ᵥ L ω + h) * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹)
        = gaussianReal (h * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) 1 ∧
    (∀ a : ℝ, Tendsto (fun n => P {ω | a < tStat n r c (T n ω) (Vhat n ω)}) atTop
      (𝓝 (gaussianReal (h * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) 1 {x | a < x}))) ∧
    ∀ a : ℝ, Tendsto (fun n => P {ω | a < |tStat n r c (T n ω) (Vhat n ω)|}) atTop
      (𝓝 (gaussianReal (h * (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹) 1 {x | a < |x|})) := by
  set s := (Real.sqrt (r ⬝ᵥ (V *ᵥ r)))⁻¹ with hs
  -- the law of `rᵀL/σ` is `N(0,1)` (the central case, applied to a constant sequence)
  have h0 : P'.map (fun ω => (r ⬝ᵥ L ω) * s) = gaussianReal 0 1 := by
    have hT0 : TendstoInDistribution
        (fun (n : ℕ) (ω' : Ω') => Real.sqrt n • ((Real.sqrt n)⁻¹ • L ω' - 0)) atTop L
        (fun _ => P') P' := by
      refine ⟨fun n => (by fun_prop : Continuous fun x : k → ℝ =>
        Real.sqrt n • ((Real.sqrt n)⁻¹ • x - 0)).measurable.comp_aemeasurable hL.aemeasurable,
        hL.aemeasurable, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hsn : Real.sqrt n ≠ 0 := by rw [Real.sqrt_ne_zero']; exact_mod_cast hn
      apply Subtype.ext
      simp only [sub_zero, smul_smul, mul_inv_cancel₀ hsn, one_smul]
    exact (t_normal (P := P') (θ₀ := 0) (Vhat := fun _ _ => Matrix.of.symm V) r 0
      (dotProduct_zero r) hpos hVpsd hT0 (tendstoInMeasure_of_tendsto_const tendsto_const_nhds) (fun _ => aemeasurable_const)
      hL hlaw).1
  have hm : Measurable (fun ω => (r ⬝ᵥ L ω) * s) :=
    ((by fun_prop : Continuous fun x : k → ℝ => r ⬝ᵥ x).measurable.comp hL).mul_const s
  have hlim : P'.map (fun ω => (r ⬝ᵥ L ω + h) * s) = gaussianReal (h * s) 1 := by
    rw [show (fun ω => (r ⬝ᵥ L ω + h) * s) = (· + h * s) ∘ (fun ω => (r ⬝ᵥ L ω) * s) by
        funext ω; simp only [Function.comp_apply]; ring,
      ← Measure.map_map (by fun_prop) hm, h0, gaussianReal_map_add_const, zero_add]
  have ht := t_local_tendsto r c h hdrift hpos hT hV hVm
  rw [← hs] at ht
  have hnull := nullSingletonClass_gaussianReal (μ := h * s) (v := 1) one_ne_zero
  refine ⟨hlim, fun a => ?_, fun a => ?_⟩
  · have hfr : gaussianReal (h * s) 1 (frontier {x : ℝ | a < x}) = 0 := by
      rw [show {x : ℝ | a < x} = Set.Ioi a from rfl, frontier_Ioi]
      exact measure_singleton a
    have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht.tendsto
      (E := {x : ℝ | a < x}) (by simp [hlim, hfr])
    simp only [ProbabilityMeasure.coe_mk, hlim] at key
    refine key.congr fun n => ?_
    exact Measure.map_apply_of_aemeasurable (ht.forall_aemeasurable n)
      (measurableSet_Ioi (a := a))
  · have hfr : gaussianReal (h * s) 1 (frontier {x : ℝ | a < |x|}) = 0 := by
      have hsub : frontier {x : ℝ | a < |x|} ⊆ {a, -a} := by
        intro x hx
        have h' := frontier_lt_subset_eq continuous_const continuous_abs hx
        simp only [Set.mem_ofPred_eq] at h'
        rcases abs_choice x with h'' | h''
        · left; rw [← h'', h']
        · right; rw [h', h'', neg_neg]; rfl
      exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)
    have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht.tendsto
      (E := {x : ℝ | a < |x|}) (by simp [hlim, hfr])
    simp only [ProbabilityMeasure.coe_mk, hlim] at key
    refine key.congr fun n => ?_
    rw [Measure.map_apply_of_aemeasurable (ht.forall_aemeasurable n)
      (measurableSet_lt measurable_const continuous_abs.measurable)]
    rfl

/-- The upper-tail probability `P(N(μ, 1) > a)` is nondecreasing in the mean `μ`. -/
lemma gaussianReal_Ioi_mono {μ μ' : ℝ} (hμ : μ ≤ μ') (a : ℝ) :
    gaussianReal μ 1 (Set.Ioi a) ≤ gaussianReal μ' 1 (Set.Ioi a) := by
  have e : ∀ m : ℝ, gaussianReal m 1 = (gaussianReal 0 1).map (· + m) := fun m => by
    rw [gaussianReal_map_add_const, zero_add]
  rw [e μ, e μ', Measure.map_apply (by fun_prop) measurableSet_Ioi,
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_Ioi] at hx ⊢
  linarith

/-- **Monotone local power**: the asymptotic local power `P(N(h/σ, 1) > a)` of the upper-tailed
t-test is nondecreasing in the drift `h`; taking `h = 0 ≤ h'` shows it is at least the asymptotic
size `P(N(0, 1) > a)` for every nonnegative drift. -/
theorem t_local_power_mono (σ : ℝ) (hσ : 0 < σ) {h h' : ℝ} (hh : h ≤ h') (a : ℝ) :
    gaussianReal (h * σ⁻¹) 1 {x | a < x} ≤ gaussianReal (h' * σ⁻¹) 1 {x | a < x} :=
  gaussianReal_Ioi_mono (mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hσ.le)) a

/-- **The Wald statistic under local alternatives**: if `√n (θ̂ₙ − θₙ) →d L`,
`√n (Rθₙ − c) → h`, `V̂ₙ →p V` and `R V Rᵀ` is invertible, then
`Wₙ →d (RL + h)ᵀ (R V Rᵀ)⁻¹ (RL + h)`. -/
theorem wald_local_tendsto [DecidableEq k] [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ : ℕ → k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (R : Matrix q k ℝ) (c h : q → ℝ)
    (hdrift : Tendsto (fun n : ℕ => Real.sqrt n • (R *ᵥ θ n - c)) atTop (𝓝 h))
    (hR : IsUnit (R * V * Rᵀ).det)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ n)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P) :
    TendstoInDistribution (fun n ω => waldStat n R c (T n ω) (Vhat n ω)) atTop
      (fun ω => (R *ᵥ L ω + h) ⬝ᵥ ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ L ω + h))) (fun _ => P) P' := by
  have hB : TendstoInMeasure P (fun n ω => waldWeight R (Vhat n ω)) atTop
      (fun _ => waldWeight R (Matrix.of.symm V)) :=
    tendstoInMeasure_comp_continuousAt hV
      (continuousAt_waldWeight R (by rw [Equiv.apply_symm_apply]; exact hR))
  have hY := tendstoInMeasure_prodMk (E := q → ℝ) (F := q → q → ℝ)
    (tendstoInMeasure_of_tendsto_const (P := P) hdrift) hB
  have hYm : ∀ n : ℕ, AEMeasurable
      (fun ω => (Real.sqrt n • (R *ᵥ θ n - c), waldWeight R (Vhat n ω))) P := fun (n : ℕ) =>
    aemeasurable_const.prodMk ((measurable_waldWeight R).comp_aemeasurable (hVm n))
  have hRT := hT.continuous_comp (g := fun x => R *ᵥ x) (by fun_prop)
  have hS := hRT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × ((q → ℝ) × (q → q → ℝ)) =>
      (p.1 + p.2.1) ⬝ᵥ (Matrix.of p.2.2 *ᵥ (p.1 + p.2.1))) (by fun_prop) hY hYm
  have heq : (fun (n : ℕ) ω => waldStat n R c (T n ω) (Vhat n ω))
      = fun (n : ℕ) ω => (fun p : (q → ℝ) × ((q → ℝ) × (q → q → ℝ)) =>
          (p.1 + p.2.1) ⬝ᵥ (Matrix.of p.2.2 *ᵥ (p.1 + p.2.1)))
        (((fun x => R *ᵥ x) ∘ fun ω => Real.sqrt n • (T n ω - θ n)) ω,
          (Real.sqrt n • (R *ᵥ θ n - c), waldWeight R (Vhat n ω))) := by
    funext n ω
    have hx : R *ᵥ (Real.sqrt n • (T n ω - θ n)) + Real.sqrt n • (R *ᵥ θ n - c)
        = Real.sqrt n • (R *ᵥ T n ω - c) := by
      rw [mulVec_smul, mulVec_sub, ← smul_add]
      congr 1
      abel
    simp only [Function.comp_apply, waldStat, of_waldWeight]
    rw [hx, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hlim : (fun ω => (R *ᵥ L ω + h) ⬝ᵥ ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ L ω + h)))
      = fun ω => (fun p : (q → ℝ) × ((q → ℝ) × (q → q → ℝ)) =>
          (p.1 + p.2.1) ⬝ᵥ (Matrix.of p.2.2 *ᵥ (p.1 + p.2.1)))
        (((fun x => R *ᵥ x) ∘ L) ω, (h, waldWeight R (Matrix.of.symm V))) := by
    funext ω
    simp only [Function.comp_apply, of_waldWeight]
    rfl
  rw [heq, hlim]
  exact hS

section Noncentral

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The **noncentral χ² distribution** with mean vector `μ`: the law of `∑ᵢ (Zᵢ + μᵢ)²` for
independent standard normals `Zᵢ`, `i ∈ ι`. (Classically it depends on `μ` only through `|ι|` and
the noncentrality `‖μ‖²`; that invariance is not formalized here.) -/
noncomputable def ncChiSq {ι : Type*} [Fintype ι] (μ : ι → ℝ) : Measure ℝ :=
  (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun z => ∑ i, (z i + μ i) ^ 2)

instance {ι : Type*} [Fintype ι] (μ : ι → ℝ) : IsProbabilityMeasure (ncChiSq μ) := by
  unfold ncChiSq; infer_instance

/-- With zero noncentrality the noncentral χ² is the central `χ²(|ι|)`. -/
theorem ncChiSq_zero (ι : Type*) [Fintype ι] : ncChiSq (0 : ι → ℝ) = chiSq (Fintype.card ι) := by
  simpa [ncChiSq] using map_sum_sq_eq_chiSq ι

/-- Reindexing the coordinates does not change the noncentral χ². -/
lemma ncChiSq_reindex {ι : Type*} [Fintype ι] (μ : ι → ℝ) :
    ncChiSq μ = ncChiSq (μ ∘ (Fintype.equivFin ι).symm) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  rw [ncChiSq, ncChiSq, ← hp.map_eq, Measure.map_map (by fun_prop) hp.measurable]
  congr 1
  funext z
  simp only [Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

lemma ncChiSq_fin_singleton (n : ℕ) (μ : Fin (n + 1) → ℝ) (c : ℝ) : ncChiSq μ {c} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
  set B : Set (ℝ × (Fin n → ℝ)) :=
    {p | (p.1 + μ 0) ^ 2 + ∑ j : Fin n, (p.2 j + μ j.succ) ^ 2 = c} with hB
  have hBm : MeasurableSet B := measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hpre : (fun z : Fin (n + 1) → ℝ => ∑ i, (z i + μ i) ^ 2) ⁻¹' {c}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹' B := by
    ext z
    simp [hB, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Fin.tail]
  rw [ncChiSq, Measure.map_apply (by fun_prop) (measurableSet_singleton c), hpre,
    hp.measure_preimage hBm.nullMeasurableSet, Measure.prod_apply_symm hBm]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  set t := c - ∑ j : Fin n, (y j + μ j.succ) ^ 2
  have hsub : (fun x => (x, y)) ⁻¹' B ⊆ {Real.sqrt t - μ 0, -Real.sqrt t - μ 0} := by
    intro x hx
    have hx2 : (x + μ 0) ^ 2 = t := by
      simp only [Set.mem_preimage, hB, Set.mem_ofPred_eq] at hx; linarith
    have habs : |x + μ 0| = Real.sqrt t := by rw [← hx2, Real.sqrt_sq_eq_abs]
    rcases abs_choice (x + μ 0) with h | h
    · left; rw [← habs, h]; ring
    · right
      have : x = -Real.sqrt t - μ 0 := by rw [← habs, h]; ring
      rw [this]; rfl
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

/-- With at least one coordinate the noncentral χ² has no atoms. -/
theorem ncChiSq_singleton {ι : Type*} [Fintype ι] [Nonempty ι] (μ : ι → ℝ) (c : ℝ) :
    ncChiSq μ {c} = 0 := by
  rw [ncChiSq_reindex]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by
    have := Fintype.card_pos (α := ι); omega⟩
  generalize μ ∘ (Fintype.equivFin ι).symm = ν
  revert ν
  rw [hn]
  exact fun ν => ncChiSq_fin_singleton n ν c

variable {M : Matrix q q ℝ}

/-- The noncentrality: with `S = M^{1/2}` for positive definite `M`, `‖S⁻¹h‖² = hᵀM⁻¹h`. -/
theorem noncentrality_eq (hM : M.PosDef) (h : q → ℝ) :
    ((CFC.sqrt M)⁻¹ *ᵥ h) ⬝ᵥ ((CFC.sqrt M)⁻¹ *ᵥ h) = h ⬝ᵥ (M⁻¹ *ᵥ h) := by
  set S := CFC.sqrt M with hSdef
  have hS0 : S.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hSt : Sᵀ = S := by
    have := hS0.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hSS : S * S = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, hSt, mulVec_mulVec,
    ← Matrix.mul_inv_rev, hSS, dotProduct_comm]

/-- **The local Wald limit is noncentral χ²**: if `L ∼ N(0, V)`, `V ⪰ 0` and `M = R V Rᵀ` is positive
definite, then `(RL + h)ᵀ M⁻¹ (RL + h) ∼ ncChiSq (M^{-1/2} h)`. -/
theorem map_wald_local_limit [DecidableEq k] {L : Ω' → k → ℝ} {V : Matrix k k ℝ} (R : Matrix q k ℝ) (h : q → ℝ)
    (hVpsd : V.PosSemidef) (hM : (R * V * Rᵀ).PosDef) (hL : Measurable L)
    (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp) :
    P'.map (fun ω => (R *ᵥ L ω + h) ⬝ᵥ ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ L ω + h)))
      = ncChiSq ((CFC.sqrt (R * V * Rᵀ))⁻¹ *ᵥ h) := by
  set M := R * V * Rᵀ with hMdef
  set S := CFC.sqrt M with hSdef
  have hRL := map_mulVec_of_gaussian hL hVpsd hlaw R
  have hS0 : S.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hSt : Sᵀ = S := by
    have := hS0.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hSS : S * S = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hSdet : IsUnit S.det := by
    have hMd : M.det ≠ 0 := hM.det_pos.ne'
    rw [← hSS, det_mul] at hMd
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hMd)
  have hf : Measurable (fun y : q → ℝ => (y + h) ⬝ᵥ (M⁻¹ *ᵥ (y + h))) :=
    (by fun_prop : Continuous fun y : q → ℝ => (y + h) ⬝ᵥ (M⁻¹ *ᵥ (y + h))).measurable
  have hRLm : Measurable (fun ω => R *ᵥ L ω) :=
    (by fun_prop : Continuous fun x : k → ℝ => R *ᵥ x).measurable.comp hL
  rw [show (fun ω => (R *ᵥ L ω + h) ⬝ᵥ (M⁻¹ *ᵥ (R *ᵥ L ω + h)))
      = (fun y => (y + h) ⬝ᵥ (M⁻¹ *ᵥ (y + h))) ∘ (fun ω => R *ᵥ L ω) from rfl,
    ← Measure.map_map hf hRLm, hRL, map_multivariateGaussian_eq,
    Measure.map_map hf (by fun_prop), ncChiSq]
  congr 1
  funext z
  simp only [Function.comp_apply]
  have hw : S *ᵥ z + h = S *ᵥ (z + S⁻¹ *ᵥ h) := by
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hSdet, one_mulVec]
  have hcore : S * M⁻¹ * S = 1 := by
    rw [← hSS, Matrix.mul_inv_rev]
    calc S * (S⁻¹ * S⁻¹) * S = (S * S⁻¹) * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hSdet, nonsing_inv_mul _ hSdet, Matrix.one_mul]
  rw [hw, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hSt, mulVec_mulVec,
    mulVec_mulVec, hcore, one_mulVec]
  simp only [dotProduct, Pi.add_apply, sq]

/-- **Asymptotic local power of the Wald test**: under local alternatives `√n (Rθₙ − c) → h`,
with `√n (θ̂ₙ − θₙ) →d L ∼ N(0, V)`, `V ⪰ 0`, `V̂ₙ →p V`, `M = R V Rᵀ` positive definite and at
least one restriction, the Wald test rejecting when `Wₙ > a` has rejection probability tending
to `P(ncChiSq(M^{-1/2} h) > a)`. -/
theorem wald_local_power [DecidableEq k] [Nonempty q] [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ : ℕ → k → ℝ}
    {V : Matrix k k ℝ} {L : Ω' → k → ℝ} (R : Matrix q k ℝ) (c h : q → ℝ)
    (hdrift : Tendsto (fun n : ℕ => Real.sqrt n • (R *ᵥ θ n - c)) atTop (𝓝 h))
    (hVpsd : V.PosSemidef) (hM : (R * V * Rᵀ).PosDef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ n)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp) (a : ℝ) :
    Tendsto (fun n => P {ω | a < waldStat n R c (T n ω) (Vhat n ω)}) atTop
      (𝓝 (ncChiSq ((CFC.sqrt (R * V * Rᵀ))⁻¹ *ᵥ h) (Set.Ioi a))) := by
  have hR : IsUnit (R * V * Rᵀ).det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have ht := wald_local_tendsto R c h hdrift hR hT hV hVm
  have hlim := map_wald_local_limit R h hVpsd hM hL hlaw
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht.tendsto
    (E := Set.Ioi a) (by simp only [hlim, frontier_Ioi]; simp [ncChiSq_singleton])
  simp only [ProbabilityMeasure.coe_mk, hlim] at key
  refine key.congr fun n => ?_
  exact Measure.map_apply_of_aemeasurable (ht.forall_aemeasurable n) measurableSet_Ioi

/-- **Non-vacuity.** Testing `θ₁ = θ₂` (`r = (1, −1)`, `R = rᵀ`, `c = 0`) along the Pitman drift
`θₙ = δ/√n`, `δ = (1, 0)`, with `√n (θ̂ₙ − θₙ) ∼ N(0, I₂)` and `V̂ₙ = (1 + 1/(n+1)) I₂`: the drift
is `h = rᵀδ = 1`, `σ = √2`; the upper-tailed t-test has asymptotic local power
`P(N(1/√2, 1) > a)`, at least its size, the two-sided test `P(|N(1/√2, 1)| > a)`, and the Wald
test `P(ncChiSq(μ) > a)` with noncentrality `‖μ‖² = 1/2`. -/
theorem local_power_witness (a : ℝ) :
    let r : Fin 2 → ℝ := ![1, -1]
    let R : Matrix (Fin 1) (Fin 2) ℝ := rowMat r
    let V : Matrix (Fin 2) (Fin 2) ℝ := 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 V).map ofLp
    let Vhat : ℕ → (Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
      fun n _ => Matrix.of.symm ((1 + 1 / ((n : ℝ) + 1)) • V)
    let δ : Fin 2 → ℝ := ![1, 0]
    let θ : ℕ → Fin 2 → ℝ := fun n => (Real.sqrt n)⁻¹ • δ
    let T : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ := fun n ω => θ n + (Real.sqrt n)⁻¹ • ω
    let μ : Fin 1 → ℝ := (CFC.sqrt (R * V * Rᵀ))⁻¹ *ᵥ (R *ᵥ δ)
    ∃ _ : IsProbabilityMeasure P,
      0 < r ⬝ᵥ (V *ᵥ r) ∧ V.PosSemidef ∧ (R * V * Rᵀ).PosDef ∧
      Tendsto (fun n : ℕ => Real.sqrt n * (r ⬝ᵥ θ n - 0)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => Real.sqrt n • (R *ᵥ θ n - 0)) atTop (𝓝 (R *ᵥ δ)) ∧
      TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ n)) atTop id
        (fun _ => P) P ∧
      TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V) ∧ (∀ n, AEMeasurable (Vhat n) P) ∧
      Measurable (id : (Fin 2 → ℝ) → Fin 2 → ℝ) ∧ P.map id = (multivariateGaussian 0 V).map ofLp ∧
      Tendsto (fun n => P {ω | a < tStat n r 0 (T n ω) (Vhat n ω)}) atTop
        (𝓝 (gaussianReal (1 * (Real.sqrt 2)⁻¹) 1 {x | a < x})) ∧
      gaussianReal 0 1 {x | a < x} ≤ gaussianReal (1 * (Real.sqrt 2)⁻¹) 1 {x | a < x} ∧
      Tendsto (fun n => P {ω | a < |tStat n r 0 (T n ω) (Vhat n ω)|}) atTop
        (𝓝 (gaussianReal (1 * (Real.sqrt 2)⁻¹) 1 {x | a < |x|})) ∧
      Tendsto (fun n => P {ω | a < waldStat n R 0 (T n ω) (Vhat n ω)}) atTop
        (𝓝 (ncChiSq μ (Set.Ioi a))) ∧
      μ ⬝ᵥ μ = 1 / 2 := by
  intro r R V P Vhat δ θ T μ
  obtain ⟨hP, hpos, -, -, -, -, hV, hVm, hT0, -, -, -, -, -, -⟩ := test_power_witness a
  have hσ : r ⬝ᵥ (V *ᵥ r) = 2 := by
    simp [r, V, dotProduct, Fin.sum_univ_two]; norm_num
  have hM : R * V * Rᵀ = Matrix.of fun _ _ => 2 := by
    rw [rowMat_mul_mul_transpose, hσ]
  have hMpd : (R * V * Rᵀ).PosDef := by
    rw [hM]
    have : (Matrix.of fun _ _ => (2 : ℝ) : Matrix (Fin 1) (Fin 1) ℝ)
        = Matrix.diagonal (fun _ => 2) := by
      ext i j; fin_cases i; fin_cases j; rfl
    rw [this]
    exact PosDef.diagonal fun _ => by norm_num
  have hδ : r ⬝ᵥ δ = 1 := by simp [r, δ, dotProduct, Fin.sum_univ_two]
  have hev : ∀ᶠ n : ℕ in atTop, Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact mul_inv_cancel₀ (by rw [Real.sqrt_ne_zero']; exact_mod_cast hn)
  have hdt : Tendsto (fun n : ℕ => Real.sqrt n * (r ⬝ᵥ θ n - 0)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [θ, dotProduct_smul, smul_eq_mul, sub_zero, hδ, hn, mul_one]
  have hdw : Tendsto (fun n : ℕ => Real.sqrt n • (R *ᵥ θ n - 0)) atTop (𝓝 (R *ᵥ δ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [θ, mulVec_smul, sub_zero, smul_smul, hn, one_smul]
  have hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ n)) atTop id
      (fun _ => P) P := by
    have : (fun (n : ℕ) (ω : Fin 2 → ℝ) => Real.sqrt n • (T n ω - θ n))
        = fun (n : ℕ) ω => Real.sqrt n • ((Real.sqrt n)⁻¹ • ω - (0 : Fin 2 → ℝ)) := by
      funext n ω; simp only [T, add_sub_cancel_left, sub_zero]
    rw [this]; exact hT0
  have hpow := t_local_normal (θ := θ) (T := T) r 0 1 hdt hpos PosSemidef.one hT hV hVm
    measurable_id Measure.map_id
  rw [hσ] at hpow
  have hμ : μ ⬝ᵥ μ = 1 / 2 := by
    simp only [μ]
    rw [noncentrality_eq hMpd, hM, inv_fin_one_const]
    simp [R, rowMat, r, δ, dotProduct, mulVec, Fin.sum_univ_two]
  refine ⟨hP, hpos, PosSemidef.one, hMpd, hdt, hdw, hT, hV, hVm, measurable_id, Measure.map_id,
    hpow.2.1 a, ?_, hpow.2.2 a, ?_, hμ⟩
  · simpa using t_local_power_mono (Real.sqrt 2) (by positivity) (zero_le_one' ℝ) a
  · exact wald_local_power (θ := θ) (T := T) R 0 (R *ᵥ δ) hdw PosSemidef.one hMpd hT hV hVm
      measurable_id Measure.map_id a

end Noncentral

end Econ.Asymptotics
