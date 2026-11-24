/-
# The multivariate delta method

van der Vaart, *Asymptotic Statistics* (1998), Thm 3.1; Hayashi, *Econometrics*
(2000), Lemma 2.5(b); Newey and McFadden (1994), §9.

**The result.** If `√n (Tₙ − θ) →d Z` in `ℝᵏ` and `g : ℝᵏ → ℝˡ` is (measurable
and) Fréchet differentiable at `θ` with derivative `g'`, then
`√n (g(Tₙ) − g(θ)) →d g'(Z)` (`delta_method_vec`). If `Z ~ N(0, Σ)` the limit is
`N(0, J Σ Jᵀ)` with `J` the Jacobian (`delta_method_vec_gaussian`). The rate is
`√n`; van der Vaart's general rate `rₙ → ∞` is not stated.

**Proof.** Write `√n (g(Tₙ) − g(θ)) = g'(Zₙ) + ‖Zₙ‖ ρ(Tₙ)` with
`Zₙ = √n (Tₙ − θ)` and the normalised remainder
`ρ(t) = (g(t) − g(θ) − g'(t − θ)) / ‖t − θ‖` (`ρ(θ) = 0`), continuous at `θ` by
differentiability. Since `Tₙ →p θ` (root-n consistency, `tendstoInMeasure_of_sqrt_pi`),
`ρ(Tₙ) →p 0`, and Slutsky's theorem applied to the continuous map
`(z, u) ↦ g'(z) + ‖z‖ u` gives the limit `g'(Z)`.
-/
module

public import EconLean.Econometrics.Asymptotics.DeltaMethod
public import EconLean.Econometrics.Asymptotics.GaussianLimits

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {k l : Type*} [Fintype k] [Fintype l]

/-- **Convergence in distribution to a constant implies convergence in
probability**, for random vectors. -/
theorem tendstoInMeasure_of_tendstoInDistribution_const_pi {X : ℕ → Ω → k → ℝ} {c : k → ℝ}
    (h : TendstoInDistribution X atTop (fun _ => c) (fun _ => P) P') :
    TendstoInMeasure P X atTop (fun _ => c) := by
  have h1 := h.continuous_comp (g := fun x => ‖x - c‖) (by fun_prop)
  have h2 : TendstoInDistribution (fun n ω => ‖X n ω - c‖) atTop (fun _ => (0 : ℝ))
      (fun _ => P) P' := by
    simpa [Function.comp_def] using h1
  have h3 := tendstoInMeasure_of_tendstoInDistribution_const h2
  rw [tendstoInMeasure_iff_norm] at h3 ⊢
  simpa using h3

/-- **Root-n consistency** for random vectors: if `√n (Tₙ − θ) →d Z` then
`Tₙ →p θ`. -/
theorem tendstoInMeasure_of_sqrt_pi {T : ℕ → Ω → k → ℝ} {θ : k → ℝ} {Z : Ω' → k → ℝ}
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ)) atTop Z
      (fun _ => P) P') :
    TendstoInMeasure P T atTop (fun _ => θ) := by
  have hprod := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (k → ℝ) × ℝ => p.2 • p.1) (by fun_prop)
    (tendstoInMeasure_const_seq (P := P) tendsto_inv_sqrt_nat) (fun _ => aemeasurable_const)
  simp only [zero_smul] at hprod
  have hp := tendstoInMeasure_of_tendstoInDistribution_const_pi hprod
  rw [tendstoInMeasure_iff_norm] at hp ⊢
  intro ε hε
  refine (hp ε hε).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  congr 1; ext ω
  have hs : Real.sqrt n ≠ 0 := by positivity
  simp only [Set.mem_ofPred_eq, sub_zero, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The normalised remainder `ρ(t) = (g(t) − g(θ) − g'(t − θ)) / ‖t − θ‖`,
`ρ(θ) = 0`. -/
noncomputable def remQuot (g : (k → ℝ) → l → ℝ) (g' : (k → ℝ) →L[ℝ] (l → ℝ)) (θ t : k → ℝ) :
    l → ℝ :=
  if t = θ then 0 else ‖t - θ‖⁻¹ • (g t - g θ - g' (t - θ))

lemma remQuot_continuousAt {g : (k → ℝ) → l → ℝ} {g' : (k → ℝ) →L[ℝ] (l → ℝ)} {θ : k → ℝ}
    (hd : HasFDerivAt g g' θ) : ContinuousAt (remQuot g g' θ) θ := by
  have ht := hasFDerivAt_iff_tendsto.mp hd
  have h0 : remQuot g g' θ θ = 0 := by simp [remQuot]
  rw [ContinuousAt, h0]
  refine squeeze_zero_norm (fun t => ?_) ht
  by_cases h : t = θ
  · subst h; simp [remQuot]
  · simp only [remQuot, h, ite_false, norm_smul, norm_inv, norm_norm]
    exact le_rfl

lemma remQuot_measurable {g : (k → ℝ) → l → ℝ} (hg : Measurable g)
    (g' : (k → ℝ) →L[ℝ] (l → ℝ)) (θ : k → ℝ) : Measurable (remQuot g g' θ) := by
  refine Measurable.ite (measurableSet_singleton θ) measurable_const ?_
  exact ((measurable_id.sub measurable_const).norm.inv).smul
    ((hg.sub measurable_const).sub (g'.continuous.measurable.comp (measurable_id.sub measurable_const)))

omit [Fintype l] in
lemma smul_sub_eq_remQuot (g : (k → ℝ) → l → ℝ) (g' : (k → ℝ) →L[ℝ] (l → ℝ)) (θ t : k → ℝ)
    (s : ℝ) (hs : 0 ≤ s) :
    s • (g t - g θ) = g' (s • (t - θ)) + ‖s • (t - θ)‖ • remQuot g g' θ t := by
  by_cases h : t = θ
  · subst h; simp
  · have hn : ‖t - θ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
    simp only [remQuot, h, ite_false, norm_smul, Real.norm_of_nonneg hs, smul_smul,
      mul_assoc, mul_inv_cancel₀ hn, mul_one, map_smul]
    rw [← smul_add]
    congr 1
    abel

/-- **Multivariate delta method** (van der Vaart Thm 3.1; Hayashi Lemma 2.5(b)): if
`√n (Tₙ − θ) →d Z` and `g` is measurable and differentiable at `θ` with
derivative `g'`, then `√n (g(Tₙ) − g(θ)) →d g'(Z)`. -/
theorem delta_method_vec {T : ℕ → Ω → k → ℝ} {θ : k → ℝ} {Z : Ω' → k → ℝ}
    (hT : ∀ n, AEMeasurable (T n) P)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ)) atTop Z
      (fun _ => P) P')
    {g : (k → ℝ) → l → ℝ} (hg : Measurable g) {g' : (k → ℝ) →L[ℝ] (l → ℝ)}
    (hd : HasFDerivAt g g' θ) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (g (T n ω) - g θ)) atTop
      (fun ω => g' (Z ω)) (fun _ => P) P' := by
  have hq := tendstoInMeasure_comp_continuousAt (tendstoInMeasure_of_sqrt_pi h)
    (remQuot_continuousAt hd)
  have hq0 : remQuot g g' θ θ = 0 := by simp [remQuot]
  rw [hq0] at hq
  have := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (k → ℝ) × (l → ℝ) => g' p.1 + ‖p.1‖ • p.2) (by fun_prop) hq
    (fun n => (remQuot_measurable hg g' θ).comp_aemeasurable (hT n))
  simp only [smul_zero, add_zero] at this
  convert this using 2 with n
  funext ω
  exact smul_sub_eq_remQuot g g' θ (T n ω) _ (Real.sqrt_nonneg _)

omit [IsProbabilityMeasure P'] in
/-- **Law of the delta-method limit**: if `Z ~ N(0, Σ)` then `g'(Z)` has law
`N(0, J Σ Jᵀ)`, `J` the Jacobian matrix of `g'` (a linear image of a Gaussian). -/
theorem delta_method_gaussian [DecidableEq k] [DecidableEq l] {Z : Ω' → k → ℝ}
    (hZ : Measurable Z) {S : Matrix k k ℝ} (hS : S.PosSemidef)
    (hlaw : P'.map Z = (multivariateGaussian 0 S).map WithLp.ofLp)
    (g' : (k → ℝ) →L[ℝ] (l → ℝ)) :
    P'.map (fun ω => g' (Z ω))
      = (multivariateGaussian 0 (LinearMap.toMatrix' (g' : (k → ℝ) →ₗ[ℝ] (l → ℝ)) * S *
          Matrix.transpose (LinearMap.toMatrix' (g' : (k → ℝ) →ₗ[ℝ] (l → ℝ))))).map
          WithLp.ofLp := by
  rw [← map_mulVec_of_gaussian hZ hS hlaw]
  simp only [LinearMap.toMatrix'_mulVec]
  rfl

/-- **Delta method, Gaussian form** (Hayashi Lemma 2.5(b)): if `√n (Tₙ − θ) →d Z`
with `Z ~ N(0, Σ)` and `g` is differentiable at `θ`, then
`√n (g(Tₙ) − g(θ)) →d g'(Z)` and `g'(Z) ~ N(0, J Σ Jᵀ)`. -/
theorem delta_method_vec_gaussian [DecidableEq k] [DecidableEq l] {T : ℕ → Ω → k → ℝ}
    {θ : k → ℝ} {Z : Ω' → k → ℝ} (hT : ∀ n, AEMeasurable (T n) P)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ)) atTop Z
      (fun _ => P) P')
    (hZ : Measurable Z) {S : Matrix k k ℝ} (hS : S.PosSemidef)
    (hlaw : P'.map Z = (multivariateGaussian 0 S).map WithLp.ofLp)
    {g : (k → ℝ) → l → ℝ} (hg : Measurable g) {g' : (k → ℝ) →L[ℝ] (l → ℝ)}
    (hd : HasFDerivAt g g' θ) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (g (T n ω) - g θ)) atTop
      (fun ω => g' (Z ω)) (fun _ => P) P' ∧
    P'.map (fun ω => g' (Z ω))
      = (multivariateGaussian 0 (LinearMap.toMatrix' (g' : (k → ℝ) →ₗ[ℝ] (l → ℝ)) * S *
          Matrix.transpose (LinearMap.toMatrix' (g' : (k → ℝ) →ₗ[ℝ] (l → ℝ))))).map
          WithLp.ofLp :=
  ⟨delta_method_vec hT h hg hd, delta_method_gaussian hZ hS hlaw g'⟩

end Econ.Asymptotics
