/-
# Two-step (feasible efficient) GMM

Hansen (1982), Thm 3.2 and Lemma 4.2; Hayashi, *Econometrics* (2000), §3.5
and Prop. 3.6; Newey and McFadden (1994), §5.

**The procedure.** A first step yields a consistent estimate `Ŝₙ` of the long-run
moment variance `S`; the second step uses the weight `Ŵₙ = Ŝₙ⁻¹`.

**The results.** If `Ŝₙ →p S` with `S` positive definite, `Ĝₙ →p G` of full
column rank and `√n ĝₙ →d L`:

* `Ŵₙ →p S⁻¹` (`tendstoInMeasure_invFn`), so the rank condition holds in the limit;
* `√n (θ̂ₙ − θ₀) →d A L` with `A = (GᵀS⁻¹G)⁻¹GᵀS⁻¹`, and if `L ~ N(0, S)` this limit
  is `N(0, (GᵀS⁻¹G)⁻¹)`, the efficiency bound (`two_step_gmm`);
* Hansen's J statistic with the estimated weight converges to `Lᵀ Q L`, the
  efficient J form, whose mean is `l − k` when `L ~ N(0, S)` (`two_step_jtest`).

**Scope.** The first-step estimator and the construction of `Ŝₙ` from its
residuals are not modelled: consistency `Ŝₙ →p S` is a hypothesis, so these are
the results for efficient GMM with a consistently estimated weight (Hayashi
Prop. 3.5). The χ²(l − k) law of the J limit is not stated, since Mathlib has no
χ² distribution; its mean `l − k` is.
-/
module

public import EconLean.Econometrics.Asymptotics.JTest

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-- The matrix inverse in function form. -/
noncomputable def invFn (M : l → l → ℝ) : l → l → ℝ := Matrix.of.symm (Matrix.of M)⁻¹

lemma of_invFn (M : l → l → ℝ) : Matrix.of (invFn M) = (Matrix.of M)⁻¹ :=
  Matrix.of.apply_symm_apply _

lemma continuousAt_invFn {M₀ : l → l → ℝ} (h : IsUnit (Matrix.of M₀).det) :
    ContinuousAt (invFn (l := l)) M₀ :=
  continuousAt_matrix_inv (Matrix.of M₀) (by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ h.ne_zero)

lemma measurable_invFn : Measurable (invFn (l := l)) := measurable_inv_of

/-- **The estimated weight is consistent**: `Ŝₙ →p S` with `S` invertible implies
`Ŝₙ⁻¹ →p S⁻¹`. -/
theorem tendstoInMeasure_invFn {Shat : ℕ → Ω → l → l → ℝ} {S : Matrix l l ℝ}
    (hS : IsUnit S.det) (h : TendstoInMeasure P Shat atTop (fun _ => Matrix.of.symm S)) :
    TendstoInMeasure P (fun n ω => invFn (Shat n ω)) atTop (fun _ => invFn (Matrix.of.symm S)) :=
  tendstoInMeasure_comp_continuousAt h (continuousAt_invFn (by rw [Equiv.apply_symm_apply]; exact hS))

lemma of_invFn_symm (S : Matrix l l ℝ) : Matrix.of (invFn (Matrix.of.symm S)) = S⁻¹ := by
  rw [of_invFn]; rfl

lemma rank_two_step {S : Matrix l l ℝ} (hS : S.PosDef) {G : l → k → ℝ}
    (hG : Function.Injective (Matrix.of G *ᵥ ·)) :
    IsUnit (gram (G, invFn (Matrix.of.symm S))).det := by
  have := GMM.isUnit_det_gram hS.inv hG
  rwa [gram, of_invFn_symm]

/-- **Efficient GMM with an estimated weight** (Hansen 1982 Thm 3.2; Hayashi
Prop. 3.5), the second step of two-step GMM: with the weight `Ŵₙ = Ŝₙ⁻¹`, `Ŝₙ →p S` positive definite, `Ĝₙ →p G` of full
column rank and `√n ĝₙ →d L`, the estimator satisfies
`√n (θ̂ₙ − θ₀) →d A L`, `A = (GᵀS⁻¹G)⁻¹GᵀS⁻¹`; if `L ~ N(0, S)` the limit is
`N(0, (GᵀS⁻¹G)⁻¹)`. -/
theorem two_step_gmm [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Ghat : ℕ → Ω → l → k → ℝ} {Shat : ℕ → Ω → l → l → ℝ} {g : ℕ → Ω → l → ℝ}
    {G : l → k → ℝ} {S : Matrix l l ℝ} {θ₀ : k → ℝ} {L : Ω' → l → ℝ}
    (hS : S.PosDef) (hG : Function.Injective (Matrix.of G *ᵥ ·))
    (hGhat : TendstoInMeasure P Ghat atTop (fun _ => G))
    (hShat : TendstoInMeasure P Shat atTop (fun _ => Matrix.of.symm S))
    (hg : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • g n ω) atTop L
      (fun _ => P) P')
    (hGm : ∀ n, AEMeasurable (Ghat n) P) (hSm : ∀ n, AEMeasurable (Shat n) P)
    (hgm : ∀ n, AEMeasurable (g n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (GMM.estimator (Matrix.of (invFn (Shat n ω)))
        (Matrix.of (Ghat n ω)) (Matrix.of (Ghat n ω) *ᵥ θ₀ + g n ω) - θ₀)) atTop
      (fun ω => Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω) (fun _ => P) P' ∧
    (Measurable L → P'.map L = (multivariateGaussian 0 S).map ofLp →
      P'.map (fun ω => Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω)
        = (multivariateGaussian 0 ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹).map ofLp) :=
  ⟨gmm_asymptotic_normal (rank_two_step hS hG) hGhat
      (tendstoInMeasure_invFn ((isUnit_iff_isUnit_det _).mp hS.isUnit) hShat) hg hGm
      (fun n => measurable_invFn.comp_aemeasurable (hSm n)) hgm,
    fun hL hlaw => gmm_limit_law_efficient hL hS hlaw hG (of_invFn_symm S)⟩

/-- **The J test with an estimated weight** (Hansen 1982 Lemma 4.2; Hayashi
Prop. 3.6): under the assumptions of `two_step_gmm`, `Jₙ →d Lᵀ Q L` with `Q` the
efficient J form, and if `L ~ N(0, S)` its mean is `l − k`, the number of
overidentifying restrictions. -/
theorem two_step_jtest [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Ghat : ℕ → Ω → l → k → ℝ} {Shat : ℕ → Ω → l → l → ℝ} {g : ℕ → Ω → l → ℝ}
    {G : l → k → ℝ} {S : Matrix l l ℝ} {θ₀ : k → ℝ} {L : Ω' → l → ℝ}
    (hS : S.PosDef) (hG : Function.Injective (Matrix.of G *ᵥ ·))
    (hGhat : TendstoInMeasure P Ghat atTop (fun _ => G))
    (hShat : TendstoInMeasure P Shat atTop (fun _ => Matrix.of.symm S))
    (hg : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • g n ω) atTop L
      (fun _ => P) P')
    (hGm : ∀ n, AEMeasurable (Ghat n) P) (hSm : ∀ n, AEMeasurable (Shat n) P)
    (hgm : ∀ n, AEMeasurable (g n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => jStat n (Ghat n ω) (invFn (Shat n ω)) (Matrix.of (Ghat n ω) *ᵥ θ₀ + g n ω))
      atTop (fun ω => L ω ⬝ᵥ (jForm S (Matrix.of G) *ᵥ L ω)) (fun _ => P) P' ∧
    (Measurable L → P'.map L = (multivariateGaussian 0 S).map ofLp →
      ∫ ω, L ω ⬝ᵥ (jForm S (Matrix.of G) *ᵥ L ω) ∂P' = (Fintype.card l : ℝ) - Fintype.card k) := by
  have hW₀ := of_invFn_symm S
  refine ⟨?_, fun hL hlaw => ?_⟩
  · have := jStat_tendsto (θ₀ := θ₀) (rank_two_step hS hG) hGhat
      (tendstoInMeasure_invFn ((isUnit_iff_isUnit_det _).mp hS.isUnit) hShat) hg hGm
      (fun n => measurable_invFn.comp_aemeasurable (hSm n)) hgm
    simp only [jLimit_efficient hS hG hW₀] at this
    exact this
  · have hc : Continuous (fun y : l → ℝ => y ⬝ᵥ (jForm S (Matrix.of G) *ᵥ y)) := by fun_prop
    rw [← integral_map hL.aemeasurable hc.aestronglyMeasurable, hlaw]
    exact integral_jLimit hS hG

/-- **Non-vacuity of the two-step theorems**: with `l = 2` moments, `k = 1`
parameter, `G = (1, 1)ᵀ`, heteroskedastic `S = diag(1, 2)` (so the efficient
weight `S⁻¹` differs from the identity), `Ŝₙ = S`, `Ĝₙ = G` and
`ĝₙ = n^{-1/2} Z` for `Z ~ N(0, S)`, every hypothesis of
`two_step_gmm`/`two_step_jtest` holds, including the Gaussian law of the limit. -/
theorem two_step_witness :
    let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]
    let G : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 S).map ofLp
    IsProbabilityMeasure P ∧ S.PosDef ∧ Function.Injective (Matrix.of G *ᵥ ·) ∧
      TendstoInMeasure P (fun (_ : ℕ) (_ : Fin 2 → ℝ) => G) atTop (fun _ => G) ∧
      TendstoInMeasure P (fun (_ : ℕ) (_ : Fin 2 → ℝ) => Matrix.of.symm S) atTop
        (fun _ => Matrix.of.symm S) ∧
      (∃ _ : IsProbabilityMeasure P, TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n • ((Real.sqrt n)⁻¹ • ω)) atTop id (fun _ => P) P) ∧
      Measurable (id : (Fin 2 → ℝ) → Fin 2 → ℝ) ∧
      P.map id = (multivariateGaussian 0 S).map ofLp := by
  intro S G P
  have hofLp : Measurable (ofLp : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hP : IsProbabilityMeasure P := (Measure.isProbabilityMeasure_map_iff hofLp.aemeasurable).mpr inferInstance
  refine ⟨hP, PosDef.diagonal fun i => by fin_cases i <;> norm_num, ?_, tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds),
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds), ⟨hP, ?_⟩, measurable_id,
    Measure.map_id⟩
  · intro a b h
    have := congrFun h 0
    simp only [mulVec, dotProduct, of_apply, one_mul, Finset.univ_unique, Finset.sum_singleton,
      G] at this
    funext i; rw [Subsingleton.elim i 0]; exact this
  · refine ⟨fun n => by fun_prop, by fun_prop, ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt n ≠ 0 := by
      rw [Real.sqrt_ne_zero']; exact_mod_cast hn
    apply Subtype.ext
    simp only [smul_smul, mul_inv_cancel₀ hs, one_smul]
    rfl

end Econ.Asymptotics
