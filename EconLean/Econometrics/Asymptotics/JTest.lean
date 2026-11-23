/-
# Hansen's J test of overidentifying restrictions

Hansen, "Large sample properties of generalized method of moments estimators",
*Econometrica* (1982), Lemma 4.2; Hayashi, *Econometrics* (2000), Prop. 3.6;
Newey and McFadden (1994), §9.5.

**The statistic.** In linear GMM with `l` moments and `k` parameters, the
moment residual at the estimate is `m̂ₙ = ŝₙ − Ŝₙ θ̂ₙ` and
`Jₙ = (√n m̂ₙ)ᵀ Ŵₙ (√n m̂ₙ)`.

**The results.**

* **Limit** (`jStat_tendsto`): if `Ŝₙ →p G`, `Ŵₙ →p W`, the rank condition holds
  and `√n ĝₙ →d L`, then `Jₙ →d (M L)ᵀ W (M L)` with `M = I − G (GᵀWG)⁻¹ GᵀW`.
* **Algebra of the efficient case** (`W = S⁻¹`, `S` positive definite, `G` of full
  column rank). Let `V = (GᵀS⁻¹G)⁻¹` and `Q = S⁻¹ − S⁻¹GVGᵀS⁻¹`. Then
  `MᵀS⁻¹M = Q` (`jForm_eq`), `QG = 0`, `QSQ = Q` (so `S^{1/2} Q S^{1/2}` is an
  orthogonal projection) and `tr(QS) = l − k` (`trace_jForm_mul`): the limit
  `Lᵀ Q L` with `L ~ N(0, S)` is a quadratic form in an idempotent of rank
  `l − k`, i.e. `χ²(l − k)`; its mean is `l − k` (`integral_jLimit`).

The χ² law itself (Mathlib has no χ² distribution) is not stated; the mean and
the idempotent-of-rank-`l−k` structure are.
-/
module

public import EconLean.Econometrics.Asymptotics.GaussianLimits

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-! ### Algebra -/

section Algebra

variable {S : Matrix l l ℝ} {G : Matrix l k ℝ}

/-- The residual-maker `M = I − G (GᵀWG)⁻¹ GᵀW`. -/
noncomputable def residMaker (W : Matrix l l ℝ) (G : Matrix l k ℝ) : Matrix l l ℝ :=
  1 - G * ((Gᵀ * W * G)⁻¹ * (Gᵀ * W))

/-- The efficient J-test form `Q = S⁻¹ − S⁻¹ G (GᵀS⁻¹G)⁻¹ Gᵀ S⁻¹`. -/
noncomputable def jForm (S : Matrix l l ℝ) (G : Matrix l k ℝ) : Matrix l l ℝ :=
  S⁻¹ - S⁻¹ * G * (Gᵀ * S⁻¹ * G)⁻¹ * Gᵀ * S⁻¹

lemma gram_unit (hS : S.PosDef) (hG : Function.Injective (G *ᵥ ·)) :
    IsUnit (Gᵀ * S⁻¹ * G).det :=
  GMM.isUnit_det_gram hS.inv hG

/-- The projection-type matrix `P = G (GᵀS⁻¹G)⁻¹ GᵀS⁻¹`, so that `M = I − P`. -/
noncomputable def projP (S : Matrix l l ℝ) (G : Matrix l k ℝ) : Matrix l l ℝ :=
  G * ((Gᵀ * S⁻¹ * G)⁻¹ * (Gᵀ * S⁻¹))

lemma residMaker_eq : residMaker S⁻¹ G = 1 - projP S G := rfl

lemma jForm_eq_projP : jForm S G = S⁻¹ - S⁻¹ * projP S G := by
  simp only [jForm, projP, Matrix.mul_assoc]

lemma projP_mul_self (hS : S.PosDef) (hG : Function.Injective (G *ᵥ ·)) :
    projP S G * projP S G = projP S G := by
  have hVG : (Gᵀ * S⁻¹ * G)⁻¹ * (Gᵀ * S⁻¹ * G) = 1 := nonsing_inv_mul _ (gram_unit hS hG)
  calc projP S G * projP S G
      = G * ((Gᵀ * S⁻¹ * G)⁻¹ * (Gᵀ * S⁻¹ * G)) * ((Gᵀ * S⁻¹ * G)⁻¹ * (Gᵀ * S⁻¹)) := by
        simp only [projP, Matrix.mul_assoc]
    _ = projP S G := by rw [hVG, Matrix.mul_one]; rfl

lemma transpose_projP_mul (hS : S.PosDef) :
    (projP S G)ᵀ * S⁻¹ = S⁻¹ * projP S G := by
  have hSi : S⁻¹ᵀ = S⁻¹ := GMM.transpose_eq_of_posDef hS.inv
  have hV : (Gᵀ * S⁻¹ * G)⁻¹ᵀ = (Gᵀ * S⁻¹ * G)⁻¹ := GMM.transpose_inv_gram hSi G
  simp only [projP, transpose_mul, hSi, transpose_transpose]
  rw [hV]
  simp only [Matrix.mul_assoc]

lemma jForm_transpose (hS : S.PosDef) : (jForm S G)ᵀ = jForm S G := by
  have hSi : S⁻¹ᵀ = S⁻¹ := GMM.transpose_eq_of_posDef hS.inv
  rw [jForm_eq_projP, transpose_sub, transpose_mul, hSi, transpose_projP_mul hS]

/-- `MᵀS⁻¹M = Q` for the efficient weight. -/
theorem jForm_eq (hS : S.PosDef) (hG : Function.Injective (G *ᵥ ·)) :
    (residMaker S⁻¹ G)ᵀ * S⁻¹ * residMaker S⁻¹ G = jForm S G := by
  have hP := projP_mul_self hS hG
  have hMt : (1 - projP S G)ᵀ * S⁻¹ = S⁻¹ * (1 - projP S G) := by
    rw [transpose_sub, transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, transpose_projP_mul hS]
  have hMM : (1 - projP S G) * (1 - projP S G) = 1 - projP S G := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hP]
    abel
  rw [residMaker_eq, hMt, Matrix.mul_assoc, hMM, jForm_eq_projP, Matrix.mul_sub, Matrix.mul_one]

/-- `Q G = 0`: the J statistic does not depend on `θ₀`. -/
theorem jForm_mul_G (hS : S.PosDef) (hG : Function.Injective (G *ᵥ ·)) : jForm S G * G = 0 := by
  have hu := gram_unit hS hG
  rw [jForm, Matrix.sub_mul]
  have : S⁻¹ * G * (Gᵀ * S⁻¹ * G)⁻¹ * Gᵀ * S⁻¹ * G = S⁻¹ * G := by
    rw [Matrix.mul_assoc _ Gᵀ, Matrix.mul_assoc _ (Gᵀ * S⁻¹), Matrix.mul_assoc (S⁻¹ * G),
      nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [this, sub_self]

/-- `Q S Q = Q`. -/
theorem jForm_mul_S_mul (hS : S.PosDef) (hG : Function.Injective (G *ᵥ ·)) :
    jForm S G * S * jForm S G = jForm S G := by
  have hSu : IsUnit S.det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have hQG := jForm_mul_G hS hG
  have hQS : jForm S G * S = 1 - S⁻¹ * G * (Gᵀ * S⁻¹ * G)⁻¹ * Gᵀ := by
    rw [jForm, Matrix.sub_mul, nonsing_inv_mul _ hSu, Matrix.mul_assoc _ S⁻¹ S,
      nonsing_inv_mul _ hSu, Matrix.mul_one]
  rw [hQS, Matrix.sub_mul, Matrix.one_mul]
  have hGQ : Gᵀ * jForm S G = 0 := by
    rw [← jForm_transpose hS, ← transpose_mul, hQG, transpose_zero]
  rw [Matrix.mul_assoc _ Gᵀ, hGQ, Matrix.mul_zero, sub_zero]

/-- `tr(QS) = l − k`: the degrees of freedom of the J test. -/
theorem trace_jForm_mul (hS : S.PosDef) (hG : Function.Injective (G *ᵥ ·)) :
    (jForm S G * S).trace = (Fintype.card l : ℝ) - Fintype.card k := by
  have hSu : IsUnit S.det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have hu := gram_unit hS hG
  have hQS : jForm S G * S = 1 - S⁻¹ * G * (Gᵀ * S⁻¹ * G)⁻¹ * Gᵀ := by
    rw [jForm, Matrix.sub_mul, nonsing_inv_mul _ hSu, Matrix.mul_assoc _ S⁻¹ S,
      nonsing_inv_mul _ hSu, Matrix.mul_one]
  rw [hQS, trace_sub, trace_one, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
    ← Matrix.mul_assoc Gᵀ, nonsing_inv_mul _ hu, trace_one]

end Algebra

/-! ### The limit of the J statistic -/

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

/-- The J statistic `(√n m̂)ᵀ Ŵ (√n m̂)` with `m̂ = ŝ − Ŝ θ̂`. -/
noncomputable def jStat (n : ℕ) (S : l → k → ℝ) (W : l → l → ℝ) (s : l → ℝ) : ℝ :=
  let m := Real.sqrt n • (s - Matrix.of S *ᵥ GMM.estimator (Matrix.of W) (Matrix.of S) s)
  m ⬝ᵥ (Matrix.of W *ᵥ m)

/-- The residual-maker in function form, as a function of `(S, W)`. -/
noncomputable def residMakerFn (p : (l → k → ℝ) × (l → l → ℝ)) : l → l → ℝ :=
  fun i j => (1 : Matrix l l ℝ) i j - ∑ m, p.1 i m * gmmA p m j

lemma residMakerFn_eq (p : (l → k → ℝ) × (l → l → ℝ)) :
    Matrix.of (residMakerFn p) = residMaker (Matrix.of p.2) (Matrix.of p.1) := by
  ext i j
  simp only [residMakerFn, residMaker, gmmA, gram, cross, of_apply]
  rfl

lemma residMakerFn_mulVec (p : (l → k → ℝ) × (l → l → ℝ)) (x : l → ℝ) :
    Matrix.of (residMakerFn p) *ᵥ x = x - Matrix.of p.1 *ᵥ (Matrix.of (gmmA p) *ᵥ x) := by
  have : Matrix.of (residMakerFn p) = 1 - Matrix.of p.1 * Matrix.of (gmmA p) := by
    ext i j; simp [residMakerFn, Matrix.mul_apply]
  rw [this, sub_mulVec, one_mulVec, mulVec_mulVec]

lemma continuousAt_residMakerFn {p₀ : (l → k → ℝ) × (l → l → ℝ)} (h : IsUnit (gram p₀).det) :
    ContinuousAt (residMakerFn (k := k) (l := l)) p₀ := by
  have hA := continuousAt_gmmA h
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  refine continuousAt_const.sub (tendsto_finsetSum _ fun m _ => ContinuousAt.mul ?_ ?_)
  · exact ((continuous_apply m).comp ((continuous_apply i).comp continuous_fst)).continuousAt
  · exact ((continuous_apply j).comp (continuous_apply m)).continuousAt.comp hA

lemma measurable_residMakerFn : Measurable (residMakerFn (k := k) (l := l)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  refine measurable_const.sub (Finset.measurable_sum _ fun m _ => Measurable.mul ?_ ?_)
  · exact (measurable_pi_apply m).comp ((measurable_pi_apply i).comp measurable_fst)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply m).comp measurable_gmmA)

/-- On the rank condition the scaled residual is `M(Ŝ, Ŵ) · √n ĝ`. -/
lemma resid_eq (n : ℕ) (S : l → k → ℝ) (W : l → l → ℝ) (h : IsUnit (gram (S, W)).det)
    (θ₀ : k → ℝ) (g : l → ℝ) :
    Real.sqrt n • ((Matrix.of S *ᵥ θ₀ + g) - Matrix.of S *ᵥ
        GMM.estimator (Matrix.of W) (Matrix.of S) (Matrix.of S *ᵥ θ₀ + g))
      = Matrix.of (residMakerFn (S, W)) *ᵥ (Real.sqrt n • g) := by
  have he := estimator_sub S W h θ₀ g
  have : GMM.estimator (Matrix.of W) (Matrix.of S) (Matrix.of S *ᵥ θ₀ + g)
      = θ₀ + Matrix.of (gmmA (S, W)) *ᵥ g := by rw [← he]; abel
  rw [this, residMakerFn_mulVec, mulVec_add]
  simp only [smul_sub, smul_add, mulVec_smul]
  abel

/-- **Limit of the J statistic** (Hansen 1982 Lemma 4.2; Hayashi Prop. 3.6): with
`Ŝₙ →p G`, `Ŵₙ →p W`, the rank condition and `√n ĝₙ →d L`,
`Jₙ →d (M L)ᵀ W (M L)`, `M = I − G (GᵀWG)⁻¹ GᵀW`. Here `S n` is the sample
Jacobian `Ŝₙ` (not the long-run variance, which is `S` in `jForm`). -/
theorem jStat_tendsto [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {S : ℕ → Ω → l → k → ℝ} {W : ℕ → Ω → l → l → ℝ}
    {g : ℕ → Ω → l → ℝ} {G : l → k → ℝ} {W₀ : l → l → ℝ} {θ₀ : k → ℝ} {L : Ω' → l → ℝ}
    (hrank : IsUnit (gram (G, W₀)).det)
    (hS : TendstoInMeasure P S atTop (fun _ => G))
    (hW : TendstoInMeasure P W atTop (fun _ => W₀))
    (hg : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • g n ω) atTop L
      (fun _ => P) P')
    (hSm : ∀ n, AEMeasurable (S n) P) (hWm : ∀ n, AEMeasurable (W n) P)
    (hgm : ∀ n, AEMeasurable (g n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => jStat n (S n ω) (W n ω) (Matrix.of (S n ω) *ᵥ θ₀ + g n ω)) atTop
      (fun ω => (Matrix.of (residMakerFn (G, W₀)) *ᵥ L ω) ⬝ᵥ
        (Matrix.of W₀ *ᵥ (Matrix.of (residMakerFn (G, W₀)) *ᵥ L ω))) (fun _ => P) P' := by
  have hSW := tendstoInMeasure_prodMk (E := l → k → ℝ) (F := l → l → ℝ) hS hW
  have hM := tendstoInMeasure_comp_continuousAt hSW (continuousAt_residMakerFn hrank)
  have hMW := tendstoInMeasure_prodMk (E := l → l → ℝ) (F := l → l → ℝ) hM hW
  have hMWm : ∀ n, AEMeasurable (fun ω => (residMakerFn (S n ω, W n ω), W n ω)) P := fun n =>
    (measurable_residMakerFn.comp_aemeasurable ((hSm n).prodMk (hWm n))).prodMk (hWm n)
  have hq : Continuous (fun p : (l → ℝ) × ((l → l → ℝ) × (l → l → ℝ)) =>
      (Matrix.of p.2.1 *ᵥ p.1) ⬝ᵥ (Matrix.of p.2.2 *ᵥ (Matrix.of p.2.1 *ᵥ p.1))) := by
    fun_prop
  have hX := hg.continuous_comp_prodMk_of_tendstoInMeasure_const hq hMW hMWm
  obtain ⟨δ, hδ, hball⟩ := exists_ball_rank hrank
  have hsub := tendstoInMeasure_sub_of_eq_near (E := ℝ)
    (Y := fun (n : ℕ) ω => jStat n (S n ω) (W n ω) (Matrix.of (S n ω) *ᵥ θ₀ + g n ω))
    (X := fun (n : ℕ) ω => (Matrix.of (residMakerFn (S n ω, W n ω)) *ᵥ (Real.sqrt n • g n ω)) ⬝ᵥ
      (Matrix.of (W n ω) *ᵥ (Matrix.of (residMakerFn (S n ω, W n ω)) *ᵥ
        (Real.sqrt n • g n ω)))) hSW hδ (fun n ω hd => by
      simp only [jStat]
      rw [resid_eq n _ _ (hball _ hd)])
  have hY : ∀ n : ℕ, AEMeasurable
      (fun ω => jStat n (S n ω) (W n ω) (Matrix.of (S n ω) *ᵥ θ₀ + g n ω)) P := by
    intro n
    have hE : ∀ ω, jStat n (S n ω) (W n ω) (Matrix.of (S n ω) *ᵥ θ₀ + g n ω)
        = (fun p : (k → l → ℝ) × (l → k → ℝ) × (l → l → ℝ) × (l → ℝ) =>
          let m := Real.sqrt n • ((Matrix.of p.2.1 *ᵥ θ₀ + p.2.2.2) - Matrix.of p.2.1 *ᵥ
            (Matrix.of p.1 *ᵥ (Matrix.of p.2.1 *ᵥ θ₀ + p.2.2.2)))
          m ⬝ᵥ (Matrix.of p.2.2.1 *ᵥ m)) (gmmA (S n ω, W n ω), S n ω, W n ω, g n ω) := by
      intro ω; simp only [jStat, estimator_eq_gmmA]
    simp_rw [hE]
    have hc : Continuous (fun p : (k → l → ℝ) × (l → k → ℝ) × (l → l → ℝ) × (l → ℝ) =>
          let m := Real.sqrt n • ((Matrix.of p.2.1 *ᵥ θ₀ + p.2.2.2) - Matrix.of p.2.1 *ᵥ
            (Matrix.of p.1 *ᵥ (Matrix.of p.2.1 *ᵥ θ₀ + p.2.2.2)))
          m ⬝ᵥ (Matrix.of p.2.2.1 *ᵥ m)) := by
      fun_prop
    have h2 := hc.measurable.comp_aemeasurable
      ((measurable_gmmA.comp_aemeasurable ((hSm n).prodMk (hWm n))).prodMk
        ((hSm n).prodMk ((hWm n).prodMk (hgm n))))
    exact h2
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX hsub hY

/-- With the efficient weight `W = S⁻¹`, the J limit is the quadratic form
`Lᵀ Q L` in the efficient J form `Q` (`jForm_eq`). -/
theorem jLimit_efficient {S : Matrix l l ℝ} (hS : S.PosDef) {G : l → k → ℝ}
    (hG : Function.Injective (Matrix.of G *ᵥ ·)) {W₀ : l → l → ℝ} (hW₀ : Matrix.of W₀ = S⁻¹)
    (x : l → ℝ) :
    (Matrix.of (residMakerFn (G, W₀)) *ᵥ x) ⬝ᵥ
        (Matrix.of W₀ *ᵥ (Matrix.of (residMakerFn (G, W₀)) *ᵥ x))
      = x ⬝ᵥ (jForm S (Matrix.of G) *ᵥ x) := by
  rw [residMakerFn_eq]
  simp only
  rw [hW₀, GMM.mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, jForm_eq hS hG]

/-! ### Mean of the limit -/

omit [DecidableEq k] in
/-- Second moments of a centred multivariate Gaussian: `E[xᵢ xⱼ] = Sᵢⱼ`. -/
lemma integral_mul_multivariateGaussian {S : Matrix l l ℝ} (hS : S.PosSemidef) (i j : l) :
    ∫ x, x i * x j ∂(multivariateGaussian 0 S) = S i j := by
  have hmean : ∀ i, ∫ x, x i ∂(multivariateGaussian (0 : EuclideanSpace ℝ l) S) = 0 := by
    intro i
    have h := (EuclideanSpace.proj i : EuclideanSpace ℝ l →L[ℝ] ℝ).integral_comp_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ l) S))
    simpa using h
  rw [← covariance_eval_multivariateGaussian (μ := 0) hS i j, covariance]
  simp [hmean]

lemma integrable_mul_eval {S : Matrix l l ℝ} (i j : l) :
    Integrable (fun x : EuclideanSpace ℝ l => x i * x j) (multivariateGaussian 0 S) := by
  have h2 : ∀ i, MemLp (fun x : EuclideanSpace ℝ l => x i) 2 (multivariateGaussian 0 S) :=
    fun i => (EuclideanSpace.proj i : EuclideanSpace ℝ l →L[ℝ] ℝ).comp_memLp'
      (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ l) S))
  exact (h2 i).integrable_mul (h2 j)

/-- **Mean of the J limit**: if `L ~ N(0, S)` with `S` positive definite and the
weight is efficient, `E[Lᵀ Q L] = tr(QS) = l − k`, the mean of `χ²(l − k)`. -/
theorem integral_jLimit {S : Matrix l l ℝ} (hS : S.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) :
    ∫ y, y ⬝ᵥ (jForm S G *ᵥ y) ∂((multivariateGaussian 0 S).map ofLp)
      = (Fintype.card l : ℝ) - Fintype.card k := by
  rw [integral_map (PiLp.continuous_ofLp 2 _).aemeasurable (by fun_prop)]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  have hint : ∀ i j, Integrable (fun x : EuclideanSpace ℝ l => ofLp x i * (jForm S G i j * ofLp x j))
      (multivariateGaussian 0 S) := fun i j =>
    ((integrable_mul_eval (S := S) i j).const_mul (jForm S G i j)).congr
      (Eventually.of_forall fun x => by simp only; ring)
  have hval : ∀ i j, ∫ x : EuclideanSpace ℝ l, ofLp x i * (jForm S G i j * ofLp x j)
      ∂(multivariateGaussian 0 S) = jForm S G i j * S j i := by
    intro i j
    have hc : (fun x : EuclideanSpace ℝ l => ofLp x i * (jForm S G i j * ofLp x j))
        = fun x => jForm S G i j * (x i * x j) := by funext x; simp only; ring
    have hSt : Sᵀ = S := GMM.transpose_eq_of_posDef hS
    rw [hc, integral_const_mul, integral_mul_multivariateGaussian hS.posSemidef]
    exact congrArg _ (congrFun (congrFun hSt j) i)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j]
  simp_rw [hval]
  rw [← trace_jForm_mul hS hG, trace]
  simp [Matrix.mul_apply]

end Econ.Asymptotics
