/-
# Feasible two-step GMM: the first step and the residual-based weight

Hansen (1982), Thm 3.2 and Lemma 4.2; White (1980); Hayashi, *Econometrics* (2000),
Prop. 3.4–3.6 and §3.5; Newey and McFadden (1994), §4.3.

**The model.** Linear moment conditions `E[zᵢ(yᵢ − xᵢᵀθ₀)] = 0` with `l`
instruments `zᵢ` and `k` regressors `xᵢ`. A sample of size `n` gives
`Ĝ = n⁻¹Σzᵢxᵢᵀ`, `n⁻¹Σzᵢyᵢ = Ĝθ₀ + ĝ(θ₀)` (`sampleZY_eq`). The first step uses
any weight `Ŵ₁ →p W₁` (e.g. `I` or `(n⁻¹Σzᵢzᵢᵀ)⁻¹` for 2SLS); the second step
uses `Ŝ(θ̃)⁻¹`, where `Ŝ(θ) = n⁻¹Σ(yᵢ − xᵢᵀθ)²zᵢzᵢᵀ` is the heteroskedasticity-robust
variance estimator built from first-step residuals.

**The results.**

* `Ŝ(θ)` is a quadratic polynomial in `θ − θ₀` with sample-moment coefficients
  (`sHat_eq_expandS`). Hence, if `Ŝ(θ₀) →p S`, the cross and fourth-order
  moments converge, and `θ̃ →p θ₀`, then `Ŝ(θ̃) →p S` (`sHat_consistent`).
* **Feasible two-step GMM** (`two_step_feasible`): the first step is consistent,
  so `Ŝ(θ̃)⁻¹ →p S⁻¹`, and the two-step estimator attains the efficient limit
  `N(0, (GᵀS⁻¹G)⁻¹)`; its J statistic has the efficient J limit with mean `l − k`.
* A concrete data-generating process satisfies every hypothesis
  (`two_step_feasible_witness`). It is just-identified (`l = k = 1`), so it shows
  the hypotheses are jointly satisfiable at the data level but does not exercise
  the weighting; the overidentified abstract case is covered by `two_step_witness`
  (`l = 2`, `S = diag(1, 2)`). Its CLT holds exactly rather than in the limit.

**Scope.** The laws of large numbers for the sample moments and the CLT for
`√n ĝ(θ₀)` are hypotheses, as in `GMMAsymptotics.lean`. Observations are
indexed by `Fin n`; no i.i.d. structure is imposed.
-/
module

public import EconLean.Econometrics.Asymptotics.TwoStepGMM
public import EconLean.Econometrics.Asymptotics.DeltaMethodVec

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {k l : Type*} [Fintype k] [Fintype l] {N : ℕ}

/-- The sample residual-weighted second moment `Ŝ(θ) = n⁻¹ Σᵢ (yᵢ − xᵢᵀθ)² zᵢzᵢᵀ`. -/
noncomputable def sHat (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) (y : Fin N → ℝ) (θ : k → ℝ) :
    l → l → ℝ :=
  fun a b => (N : ℝ)⁻¹ * ∑ i, (y i - x i ⬝ᵥ θ) ^ 2 * (z i a * z i b)

/-- The cross moment `n⁻¹ Σᵢ uᵢ xᵢ_c zᵢzᵢᵀ` at `θ₀`. -/
noncomputable def sCross (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) (y : Fin N → ℝ) (θ₀ : k → ℝ) :
    l → l → k → ℝ :=
  fun a b c => (N : ℝ)⁻¹ * ∑ i, (y i - x i ⬝ᵥ θ₀) * x i c * (z i a * z i b)

/-- The fourth-order moment `n⁻¹ Σᵢ xᵢ_c xᵢ_e zᵢzᵢᵀ`. -/
noncomputable def sQuad (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) : l → l → k → k → ℝ :=
  fun a b c e => (N : ℝ)⁻¹ * ∑ i, x i c * x i e * (z i a * z i b)

/-- The quadratic expansion `M₀ − 2 M₁[d] + M₂[d, d]`. -/
def expandS (M0 : l → l → ℝ) (M1 : l → l → k → ℝ) (M2 : l → l → k → k → ℝ) (d : k → ℝ) :
    l → l → ℝ :=
  fun a b => M0 a b - 2 * ∑ c, M1 a b c * d c + ∑ c, ∑ e, M2 a b c e * (d c * d e)

omit [Fintype l] in
lemma sHat_eq_expandS (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) (y : Fin N → ℝ) (θ₀ θ : k → ℝ) :
    sHat z x y θ = expandS (sHat z x y θ₀) (sCross z x y θ₀) (sQuad z x) (θ - θ₀) := by
  funext a b
  simp only [sHat, expandS, sCross, sQuad]
  have hres : ∀ i, y i - x i ⬝ᵥ θ = (y i - x i ⬝ᵥ θ₀) - ∑ c, x i c * (θ - θ₀) c := by
    intro i; simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring
  simp_rw [hres]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => arg 1; arg 2; rw [Finset.sum_comm]
  conv_rhs => arg 2; arg 2; ext c; rw [Finset.sum_comm]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  set u := y i - x i ⬝ᵥ θ₀
  set w := z i a * z i b
  set d := θ - θ₀
  have hs1 : ∑ c, 2 * ((N : ℝ)⁻¹ * (u * x i c * w) * d c)
      = 2 * (N : ℝ)⁻¹ * u * w * ∑ c, x i c * d c := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  have hs2 : ∑ c, ∑ e, (N : ℝ)⁻¹ * (x i c * x i e * w) * (d c * d e)
      = (N : ℝ)⁻¹ * w * ((∑ c, x i c * d c) * ∑ e, x i e * d e) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
  rw [hs1, hs2]; ring

omit [Fintype l] in
lemma expandS_zero (M0 : l → l → ℝ) (M1 : l → l → k → ℝ) (M2 : l → l → k → k → ℝ) :
    expandS M0 M1 M2 0 = M0 := by
  funext a b; simp [expandS]

omit [Fintype l] in
lemma continuous_expandS : Continuous (fun p : ((l → l → ℝ) × (l → l → k → ℝ) ×
    (l → l → k → k → ℝ)) × (k → ℝ) => expandS p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold expandS; fun_prop

omit [Fintype l] in
lemma continuous_sHat : Continuous (fun p : (Fin N → l → ℝ) × (Fin N → k → ℝ) × (Fin N → ℝ) ×
    (k → ℝ) => sHat p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold sHat dotProduct; fun_prop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Consistency of the residual-based variance estimator** (White 1980; Hayashi
Prop. 3.4 / §3.5): if the sample moments at the true parameter converge,
`Ŝₙ(θ₀) →p S`, the cross and fourth-order moments converge (to any limits), and
`θ̃ₙ →p θ₀`, then `Ŝₙ(θ̃ₙ) →p S`. -/
theorem sHat_consistent {z : (n : ℕ) → Ω → Fin n → l → ℝ} {x : (n : ℕ) → Ω → Fin n → k → ℝ}
    {y : (n : ℕ) → Ω → Fin n → ℝ} {θt : ℕ → Ω → k → ℝ} {θ₀ : k → ℝ} {S : l → l → ℝ}
    {A1 : l → l → k → ℝ} {A2 : l → l → k → k → ℝ}
    (h0 : TendstoInMeasure P (fun n ω => sHat (z n ω) (x n ω) (y n ω) θ₀) atTop (fun _ => S))
    (h1 : TendstoInMeasure P (fun n ω => sCross (z n ω) (x n ω) (y n ω) θ₀) atTop (fun _ => A1))
    (h2 : TendstoInMeasure P (fun n ω => sQuad (z n ω) (x n ω)) atTop (fun _ => A2))
    (hθ : TendstoInMeasure P θt atTop (fun _ => θ₀)) :
    TendstoInMeasure P (fun n ω => sHat (z n ω) (x n ω) (y n ω) (θt n ω)) atTop (fun _ => S) := by
  have hd : TendstoInMeasure P (fun n ω => θt n ω - θ₀) atTop (fun _ => (0 : k → ℝ)) := by
    have := tendstoInMeasure_comp_continuousAt hθ (q := fun t : k → ℝ => t - θ₀)
      (continuous_id.sub continuous_const).continuousAt
    simpa using this
  have h12 := tendstoInMeasure_prodMk (E := l → l → k → ℝ) (F := l → l → k → k → ℝ) h1 h2
  have h012 := tendstoInMeasure_prodMk (E := l → l → ℝ)
    (F := (l → l → k → ℝ) × (l → l → k → k → ℝ)) h0 h12
  have hall := tendstoInMeasure_prodMk
    (E := (l → l → ℝ) × (l → l → k → ℝ) × (l → l → k → k → ℝ)) (F := k → ℝ) h012 hd
  have := tendstoInMeasure_comp_continuousAt hall continuous_expandS.continuousAt
  simp only [expandS_zero] at this
  refine this.congr_left fun n => Filter.Eventually.of_forall fun ω => ?_
  exact (sHat_eq_expandS _ _ _ θ₀ _).symm

/-! ### Linear moment conditions and the feasible two-step estimator -/

/-- The sample Jacobian `Ĝ = n⁻¹ Σᵢ zᵢxᵢᵀ`. -/
noncomputable def sampleG (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) : l → k → ℝ :=
  fun a c => (N : ℝ)⁻¹ * ∑ i, z i a * x i c

/-- The sample cross moment `n⁻¹ Σᵢ zᵢyᵢ`. -/
noncomputable def sampleZY (z : Fin N → l → ℝ) (y : Fin N → ℝ) : l → ℝ :=
  fun a => (N : ℝ)⁻¹ * ∑ i, z i a * y i

/-- The sample moment `ĝ(θ) = n⁻¹ Σᵢ zᵢ(yᵢ − xᵢᵀθ)`. -/
noncomputable def sampleMoment (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) (y : Fin N → ℝ)
    (θ : k → ℝ) : l → ℝ :=
  fun a => (N : ℝ)⁻¹ * ∑ i, z i a * (y i - x i ⬝ᵥ θ)

omit [Fintype l] in
/-- `n⁻¹ Σ zᵢyᵢ = Ĝ θ₀ + ĝ(θ₀)`. -/
lemma sampleZY_eq (z : Fin N → l → ℝ) (x : Fin N → k → ℝ) (y : Fin N → ℝ) (θ₀ : k → ℝ) :
    sampleZY z y = Matrix.of (sampleG z x) *ᵥ θ₀ + sampleMoment z x y θ₀ := by
  funext a
  simp only [sampleZY, sampleG, sampleMoment, mulVec, dotProduct, of_apply, Pi.add_apply,
    Finset.sum_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ c, (N : ℝ)⁻¹ * (z i a * x i c) * θ₀ c = ∑ c, (N : ℝ)⁻¹ * (z i a * (x i c * θ₀ c)) :=
    fun i => Finset.sum_congr rfl fun c _ => by ring
  simp only [this]; ring

omit [Fintype k] [Fintype l] in
lemma continuous_sampleG : Continuous (fun p : (Fin N → l → ℝ) × (Fin N → k → ℝ) =>
    sampleG p.1 p.2) := by
  unfold sampleG; fun_prop

omit [Fintype k] [Fintype l] in
lemma continuous_sampleZY : Continuous (fun p : (Fin N → l → ℝ) × (Fin N → ℝ) =>
    sampleZY p.1 p.2) := by
  unfold sampleZY; fun_prop

omit [Fintype l] in
lemma continuous_sampleMoment (θ₀ : k → ℝ) : Continuous (fun p : (Fin N → l → ℝ) ×
    (Fin N → k → ℝ) × (Fin N → ℝ) => sampleMoment p.1 p.2.1 p.2.2 θ₀) := by
  unfold sampleMoment dotProduct; fun_prop

variable [DecidableEq k] [DecidableEq l]

/-- The first-step GMM estimator with weight `W₁`. -/
noncomputable def firstStep (W1 : l → l → ℝ) (z : Fin N → l → ℝ) (x : Fin N → k → ℝ)
    (y : Fin N → ℝ) : k → ℝ :=
  GMM.estimator (Matrix.of W1) (Matrix.of (sampleG z x)) (sampleZY z y)

/-- The second-step weight `Ŝ(θ̃)⁻¹` from first-step residuals. -/
noncomputable def secondWeight (W1 : l → l → ℝ) (z : Fin N → l → ℝ) (x : Fin N → k → ℝ)
    (y : Fin N → ℝ) : l → l → ℝ :=
  invFn (sHat z x y (firstStep W1 z x y))

/-- The two-step efficient GMM estimator. -/
noncomputable def twoStep (W1 : l → l → ℝ) (z : Fin N → l → ℝ) (x : Fin N → k → ℝ)
    (y : Fin N → ℝ) : k → ℝ :=
  GMM.estimator (Matrix.of (secondWeight W1 z x y)) (Matrix.of (sampleG z x)) (sampleZY z y)

omit [DecidableEq l] in
lemma measurable_firstStep : Measurable (fun p : (l → l → ℝ) × (Fin N → l → ℝ) ×
    (Fin N → k → ℝ) × (Fin N → ℝ) => firstStep p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hG : Measurable (fun p : (l → l → ℝ) × (Fin N → l → ℝ) × (Fin N → k → ℝ) ×
      (Fin N → ℝ) => (sampleG p.2.1 p.2.2.1, p.1)) :=
    ((continuous_sampleG.comp (by fun_prop :
      Continuous (fun p : (l → l → ℝ) × (Fin N → l → ℝ) × (Fin N → k → ℝ) × (Fin N → ℝ) =>
        (p.2.1, p.2.2.1)))).measurable).prodMk measurable_fst
  have hZY : Measurable (fun p : (l → l → ℝ) × (Fin N → l → ℝ) × (Fin N → k → ℝ) ×
      (Fin N → ℝ) => sampleZY p.2.1 p.2.2.2) :=
    (continuous_sampleZY.comp (by fun_prop :
      Continuous (fun p : (l → l → ℝ) × (Fin N → l → ℝ) × (Fin N → k → ℝ) × (Fin N → ℝ) =>
        (p.2.1, p.2.2.2)))).measurable
  have hmv : Continuous (fun q : (k → l → ℝ) × (l → ℝ) => Matrix.of q.1 *ᵥ q.2) := by fun_prop
  have : (fun p : (l → l → ℝ) × (Fin N → l → ℝ) × (Fin N → k → ℝ) × (Fin N → ℝ) =>
      firstStep p.1 p.2.1 p.2.2.1 p.2.2.2)
      = (fun q : (k → l → ℝ) × (l → ℝ) => Matrix.of q.1 *ᵥ q.2) ∘
        (fun p => (gmmA (sampleG p.2.1 p.2.2.1, p.1), sampleZY p.2.1 p.2.2.2)) := by
    funext p; simp only [firstStep, Function.comp_apply, estimator_eq_gmmA]
  rw [this]
  exact hmv.measurable.comp ((measurable_gmmA.comp hG).prodMk hZY)

omit [DecidableEq l] in
lemma aemeasurable_firstStep {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {W : α → l → l → ℝ} {z : α → Fin N → l → ℝ} {x : α → Fin N → k → ℝ} {y : α → Fin N → ℝ}
    (hW : AEMeasurable W μ) (hz : AEMeasurable z μ) (hx : AEMeasurable x μ)
    (hy : AEMeasurable y μ) :
    AEMeasurable (fun ω => firstStep (W ω) (z ω) (x ω) (y ω)) μ :=
  measurable_firstStep.comp_aemeasurable (f := fun ω => (W ω, z ω, x ω, y ω))
    (hW.prodMk (hz.prodMk (hx.prodMk hy)))

/-- **Feasible two-step efficient GMM** (Hansen 1982 Thm 3.2 and Lemma 4.2;
Hayashi Prop. 3.5–3.6). In the linear model with instruments `zᵢ`, regressors
`xᵢ`, outcomes `yᵢ`, a first step with weight `Ŵ₁ →p W₁` (rank condition at `W₁`),
the residual-based `Ŝ(θ̃)` and second-step weight `Ŝ(θ̃)⁻¹`: if
`Ĝ →p G` of full column rank, `√n ĝ(θ₀) →d L`, `Ŝ(θ₀) →p S` positive definite
and the cross and fourth-order sample moments converge, then
`√n (θ̂ − θ₀) →d A L` with `A = (GᵀS⁻¹G)⁻¹GᵀS⁻¹` (law `N(0, (GᵀS⁻¹G)⁻¹)` if
`L ~ N(0, S)`), and the J statistic converges to the efficient J form with mean
`l − k`. -/
theorem two_step_feasible [IsProbabilityMeasure P] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {z : (n : ℕ) → Ω → Fin n → l → ℝ} {x : (n : ℕ) → Ω → Fin n → k → ℝ}
    {y : (n : ℕ) → Ω → Fin n → ℝ} {W1 : ℕ → Ω → l → l → ℝ}
    {G : l → k → ℝ} {W₁ : l → l → ℝ} {S : Matrix l l ℝ} {θ₀ : k → ℝ}
    {A1 : l → l → k → ℝ} {A2 : l → l → k → k → ℝ} {L : Ω' → l → ℝ}
    (hS : S.PosDef) (hG : Function.Injective (Matrix.of G *ᵥ ·))
    (hrank1 : IsUnit (gram (G, W₁)).det)
    (hGhat : TendstoInMeasure P (fun n ω => sampleG (z n ω) (x n ω)) atTop (fun _ => G))
    (hW1 : TendstoInMeasure P W1 atTop (fun _ => W₁))
    (hg : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (x n ω) (y n ω) θ₀) atTop L
      (fun _ => P) P')
    (h0 : TendstoInMeasure P (fun n ω => sHat (z n ω) (x n ω) (y n ω) θ₀) atTop
      (fun _ => Matrix.of.symm S))
    (h1 : TendstoInMeasure P (fun n ω => sCross (z n ω) (x n ω) (y n ω) θ₀) atTop (fun _ => A1))
    (h2 : TendstoInMeasure P (fun n ω => sQuad (z n ω) (x n ω)) atTop (fun _ => A2))
    (hz : ∀ n, AEMeasurable (z n) P) (hx : ∀ n, AEMeasurable (x n) P)
    (hy : ∀ n, AEMeasurable (y n) P) (hW1m : ∀ n, AEMeasurable (W1 n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (twoStep (W1 n ω) (z n ω) (x n ω) (y n ω) - θ₀)) atTop
      (fun ω => Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω) (fun _ => P) P' ∧
    (Measurable L → P'.map L = (multivariateGaussian 0 S).map ofLp →
      P'.map (fun ω => Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω)
        = (multivariateGaussian 0 ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹).map ofLp) ∧
    TendstoInDistribution
      (fun (n : ℕ) ω => jStat n (sampleG (z n ω) (x n ω)) (secondWeight (W1 n ω) (z n ω) (x n ω)
        (y n ω)) (sampleZY (z n ω) (y n ω)))
      atTop (fun ω => L ω ⬝ᵥ (jForm S (Matrix.of G) *ᵥ L ω)) (fun _ => P) P' ∧
    (Measurable L → P'.map L = (multivariateGaussian 0 S).map ofLp →
      ∫ ω, L ω ⬝ᵥ (jForm S (Matrix.of G) *ᵥ L ω) ∂P' = (Fintype.card l : ℝ) - Fintype.card k) := by
  have hZY : ∀ n ω, sampleZY (z n ω) (y n ω)
      = Matrix.of (sampleG (z n ω) (x n ω)) *ᵥ θ₀ + sampleMoment (z n ω) (x n ω) (y n ω) θ₀ :=
    fun n ω => sampleZY_eq _ _ _ θ₀
  -- first-step consistency
  have hg0 : TendstoInMeasure P (fun n ω => sampleMoment (z n ω) (x n ω) (y n ω) θ₀) atTop
      (fun _ => 0) :=
    tendstoInMeasure_of_sqrt_pi (θ := 0) (by simpa only [sub_zero] using hg)
  have hθt : TendstoInMeasure P (fun n ω => firstStep (W1 n ω) (z n ω) (x n ω) (y n ω)) atTop
      (fun _ => θ₀) := by
    have := gmm_consistent (θ₀ := θ₀) hrank1 hGhat hW1 hg0
    refine this.congr_left fun n => Filter.Eventually.of_forall fun ω => ?_
    simp only [firstStep, hZY]
  have hShat := sHat_consistent h0 h1 h2 hθt
  -- measurability
  have hGm : ∀ n, AEMeasurable (fun ω => sampleG (z n ω) (x n ω)) P := fun n =>
    (continuous_sampleG (N := n) (k := k) (l := l)).measurable.comp_aemeasurable
      (f := fun ω => (z n ω, x n ω)) ((hz n).prodMk (hx n))
  have hgm : ∀ n, AEMeasurable (fun ω => sampleMoment (z n ω) (x n ω) (y n ω) θ₀) P := fun n =>
    (continuous_sampleMoment (N := n) (l := l) θ₀).measurable.comp_aemeasurable
      (f := fun ω => (z n ω, x n ω, y n ω)) ((hz n).prodMk ((hx n).prodMk (hy n)))
  have hθm : ∀ n, AEMeasurable (fun ω => firstStep (W1 n ω) (z n ω) (x n ω) (y n ω)) P :=
    fun n => aemeasurable_firstStep (hW1m n) (hz n) (hx n) (hy n)
  have hSm : ∀ n, AEMeasurable (fun ω => sHat (z n ω) (x n ω) (y n ω)
      (firstStep (W1 n ω) (z n ω) (x n ω) (y n ω))) P := fun n =>
    (continuous_sHat (N := n) (k := k) (l := l)).measurable.comp_aemeasurable
      (f := fun ω => (z n ω, x n ω, y n ω, firstStep (W1 n ω) (z n ω) (x n ω) (y n ω))) ((hz n).prodMk ((hx n).prodMk ((hy n).prodMk (hθm n))))
  obtain ⟨hA, hlaw⟩ := two_step_gmm (θ₀ := θ₀) hS hG hGhat hShat hg hGm hSm hgm
  obtain ⟨hJ, hmean⟩ := two_step_jtest (θ₀ := θ₀) hS hG hGhat hShat hg hGm hSm hgm
  refine ⟨?_, hlaw, ?_, hmean⟩
  · have heq : (fun (n : ℕ) ω => Real.sqrt n • (twoStep (W1 n ω) (z n ω) (x n ω) (y n ω) - θ₀))
        = fun (n : ℕ) ω => Real.sqrt n • (GMM.estimator (Matrix.of (invFn (sHat (z n ω) (x n ω)
          (y n ω) (firstStep (W1 n ω) (z n ω) (x n ω) (y n ω))))) (Matrix.of (sampleG (z n ω) (x n ω)))
          (Matrix.of (sampleG (z n ω) (x n ω)) *ᵥ θ₀ + sampleMoment (z n ω) (x n ω) (y n ω) θ₀) - θ₀) := by
      funext n ω; rw [twoStep, secondWeight, hZY]
    rw [heq]; exact hA
  · have heq : (fun (n : ℕ) ω => jStat n (sampleG (z n ω) (x n ω))
        (secondWeight (W1 n ω) (z n ω) (x n ω) (y n ω)) (sampleZY (z n ω) (y n ω)))
        = fun (n : ℕ) ω => jStat n (sampleG (z n ω) (x n ω)) (invFn (sHat (z n ω) (x n ω)
          (y n ω) (firstStep (W1 n ω) (z n ω) (x n ω) (y n ω))))
          (Matrix.of (sampleG (z n ω) (x n ω)) *ᵥ θ₀ + sampleMoment (z n ω) (x n ω) (y n ω) θ₀) := by
      funext n ω; rw [secondWeight, hZY]
    rw [heq]; exact hJ


/-! ### Non-vacuity -/

/-- Deterministic design errors `ε₀ = √(n/2)`, `ε₁ = −√(n/2)`, zero otherwise:
they sum to `0` and their squares to `n`. -/
noncomputable def wEps (n j : ℕ) : ℝ :=
  (if j = 0 then Real.sqrt (n / 2) else 0) + (if j = 1 then -Real.sqrt (n / 2) else 0)

lemma sum_wEps {n : ℕ} (hn : 2 ≤ n) : ∑ i : Fin n, wEps n i = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => wEps n j)]
  simp only [wEps, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  simp only [show 0 < n by omega, show 1 < n by omega, ↓reduceIte]; ring

lemma sum_wEps_sq {n : ℕ} (hn : 2 ≤ n) : ∑ i : Fin n, wEps n i ^ 2 = n := by
  have h : ∀ j : ℕ, wEps n j ^ 2 = (if j = 0 then (n : ℝ) / 2 else 0) + (if j = 1 then (n : ℝ) / 2 else 0) := by
    intro j
    have hs : Real.sqrt (n / 2) ^ 2 = (n : ℝ) / 2 := Real.sq_sqrt (by positivity)
    rcases Nat.lt_trichotomy j 1 with hj | rfl | hj
    · obtain rfl : j = 0 := by omega
      simp only [wEps, ↓reduceIte, zero_ne_one, add_zero, hs]
    · simp only [wEps, ↓reduceIte, one_ne_zero, zero_add, neg_sq, hs]
    · simp [wEps, show j ≠ 0 by omega, show j ≠ 1 by omega]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j = 0 then (n : ℝ) / 2 else 0) +
    (if j = 1 then (n : ℝ) / 2 else 0))]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  simp only [show 0 < n by omega, show 1 < n by omega, ↓reduceIte]; ring

/-- **Non-vacuity of `two_step_feasible`**: one instrument, one regressor
(`zᵢ = xᵢ = 1`), `θ₀ = 0` and outcomes `yᵢ = Z/√n + εᵢ` with `Z ~ N(0, 1)` and the
design errors `wEps`. Every hypothesis holds (with `S = 1`, `W₁ = 1`), so the
limit of the two-step estimator follows from `two_step_feasible`. -/
theorem two_step_feasible_witness :
    let P : Measure (Fin 1 → ℝ) := (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).map ofLp
    let z : (n : ℕ) → (Fin 1 → ℝ) → Fin n → Fin 1 → ℝ := fun _ _ _ _ => 1
    let y : (n : ℕ) → (Fin 1 → ℝ) → Fin n → ℝ := fun n ω i => (Real.sqrt n)⁻¹ * ω 0 + wEps n i
    let G : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    ∃ _ : IsProbabilityMeasure P,
      Function.Injective (Matrix.of G *ᵥ ·) ∧ IsUnit (gram (G, G)).det ∧
      TendstoInMeasure P (fun n ω => sampleG (z n ω) (z n ω)) atTop (fun _ => G) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (z n ω) (y n ω) 0) atTop id
        (fun _ => P) P ∧
      TendstoInMeasure P (fun n ω => sHat (z n ω) (z n ω) (y n ω) 0) atTop
        (fun _ => Matrix.of.symm 1) ∧
      TendstoInMeasure P (fun n ω => sCross (z n ω) (z n ω) (y n ω) 0) atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun n ω => sQuad (z n ω) (z n ω)) atTop (fun _ => fun _ _ _ _ => 1) ∧
      (∀ n, AEMeasurable (y n) P) ∧ P.map id = (multivariateGaussian 0 1).map ofLp ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n • (twoStep (fun _ _ => 1) (z n ω) (z n ω) (y n ω) - 0))
        atTop (fun ω => Matrix.of (gmmA (G, invFn (Matrix.of.symm 1))) *ᵥ ω) (fun _ => P) P := by
  intro P z y G
  have hofLp : Measurable (ofLp : EuclideanSpace ℝ (Fin 1) → Fin 1 → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hP : IsProbabilityMeasure P := (Measure.isProbabilityMeasure_map_iff hofLp.aemeasurable).mpr inferInstance
  have hfin : ∀ (v : Fin 1 → ℝ), v = fun _ => v 0 := fun v => funext fun a => by
    rw [Subsingleton.elim a 0]
  -- exact sample moments for `n ≥ 2`
  have hGe : ∀ n : ℕ, 2 ≤ n → ∀ ω, sampleG (z n ω) (z n ω) = G := by
    intro n hn ω; funext a c
    have : (n : ℝ) ≠ 0 := by positivity
    simp [sampleG, z, G, this]
  have hme : ∀ n : ℕ, 2 ≤ n → ∀ ω, sampleMoment (z n ω) (z n ω) (y n ω) 0
      = fun _ => (Real.sqrt n)⁻¹ * ω 0 := by
    intro n hn ω; funext a
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [sampleMoment, z, y, dotProduct_zero, sub_zero, one_mul, Finset.sum_add_distrib,
      sum_wEps hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_zero]
    field_simp
  have hSe : ∀ n : ℕ, 2 ≤ n → ∀ ω, sHat (z n ω) (z n ω) (y n ω) 0
      = fun _ _ => ((Real.sqrt n)⁻¹ * ω 0) ^ 2 + 1 := by
    intro n hn ω; funext a b
    have : (n : ℝ) ≠ 0 := by positivity
    have hsq : ∀ i : Fin n, ((Real.sqrt n)⁻¹ * ω 0 + wEps n i) ^ 2
        = ((Real.sqrt n)⁻¹ * ω 0) ^ 2 + 2 * ((Real.sqrt n)⁻¹ * ω 0) * wEps n i + wEps n i ^ 2 :=
      fun i => by ring
    simp only [sHat, z, y, dotProduct_zero, sub_zero, mul_one, hsq, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_wEps hn, sum_wEps_sq hn, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero]
    field_simp
  have hCe : ∀ n : ℕ, 2 ≤ n → ∀ ω, sCross (z n ω) (z n ω) (y n ω) 0
      = fun _ _ _ => (Real.sqrt n)⁻¹ * ω 0 := by
    intro n hn ω; funext a b c
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [sCross, z, y, dotProduct_zero, sub_zero, mul_one, Finset.sum_add_distrib,
      sum_wEps hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_zero]
    field_simp
  have hQe : ∀ n : ℕ, 2 ≤ n → ∀ ω, sQuad (z n ω) (z n ω) = fun _ _ _ _ => 1 := by
    intro n hn ω; funext a b c e
    have : (n : ℝ) ≠ 0 := by positivity
    simp [sQuad, z, this]
  have hev := Filter.eventually_ge_atTop (2 : ℕ)
  -- the CLT hypothesis
  have hym : ∀ n : ℕ, Measurable (y n) := fun n => by
    simp only [y]; fun_prop
  have hgm : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n • sampleMoment (z n ω) (z n ω) (y n ω) 0) P :=
    fun n => by
      have h : Measurable (fun ω => sampleMoment (z n ω) (z n ω) (y n ω) 0) :=
        (continuous_sampleMoment (N := n) (k := Fin 1) (l := Fin 1) 0).measurable.comp
          (f := fun ω => (z n ω, z n ω, y n ω)) (measurable_const.prodMk
            (measurable_const.prodMk (hym n)))
      exact (h.const_smul (Real.sqrt n)).aemeasurable
  have hTID : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (z n ω) (y n ω) 0) atTop id
      (fun _ => P) P := by
    refine ⟨hgm, aemeasurable_id, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [hev] with n hn
    have hs : Real.sqrt n ≠ 0 := by
      rw [Real.sqrt_ne_zero']; exact_mod_cast (by omega : 0 < n)
    apply Subtype.ext
    simp only
    congr 1
    funext ω
    rw [hme n hn ω, hfin ω]
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, id]
    field_simp
  have hm0 : TendstoInMeasure P (fun n ω => sampleMoment (z n ω) (z n ω) (y n ω) 0) atTop
      (fun _ => 0) :=
    tendstoInMeasure_of_sqrt_pi (θ := 0) (by simpa only [sub_zero] using hTID)
  have hconst : ∀ {E : Type} [PseudoMetricSpace E] (c : E),
      TendstoInMeasure P (fun (_ : ℕ) (_ : Fin 1 → ℝ) => c) atTop (fun _ => c) := fun c =>
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
  have hGhat : TendstoInMeasure P (fun n ω => sampleG (z n ω) (z n ω)) atTop (fun _ => G) := by
    refine (hconst G).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hev] with n hn
    exact Filter.Eventually.of_forall fun ω => (hGe n hn ω).symm
  have hShat : TendstoInMeasure P (fun n ω => sHat (z n ω) (z n ω) (y n ω) 0) atTop
      (fun _ => Matrix.of.symm 1) := by
    have h := tendstoInMeasure_comp_continuousAt hm0
      (q := fun v : Fin 1 → ℝ => fun (_ _ : Fin 1) => v 0 ^ 2 + 1)
      (Continuous.continuousAt (by fun_prop))
    refine h.congr' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · filter_upwards [hev] with n hn
      exact Filter.Eventually.of_forall fun ω => by
        simp only; rw [hme n hn ω, hSe n hn ω]
    · funext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp
  have hCross : TendstoInMeasure P (fun n ω => sCross (z n ω) (z n ω) (y n ω) 0) atTop
      (fun _ => 0) := by
    have h := tendstoInMeasure_comp_continuousAt hm0
      (q := fun v : Fin 1 → ℝ => fun (_ _ : Fin 1) (_ : Fin 1) => v 0)
      (Continuous.continuousAt (by fun_prop))
    refine h.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hev] with n hn
    exact Filter.Eventually.of_forall fun ω => by
      simp only; rw [hme n hn ω, hCe n hn ω]
  have hQuad : TendstoInMeasure P (fun n ω => sQuad (z n ω) (z n ω)) atTop
      (fun _ => fun _ _ _ _ => 1) := by
    refine (hconst (fun (_ _ _ _ : Fin 1) => (1 : ℝ))).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hev] with n hn
    exact Filter.Eventually.of_forall fun ω => (hQe n hn ω).symm
  have hinj : Function.Injective (Matrix.of G *ᵥ ·) := by
    intro a b h
    have := congrFun h 0
    simp only [mulVec, dotProduct, of_apply, one_mul, Finset.univ_unique, Finset.sum_singleton,
      G] at this
    funext i; rw [Subsingleton.elim i 0]; exact this
  have hrank : IsUnit (gram (G, G)).det := by
    simp [gram, Matrix.det_unique, Matrix.mul_apply, G]
  refine ⟨hP, hinj, hrank, hGhat, hTID, hShat, hCross, hQuad,
    fun n => (hym n).aemeasurable, Measure.map_id, ?_⟩
  exact (two_step_feasible (θ₀ := 0) PosDef.one hinj hrank hGhat (hconst G) hTID hShat hCross
    hQuad (fun _ => aemeasurable_const) (fun _ => aemeasurable_const)
    (fun n => (hym n).aemeasurable) (fun _ => aemeasurable_const)).1

end Econ.Asymptotics
