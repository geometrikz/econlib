/-
# The Gauss–Markov theorem

Hayashi, *Econometrics* (2000), Prop. 1.1(c)–(d); Greene, *Econometric
Analysis* (2018), Thm 4.2; Davidson–MacKinnon (2004), Thm 3.3.

**The economics.** In the classical linear model with a fixed (non-random)
design, `y = Xβ + ε` with `E[ε] = 0` and `Var(ε) = E[εεᵀ] = σ² I`
(homoskedastic, uncorrelated errors) and `XᵀX` nonsingular:

* a linear estimator `b̃ = C y` is unbiased for every `β` if and only if
  `C X = I` (`unbiased_iff`);
* the covariance matrix of any linear unbiased estimator is `σ² C Cᵀ`, and that
  of OLS is `σ² (XᵀX)⁻¹` (`cov_linear`, `cov_ols`);
* **Gauss–Markov**: `Var(b̃) − Var(β̂_OLS)` is positive semidefinite, i.e. OLS is
  the best linear unbiased estimator (`gauss_markov`).

**Encoding.** The design `X` is fixed (conditioning on `X` in Hayashi's
random-regressor version); `ε : Ω → n → ℝ` is a random vector whose entries and
pairwise products are integrable. `cov μ v` is the covariance matrix of a random
vector `v`.
-/
module

public import EconLean.Econometrics.OLS
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

namespace Econ.OLS

open Matrix MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n k : Type*} [Fintype n] [Fintype k]

/-- The covariance matrix `E[(v − E v)(v − E v)ᵀ]` of a random vector. -/
noncomputable def cov (μ : Measure Ω) (v : Ω → k → ℝ) : Matrix k k ℝ :=
  Matrix.of fun a b => ∫ ω, (v ω a - ∫ ω', v ω' a ∂μ) * (v ω b - ∫ ω', v ω' b ∂μ) ∂μ

/-- The second-moment matrix `E[ε εᵀ]`. -/
noncomputable def secondMoments (μ : Measure Ω) (ε : Ω → n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => ∫ ω, ε ω i * ε ω j ∂μ

omit [Fintype k] in
/-- `E[C ε] = C E[ε]`. -/
lemma integral_mulVec {ε : Ω → n → ℝ} (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (C : Matrix k n ℝ) (a : k) :
    ∫ ω, (C *ᵥ ε ω) a ∂μ = (C *ᵥ fun i => ∫ ω, ε ω i ∂μ) a := by
  simp only [mulVec, dotProduct]
  rw [integral_finsetSum _ fun i _ => (hε i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

omit [Fintype k] in
/-- `E[(Cε)(Dε)ᵀ] = C E[εεᵀ] Dᵀ`. -/
lemma integral_mulVec_mul_mulVec {ε : Ω → n → ℝ}
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (C D : Matrix k n ℝ) (a b : k) :
    ∫ ω, (C *ᵥ ε ω) a * (D *ᵥ ε ω) b ∂μ = (C * secondMoments μ ε * Dᵀ) a b := by
  have hexp : ∀ ω, (C *ᵥ ε ω) a * (D *ᵥ ε ω) b
      = ∑ i, ∑ j, (C a i * D b j) * (ε ω i * ε ω j) := by
    intro ω
    simp only [mulVec, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hεε i j).const_mul _]
  simp only [Matrix.mul_apply, secondMoments, of_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hεε i j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]; ring

section Classical

variable [IsProbabilityMeasure μ] [DecidableEq k] {X : Matrix n k ℝ} {ε : Ω → n → ℝ}

omit [DecidableEq k] in
/-- Mean of a linear estimator `C y` with `y = Xβ + ε`, `E ε = 0`: `E[C y] = C X β`. -/
lemma integral_linear (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (C : Matrix k n ℝ) (β : k → ℝ) (a : k) :
    ∫ ω, (C *ᵥ (X *ᵥ β + ε ω)) a ∂μ = ((C * X) *ᵥ β) a := by
  have hint : Integrable (fun ω => (C *ᵥ ε ω) a) μ := by
    simp only [mulVec, dotProduct]
    exact integrable_finsetSum _ fun i _ => (hε i).const_mul _
  simp only [mulVec_add, Pi.add_apply]
  rw [integral_add (integrable_const _) hint, integral_const, integral_mulVec hε,
    show (fun i => ∫ ω, ε ω i ∂μ) = 0 from funext hmean, mulVec_zero, mulVec_mulVec]
  simp

/-- **Linear unbiasedness** (Hayashi §1.3): `C y` is unbiased for every `β` iff
`C X = I`. -/
theorem unbiased_iff (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (C : Matrix k n ℝ) :
    (∀ β : k → ℝ, ∀ a, ∫ ω, (C *ᵥ (X *ᵥ β + ε ω)) a ∂μ = β a) ↔ C * X = 1 := by
  simp only [integral_linear hε hmean]
  constructor
  · intro h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun β => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    exact funext (h β)
  · intro h β a; rw [h, one_mulVec]

omit [DecidableEq k] in
/-- **Covariance of a linear estimator**: `Var(C y) = C E[εεᵀ] Cᵀ` (no unbiasedness needed). -/
theorem cov_linear (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (C : Matrix k n ℝ) (β : k → ℝ) :
    cov μ (fun ω => C *ᵥ (X *ᵥ β + ε ω)) = C * secondMoments μ ε * Cᵀ := by
  ext a b
  have hc : ∀ (c : k) ω, (C *ᵥ (X *ᵥ β + ε ω)) c - ∫ ω', (C *ᵥ (X *ᵥ β + ε ω')) c ∂μ
      = (C *ᵥ ε ω) c := by
    intro c ω
    rw [integral_linear hε hmean, mulVec_add, mulVec_mulVec, Pi.add_apply, add_sub_cancel_left]
  simp only [cov, of_apply, hc]
  exact integral_mulVec_mul_mulVec hεε C C a b

/-- The OLS estimator is the linear estimator `C₀ y` with `C₀ = (XᵀX)⁻¹ Xᵀ`. -/
lemma ols_eq_mulVec (X : Matrix n k ℝ) (y : n → ℝ) : ols X y = ((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y := by
  rw [ols, mulVec_mulVec]

/-- **Variance of OLS** (Hayashi Prop. 1.1(b)): with `E[εεᵀ] = σ² I`,
`Var(β̂) = σ² (XᵀX)⁻¹`. -/
theorem cov_ols [DecidableEq n] (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    {σ2 : ℝ} (hvar : secondMoments μ ε = σ2 • (1 : Matrix n n ℝ))
    (hX : IsUnit (Xᵀ * X).det) (β : k → ℝ) :
    cov μ (fun ω => ols X (X *ᵥ β + ε ω)) = σ2 • (Xᵀ * X)⁻¹ := by
  have hC : (Xᵀ * X)⁻¹ * Xᵀ * X = 1 := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hX]
  simp only [ols_eq_mulVec]
  rw [cov_linear hε hεε hmean _, hvar, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ,
    ← Matrix.mul_assoc ((Xᵀ * X)⁻¹), nonsing_inv_mul _ hX, Matrix.one_mul, transpose_nonsing_inv,
    transpose_mul, transpose_transpose]

/-- **Gauss–Markov theorem** (Hayashi Prop. 1.1(c)): in the classical linear
model with fixed full-rank design and spherical errors (`E[εεᵀ] = σ² I`), every
linear unbiased estimator `C y` (`C X = I`) has covariance at least that of OLS:
`Var(C y) − Var(β̂_OLS)` is positive semidefinite. -/
theorem gauss_markov [DecidableEq n] (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    {σ2 : ℝ} (hvar : secondMoments μ ε = σ2 • (1 : Matrix n n ℝ))
    (hX : IsUnit (Xᵀ * X).det) {C : Matrix k n ℝ} (hC : C * X = 1) (β : k → ℝ) :
    (cov μ (fun ω => C *ᵥ (X *ᵥ β + ε ω)) - cov μ (fun ω => ols X (X *ᵥ β + ε ω))).PosSemidef := by
  rw [cov_linear hε hεε hmean C, cov_ols hε hεε hmean hvar hX, hvar, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, ← smul_sub]
  set C₀ := (Xᵀ * X)⁻¹ * Xᵀ with hC₀
  set D := C - C₀ with hD
  have hDX : D * X = 0 := by
    rw [hD, Matrix.sub_mul, hC, hC₀, Matrix.mul_assoc, nonsing_inv_mul _ hX, sub_self]
  have hsym : (Xᵀ * X)⁻¹ᵀ = (Xᵀ * X)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]
  have hC₀C₀ : C₀ * C₀ᵀ = (Xᵀ * X)⁻¹ := by
    rw [hC₀, transpose_mul, transpose_transpose, hsym, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hX, Matrix.one_mul]
  have hDC₀ : D * C₀ᵀ = 0 := by
    rw [hC₀, transpose_mul, transpose_transpose, hsym, ← Matrix.mul_assoc, hDX,
      Matrix.zero_mul]
  have hC₀D : C₀ * Dᵀ = 0 := by
    rw [← transpose_transpose C₀, ← transpose_mul, hDC₀, transpose_zero]
  have key : C * Cᵀ - (Xᵀ * X)⁻¹ = D * Dᵀ := by
    have hCD : C = C₀ + D := by rw [hD]; abel
    rw [hCD, transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hC₀C₀, hC₀D,
      hDC₀]
    abel
  rw [key]
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
  · have : D * Dᵀ = 0 := by ext a b; simp [Matrix.mul_apply]
    rw [this, smul_zero]; exact PosSemidef.zero
  · have hσ : 0 ≤ σ2 := by
      have := congrFun (congrFun hvar i) i
      simp only [secondMoments, of_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
        mul_one] at this
      rw [← this]
      exact integral_nonneg fun ω => mul_self_nonneg _
    have := (posSemidef_self_mul_conjTranspose D).smul hσ
    rwa [conjTranspose_eq_transpose_of_trivial] at this

end Classical

/-- **Non-vacuity** of the Gauss–Markov hypotheses: a fair-coin error `ε = ±1`
on `Ω = Bool` has mean zero, second moment `1`, and all moments integrable. -/
theorem gaussMarkov_witness :
    let μ : Measure Bool := ProbabilityTheory.uniformOn Set.univ
    let ε : Bool → Unit → ℝ := fun ω _ => if ω then 1 else -1
    IsProbabilityMeasure μ ∧ (∀ i, Integrable (fun ω => ε ω i) μ) ∧
      (∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) ∧ (∀ i, ∫ ω, ε ω i ∂μ = 0) ∧
      secondMoments μ ε = (1 : ℝ) • (1 : Matrix Unit Unit ℝ) := by
  intro μ ε
  have hμ : IsProbabilityMeasure μ := by simp only [μ]; infer_instance
  have hs : ∀ b : Bool, μ.real {b} = 1 / 2 := by
    intro b
    simp only [μ, measureReal_def, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    norm_num
  refine ⟨hμ, fun _ => Integrable.of_finite, fun _ _ => Integrable.of_finite,
    fun i => ?_, ?_⟩
  · rw [integral_fintype Integrable.of_finite]
    simp [hs, ε]
  · ext i j
    simp only [secondMoments, Matrix.of_apply]
    rw [integral_fintype Integrable.of_finite]
    simp [hs, ε]
    norm_num

end Econ.OLS
