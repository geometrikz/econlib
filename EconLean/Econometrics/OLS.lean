/-
# Ordinary least squares as a projection

Hayashi, *Econometrics* (2000), §1.1–1.3 and §1.2 (algebra of least squares);
Davidson–MacKinnon, *Econometric Theory and Methods* (2004), §2.3–2.4 (FWL);
Angrist–Pischke, *Mostly Harmless Econometrics* (2009), §3.2.2 (omitted-variable bias).

**The economics.** The linear regression `y = X β + ε` with `n` observations
and `K` regressors is the workhorse of empirical economics. Everything in this
file is *finite-sample algebra*: no probability is needed except in the last
section (unbiasedness).

* The OLS estimate `b` minimises the sum of squared residuals
  `SSR(b) = (y − X b)ᵀ (y − X b)`.
* The minimisers are exactly the solutions of the **normal equations**
  `Xᵀ (y − X b) = 0` (residuals are orthogonal to every regressor).
* If `X` has full column rank (`XᵀX` invertible), the solution is unique:
  `b = (XᵀX)⁻¹ Xᵀ y` (Hayashi eq. 1.2.5).
* The fitted values `X b = P y` are the orthogonal projection of `y` on the
  column space of `X`, with `P = X (XᵀX)⁻¹ Xᵀ` symmetric and idempotent; the
  residuals are `M y` with `M = I − P` (Hayashi §1.2).
* **Frisch–Waugh–Lovell**: in the regression of `y` on `[X₁ X₂]`, the
  coefficients on `X₂` are the coefficients from regressing the residualised
  `M₁ y` on the residualised `M₁ X₂`, and the residuals coincide
  (Davidson–MacKinnon Thm 2.1, Frisch–Waugh 1933, Lovell 1963).
* **Omitted-variable bias** (in-sample algebraic form; the population version
  in Angrist–Pischke replaces sample moments by population moments): if the truth is `y = X₁ β₁ + X₂ β₂ + ε` and we
  regress `y` on `X₁` only, we get `β₁ + δ β₂ + (X₁ᵀX₁)⁻¹X₁ᵀε`, where `δ` is
  the matrix of coefficients from regressing `X₂` on `X₁`.
* **Unbiasedness** (Hayashi Prop. 1.1(a)): if `y = X β + ε` with `E[ε] = 0`
  then `E[b] = β`.

**Lean encoding.** Observations are indexed by a finite type `n`, regressors
by a finite type `k` (so partitioned regressors are simply `k₁ ⊕ k₂`).
`X : Matrix n k ℝ`, `y : n → ℝ`. `M *ᵥ v` is matrix–vector product, `v ⬝ᵥ w`
the dot product, `Mᵀ` the transpose. "Full column rank" is
`IsUnit (Xᵀ * X).det`; `isUnit_det_gram_iff` shows it is equivalent to
`X *ᵥ ·` being injective (no exact collinearity).

**Documented deviation.** Unbiasedness is proved for a *fixed* design matrix
`X` with `E[ε] = 0`. Hayashi conditions on `X` and assumes `E[ε | X] = 0`;
conditional on `X` this is exactly our statement. The random-design version
(integrating over `X`) needs conditional expectation and is left for later.
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace Econ.OLS

open Matrix

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]

/-! ## Least squares and the normal equations -/

/-- Sum of squared residuals `SSR(b) = (y − X b) ⬝ (y − X b)`. -/
def ssr (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) : ℝ :=
  (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b)

/-- `b` is a least-squares estimate: it minimises the sum of squared residuals.
This is the *definition* of OLS (Hayashi eq. 1.2.1). -/
def IsLeastSquares (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) : Prop :=
  ∀ b' : k → ℝ, ssr X y b ≤ ssr X y b'

/-- The normal equations `Xᵀ (y − X b) = 0`: the residual vector is orthogonal to
every column of `X` (Hayashi eq. 1.2.3). -/
def NormalEquations (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) : Prop :=
  Xᵀ *ᵥ (y - X *ᵥ b) = 0

/-- The OLS formula `b = (XᵀX)⁻¹ Xᵀ y` (Hayashi eq. 1.2.5). Only meaningful when
`XᵀX` is invertible: Lean's `⁻¹` returns `0` for a singular matrix, so every
theorem about `ols` below assumes full column rank. -/
noncomputable def ols (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)

/-- A dot product of a real vector with itself is nonnegative. -/
lemma dotProduct_self_nonneg' {m : Type*} [Fintype m] (v : m → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [DecidableEq k] in
/-- Key expansion: moving from `b` to `b'` changes `SSR` by a cross term and a
nonnegative quadratic term. With `r = y − X b` and `d = b − b'`:
`SSR(b') = SSR(b) + 2 (Xᵀ r) ⬝ d + (X d) ⬝ (X d)`. -/
lemma ssr_eq (X : Matrix n k ℝ) (y : n → ℝ) (b b' : k → ℝ) :
    ssr X y b' = ssr X y b + 2 * ((Xᵀ *ᵥ (y - X *ᵥ b)) ⬝ᵥ (b - b'))
      + (X *ᵥ (b - b')) ⬝ᵥ (X *ᵥ (b - b')) := by
  have hcross : (Xᵀ *ᵥ (y - X *ᵥ b)) ⬝ᵥ (b - b') = (y - X *ᵥ b) ⬝ᵥ (X *ᵥ (b - b')) := by
    rw [mulVec_transpose, dotProduct_mulVec]
  have hsplit : y - X *ᵥ b' = (y - X *ᵥ b) + X *ᵥ (b - b') := by
    rw [mulVec_sub]; abel
  rw [hcross, ssr, ssr, hsplit]
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm (X *ᵥ (b - b')) (y - X *ᵥ b)]
  ring

/-- A scalar fact used for the first-order condition: if `−2 t q + t² s ≥ 0` for
every real `t`, with `s ≥ 0`, then `q = 0`. -/
lemma eq_zero_of_forall_quadratic_nonneg {q s : ℝ} (hs : 0 ≤ s)
    (h : ∀ t : ℝ, 0 ≤ -2 * t * q + t ^ 2 * s) : q = 0 := by
  -- Take `t = q / (s + 1)`; then the quadratic equals `−q² (s + 2) / (s + 1)²`.
  have h1 := h (q / (s + 1))
  have hs1 : 0 < s + 1 := by linarith
  have key : -2 * (q / (s + 1)) * q + (q / (s + 1)) ^ 2 * s
      = -(q ^ 2 * (s + 2)) / (s + 1) ^ 2 := by
    field_simp; ring
  rw [key] at h1
  have h2 : q ^ 2 * (s + 2) ≤ 0 := by
    have := div_nonneg_iff.mp h1
    rcases this with ⟨h3, _⟩ | ⟨_, h4⟩
    · linarith
    · nlinarith [sq_nonneg (s + 1)]
  have h3 : q ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg q]) (sq_nonneg q)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3

omit [DecidableEq k] in
/-- **Least squares ⟺ normal equations.** `b` minimises the sum of squared
residuals if and only if the residuals are orthogonal to the regressors. This
holds with or without full rank. -/
theorem isLeastSquares_iff_normalEquations (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) :
    IsLeastSquares X y b ↔ NormalEquations X y b := by
  constructor
  · intro h
    -- Perturb `b` along `g = Xᵀ r`: `b' = b + t g`. Then
    -- `SSR(b') − SSR(b) = −2 t (g ⬝ g) + t² ‖X g‖²`, and minimality forces `g ⬝ g = 0`.
    set g := Xᵀ *ᵥ (y - X *ᵥ b) with hg
    have hq : g ⬝ᵥ g = 0 := by
      refine eq_zero_of_forall_quadratic_nonneg (dotProduct_self_nonneg' (X *ᵥ g)) fun t => ?_
      have := h (b + t • g)
      rw [ssr_eq X y b (b + t • g)] at this
      have hd : b - (b + t • g) = -(t • g) := by abel
      rw [hd, ← hg] at this
      simp only [mulVec_neg, mulVec_smul, dotProduct_neg, neg_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul] at this
      nlinarith
    exact dotProduct_self_eq_zero.mp hq
  · intro h b'
    rw [ssr_eq X y b b', show Xᵀ *ᵥ (y - X *ᵥ b) = 0 from h, zero_dotProduct]
    linarith [dotProduct_self_nonneg' (X *ᵥ (b - b'))]

/-! ## Full column rank and the OLS formula -/

/-- Full column rank in the textbook sense (no exact collinearity: `X v = 0` only
for `v = 0`) is equivalent to invertibility of the Gram matrix `XᵀX`. -/
theorem isUnit_det_gram_iff (X : Matrix n k ℝ) :
    IsUnit (Xᵀ * X).det ↔ Function.Injective (X *ᵥ ·) := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  constructor
  · intro h v w hvw
    replace hvw : X *ᵥ v = X *ᵥ w := hvw
    apply h
    show (Xᵀ * X) *ᵥ v = (Xᵀ * X) *ᵥ w
    rw [← mulVec_mulVec, ← mulVec_mulVec, hvw]
  · intro h v w hvw
    replace hvw : (Xᵀ * X) *ᵥ v = (Xᵀ * X) *ᵥ w := hvw
    -- `XᵀX (v − w) = 0` gives `‖X (v − w)‖² = (v − w) ⬝ XᵀX (v − w) = 0`.
    have h0 : (Xᵀ * X) *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
    have h1 : (X *ᵥ (v - w)) ⬝ᵥ (X *ᵥ (v - w)) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, h0, zero_dotProduct]
    have h2 : X *ᵥ (v - w) = 0 := dotProduct_self_eq_zero.mp h1
    have : v - w = 0 := h (show X *ᵥ (v - w) = X *ᵥ 0 by rw [h2, mulVec_zero])
    exact sub_eq_zero.mp this

/-- `(XᵀX)⁻¹ Xᵀ` is a left inverse of `X` under full column rank. -/
lemma gram_inv_mul_self {X : Matrix n k ℝ} (hX : IsUnit (Xᵀ * X).det) :
    (Xᵀ * X)⁻¹ * Xᵀ * X = 1 := by
  rw [Matrix.mul_assoc, nonsing_inv_mul _ hX]

/-- With full column rank, the OLS formula solves the normal equations. -/
theorem normalEquations_ols {X : Matrix n k ℝ} (hX : IsUnit (Xᵀ * X).det) (y : n → ℝ) :
    NormalEquations X y (ols X y) := by
  unfold NormalEquations ols
  rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hX, one_mulVec, sub_self]

/-- With full column rank, the normal equations have only the OLS solution. -/
theorem eq_ols_of_normalEquations {X : Matrix n k ℝ} (hX : IsUnit (Xᵀ * X).det)
    {y : n → ℝ} {b : k → ℝ} (h : NormalEquations X y b) : b = ols X y := by
  unfold NormalEquations at h
  rw [mulVec_sub, sub_eq_zero, mulVec_mulVec] at h
  unfold ols
  rw [h, mulVec_mulVec, nonsing_inv_mul _ hX, one_mulVec]

/-- **OLS (Hayashi eq. 1.2.5).** Under full column rank, `b` minimises the sum
of squared residuals if and only if `b = (XᵀX)⁻¹ Xᵀ y`. In particular the
least-squares estimate exists and is unique. -/
theorem isLeastSquares_iff_eq_ols {X : Matrix n k ℝ} (hX : IsUnit (Xᵀ * X).det)
    (y : n → ℝ) (b : k → ℝ) : IsLeastSquares X y b ↔ b = ols X y := by
  rw [isLeastSquares_iff_normalEquations]
  exact ⟨eq_ols_of_normalEquations hX, fun h => h ▸ normalEquations_ols hX y⟩

/-! ## Projection matrices -/

section Projection

variable [DecidableEq n]

/-- The projection ("hat") matrix `P = X (XᵀX)⁻¹ Xᵀ`. -/
noncomputable def hat (X : Matrix n k ℝ) : Matrix n n ℝ := X * (Xᵀ * X)⁻¹ * Xᵀ

/-- The annihilator ("residual maker") `M = I − P`. -/
noncomputable def annihilator (X : Matrix n k ℝ) : Matrix n n ℝ := 1 - hat X

variable {X : Matrix n k ℝ}

omit [DecidableEq n] in
/-- `P X = X`: projecting a column of `X` leaves it unchanged. -/
theorem hat_mul_self (hX : IsUnit (Xᵀ * X).det) : hat X * X = X := by
  unfold hat
  rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hX, Matrix.mul_one]

omit [DecidableEq n] in
/-- `P` is idempotent: projecting twice is projecting once. -/
theorem hat_idempotent (hX : IsUnit (Xᵀ * X).det) : hat X * hat X = hat X := by
  unfold hat
  rw [show X * (Xᵀ * X)⁻¹ * Xᵀ * (X * (Xᵀ * X)⁻¹ * Xᵀ)
      = X * ((Xᵀ * X)⁻¹ * (Xᵀ * X) * (Xᵀ * X)⁻¹) * Xᵀ by simp only [Matrix.mul_assoc],
    nonsing_inv_mul _ hX, Matrix.one_mul]

omit [DecidableEq n] in
/-- `P` is symmetric. -/
theorem hat_transpose : (hat X)ᵀ = hat X := by
  unfold hat
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_nonsing_inv,
    transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- `M X = 0`: the residual maker annihilates the regressors. -/
theorem annihilator_mul_self (hX : IsUnit (Xᵀ * X).det) : annihilator X * X = 0 := by
  rw [annihilator, Matrix.sub_mul, Matrix.one_mul, hat_mul_self hX, sub_self]

/-- `M` is idempotent. -/
theorem annihilator_idempotent (hX : IsUnit (Xᵀ * X).det) :
    annihilator X * annihilator X = annihilator X := by
  unfold annihilator
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hat_idempotent hX]
  abel

/-- `M` is symmetric. -/
theorem annihilator_transpose : (annihilator X)ᵀ = annihilator X := by
  rw [annihilator, transpose_sub, transpose_one, hat_transpose]

omit [DecidableEq n] in
/-- Fitted values are the projection of `y`: `X b = P y`. -/
theorem fitted_eq_hat (y : n → ℝ) : X *ᵥ ols X y = hat X *ᵥ y := by
  unfold ols hat
  rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- Residuals are `M y`. -/
theorem residual_eq_annihilator (y : n → ℝ) : y - X *ᵥ ols X y = annihilator X *ᵥ y := by
  rw [fitted_eq_hat, annihilator, sub_mulVec, one_mulVec]

/-- A vector orthogonal to the columns of `X` is fixed by `M`. -/
theorem annihilator_mulVec_of_orthogonal {r : n → ℝ} (hr : Xᵀ *ᵥ r = 0) :
    annihilator X *ᵥ r = r := by
  unfold annihilator hat
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hr, mulVec_zero, sub_zero]

end Projection

/-! ## Frisch–Waugh–Lovell -/

section FWL

variable [DecidableEq n] {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂] [DecidableEq k₁]
  [DecidableEq k₂]

omit [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] in
/-- The normal equations for a partitioned regressor matrix `[X₁ X₂]` split into
orthogonality to `X₁` and to `X₂`. -/
theorem normalEquations_fromCols_iff (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    (b : k₁ ⊕ k₂ → ℝ) :
    NormalEquations (fromCols X₁ X₂) y b ↔
      X₁ᵀ *ᵥ (y - fromCols X₁ X₂ *ᵥ b) = 0 ∧ X₂ᵀ *ᵥ (y - fromCols X₁ X₂ *ᵥ b) = 0 := by
  unfold NormalEquations
  rw [transpose_fromCols, fromRows_mulVec]
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
  · rintro ⟨h₁, h₂⟩
    funext i
    rcases i with i | i
    · exact congrFun h₁ i
    · exact congrFun h₂ i

omit [DecidableEq k₂] in
/-- **Frisch–Waugh–Lovell theorem** (Davidson–MacKinnon Thm 2.1). Let `b` be a
least-squares estimate in the regression of `y` on `[X₁ X₂]`, and let `M₁` be
the residual maker of `X₁` (assumed of full column rank). Then the `X₂` block of
`b` is a least-squares estimate in the regression of `M₁ y` on `M₁ X₂`, and the
two regressions have identical residuals. -/
theorem fwl {X₁ : Matrix n k₁ ℝ} (X₂ : Matrix n k₂ ℝ) (h₁ : IsUnit (X₁ᵀ * X₁).det)
    (y : n → ℝ) (b : k₁ ⊕ k₂ → ℝ) (hb : IsLeastSquares (fromCols X₁ X₂) y b) :
    IsLeastSquares (annihilator X₁ * X₂) (annihilator X₁ *ᵥ y) (b ∘ Sum.inr) ∧
      annihilator X₁ *ᵥ y - (annihilator X₁ * X₂) *ᵥ (b ∘ Sum.inr)
        = y - fromCols X₁ X₂ *ᵥ b := by
  rw [isLeastSquares_iff_normalEquations, normalEquations_fromCols_iff] at hb
  obtain ⟨hr₁, hr₂⟩ := hb
  set r := y - fromCols X₁ X₂ *ᵥ b with hr
  -- `M₁ y − M₁ X₂ b₂ = M₁ (X₁ b₁ + r) = M₁ r = r`.
  have hres : annihilator X₁ *ᵥ y - (annihilator X₁ * X₂) *ᵥ (b ∘ Sum.inr) = r := by
    have hy : y = X₁ *ᵥ (b ∘ Sum.inl) + X₂ *ᵥ (b ∘ Sum.inr) + r := by
      rw [hr, fromCols_mulVec]; abel
    conv_lhs => rw [hy]
    rw [mulVec_add, mulVec_add, mulVec_mulVec, annihilator_mul_self h₁, zero_mulVec,
      ← mulVec_mulVec, annihilator_mulVec_of_orthogonal hr₁]
    abel
  refine ⟨?_, hres⟩
  rw [isLeastSquares_iff_normalEquations, NormalEquations, hres, transpose_mul,
    annihilator_transpose, ← mulVec_mulVec, annihilator_mulVec_of_orthogonal hr₁, hr₂]

/-- If `[X₁ X₂]` has full column rank, so does the residualised block `M₁ X₂`:
if `M₁ X₂ u = 0` then `X₂ u = X₁ c` for `c = (X₁ᵀX₁)⁻¹X₁ᵀX₂ u`, so
`[X₁ X₂] (−c, u) = 0`, forcing `u = 0`. -/
theorem isUnit_det_gram_annihilator_mul {X₁ : Matrix n k₁ ℝ} {X₂ : Matrix n k₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) :
    IsUnit ((annihilator X₁ * X₂)ᵀ * (annihilator X₁ * X₂)).det := by
  rw [isUnit_det_gram_iff] at h ⊢
  intro v w hvw
  replace hvw : (annihilator X₁ * X₂) *ᵥ v = (annihilator X₁ * X₂) *ᵥ w := hvw
  set u := v - w with hu
  have h0 : annihilator X₁ *ᵥ (X₂ *ᵥ u) = 0 := by
    rw [mulVec_mulVec, hu, mulVec_sub, hvw, sub_self]
  set c := (X₁ᵀ * X₁)⁻¹ *ᵥ (X₁ᵀ *ᵥ (X₂ *ᵥ u)) with hc
  have hX₂ : X₂ *ᵥ u = X₁ *ᵥ c := by
    have : X₂ *ᵥ u - hat X₁ *ᵥ (X₂ *ᵥ u) = 0 := by
      rw [annihilator, sub_mulVec, one_mulVec] at h0; exact h0
    rw [sub_eq_zero] at this
    rw [this, hat, hc]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  have hz : fromCols X₁ X₂ *ᵥ Sum.elim (-c) u = fromCols X₁ X₂ *ᵥ 0 := by
    rw [fromCols_mulVec_sumElim, mulVec_neg, hX₂, mulVec_zero, neg_add_cancel]
  have hu0 : u = 0 := funext fun i => by simpa using congrFun (h hz) (Sum.inr i)
  exact sub_eq_zero.mp hu0

omit [DecidableEq n] in
/-- If `[X₁ X₂]` has full column rank, so does its first block `X₁`. -/
theorem isUnit_det_gram_left {X₁ : Matrix n k₁ ℝ} {X₂ : Matrix n k₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) : IsUnit (X₁ᵀ * X₁).det := by
  rw [isUnit_det_gram_iff] at h ⊢
  intro v w hvw
  replace hvw : X₁ *ᵥ v = X₁ *ᵥ w := hvw
  have hz : fromCols X₁ X₂ *ᵥ Sum.elim v 0 = fromCols X₁ X₂ *ᵥ Sum.elim w 0 := by
    rw [fromCols_mulVec_sumElim, fromCols_mulVec_sumElim, hvw]
  exact funext fun i => by simpa using congrFun (h hz) (Sum.inl i)

/-- FWL in formula form: if `[X₁ X₂]` has full column rank, the OLS
coefficients on `X₂` equal `(X₂ᵀ M₁ X₂)⁻¹ X₂ᵀ M₁ y`, the OLS coefficients from
regressing `M₁ y` on `M₁ X₂`. -/
theorem ols_inr_eq {X₁ : Matrix n k₁ ℝ} {X₂ : Matrix n k₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) (y : n → ℝ) :
    ols (fromCols X₁ X₂) y ∘ Sum.inr = ols (annihilator X₁ * X₂) (annihilator X₁ *ᵥ y) := by
  have hb := (isLeastSquares_iff_eq_ols h y _).mpr rfl
  exact (isLeastSquares_iff_eq_ols (isUnit_det_gram_annihilator_mul h) _ _).mp
    (fwl X₂ (isUnit_det_gram_left h) y _ hb).1

end FWL

/-! ## Omitted-variable bias -/

/-- **Omitted-variable bias** (Angrist–Pischke §3.2.2). If the true model is
`y = X₁ β₁ + X₂ β₂ + ε` and we regress `y` on `X₁` alone, the OLS coefficient is
`β₁ + δ β₂ + (X₁ᵀX₁)⁻¹ X₁ᵀ ε`, where `δ = (X₁ᵀX₁)⁻¹ X₁ᵀ X₂` collects the
coefficients from regressing each omitted regressor on `X₁`. -/
theorem ols_omitted {k₂ : Type*} [Fintype k₂] {X₁ : Matrix n k ℝ} (X₂ : Matrix n k₂ ℝ)
    (h₁ : IsUnit (X₁ᵀ * X₁).det) (β₁ : k → ℝ) (β₂ : k₂ → ℝ) (ε : n → ℝ) :
    ols X₁ (X₁ *ᵥ β₁ + X₂ *ᵥ β₂ + ε)
      = β₁ + ((X₁ᵀ * X₁)⁻¹ * X₁ᵀ * X₂) *ᵥ β₂ + ols X₁ ε := by
  unfold ols
  simp only [mulVec_add, mulVec_mulVec, Matrix.mul_assoc]
  rw [nonsing_inv_mul _ h₁, one_mulVec]

/-! ## Unbiasedness -/

section Unbiased

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- OLS is linear in the data: `ols X (X β + ε) = β + (XᵀX)⁻¹Xᵀ ε`. -/
theorem ols_linear_model {X : Matrix n k ℝ} (hX : IsUnit (Xᵀ * X).det) (β : k → ℝ)
    (ε : n → ℝ) : ols X (X *ᵥ β + ε) = β + ((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ ε := by
  unfold ols
  simp only [mulVec_add, mulVec_mulVec]
  rw [nonsing_inv_mul _ hX, one_mulVec]

/-- **Unbiasedness of OLS** (Hayashi Prop. 1.1(a), fixed design). In the linear
model `y = X β + ε` with full-column-rank `X` and integrable errors with mean
zero, `E[b] = β`, coefficient by coefficient. -/
theorem integral_ols [IsProbabilityMeasure μ] {X : Matrix n k ℝ} (hX : IsUnit (Xᵀ * X).det)
    (β : k → ℝ) (ε : Ω → n → ℝ) (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (j : k) :
    ∫ ω, ols X (X *ᵥ β + ε ω) j ∂μ = β j := by
  simp_rw [ols_linear_model hX, Pi.add_apply, mulVec, dotProduct]
  rw [integral_add (integrable_const _)
      (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
    integral_finsetSum _ fun i _ => (hint i).const_mul _]
  simp [integral_const_mul, hmean]

end Unbiased

end Econ.OLS
