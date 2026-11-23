/-
# Generalised least squares and robust standard errors

Aitken (1935); Hayashi, *Econometrics* (2000), §1.6 and §2.5; White (1980);
MacKinnon and White (1985); Newey and West (1987).

**The results.** In the linear model `y = Xβ + ε` with fixed design and error
second-moment matrix `E[εεᵀ] = V` (positive definite):

* **Aitken's theorem**: the GLS estimator `β̂_GLS = (XᵀV⁻¹X)⁻¹XᵀV⁻¹y` is linear
  unbiased with covariance `(XᵀV⁻¹X)⁻¹`, and every linear unbiased estimator has
  covariance at least that large (`cov_gls`, `aitken`); in particular OLS is no
  better than GLS (`ols_cov_sub_gls_posSemidef`).
* **Transformation**: if `V = LLᵀ`, GLS is OLS on the whitened data `L⁻¹y`,
  `L⁻¹X` (`gls_eq_ols_transformed`).
* **Heteroskedasticity-robust covariance** (White 1980): with uncorrelated errors
  of variances `σᵢ²`, the OLS covariance is the sandwich
  `(XᵀX)⁻¹ Xᵀ diag(σ²) X (XᵀX)⁻¹` (`cov_ols_hetero`); the HC0 estimator is
  positive semidefinite (`hc0_posSemidef`) and its infeasible version with the
  true errors is unbiased (`integral_sandwich_sq`).
* **Leverage and HC2** (MacKinnon–White 1985): residuals have second moments
  `M V M`; under homoskedasticity `E[eᵢ²] = σ²(1 − hᵢᵢ)`, so `eᵢ²/(1 − hᵢᵢ)` is
  unbiased for `σ²` (`secondMoments_resid`, `hc2_unbiased`).
* **Newey–West** (1987): the Bartlett-weighted long-run covariance estimator
  `Σₜ Σₛ (1 − |t−s|/(L+1))⁺ gₜ gₛᵀ` is positive semidefinite for any data
  (`neweyWest_posSemidef`), unlike the unweighted truncated estimator
  (`truncated_not_posSemidef`).
-/
module

public import EconLean.Econometrics.GaussMarkov
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace Econ.OLS

open Matrix MeasureTheory

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-! ## Generalised least squares -/

/-- The GLS weight matrix `(XᵀV⁻¹X)⁻¹ Xᵀ V⁻¹`. -/
noncomputable def glsMat (V : Matrix n n ℝ) (X : Matrix n k ℝ) : Matrix k n ℝ :=
  (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * V⁻¹

/-- The GLS estimator `β̂_GLS = (XᵀV⁻¹X)⁻¹ XᵀV⁻¹ y`. -/
noncomputable def gls (V : Matrix n n ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  glsMat V X *ᵥ y

variable {V : Matrix n n ℝ} {X : Matrix n k ℝ}

/-- GLS is unbiased: `C_GLS X = I`. -/
lemma glsMat_mul (hA : IsUnit (Xᵀ * V⁻¹ * X).det) : glsMat V X * X = 1 := by
  rw [glsMat, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, nonsing_inv_mul _ hA]

lemma transpose_of_posDef {m : Type*} [Fintype m] {A : Matrix m m ℝ} (hA : A.PosDef) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.1

lemma isUnit_det_of_posDef {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℝ}
    (hA : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.mpr hA.det_pos.ne'

/-- The GLS covariance identity `C_GLS V C_GLSᵀ = (XᵀV⁻¹X)⁻¹`. -/
lemma glsMat_mul_mul_transpose (hV : V.PosDef) (hA : IsUnit (Xᵀ * V⁻¹ * X).det) :
    glsMat V X * V * (glsMat V X)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
  have hVt := transpose_of_posDef hV
  have hVu := isUnit_det_of_posDef hV
  have hAt : (Xᵀ * V⁻¹ * X)ᵀ = Xᵀ * V⁻¹ * X := by
    rw [transpose_mul, transpose_mul, transpose_transpose, transpose_nonsing_inv, hVt,
      Matrix.mul_assoc]
  rw [glsMat, transpose_mul, transpose_mul, transpose_nonsing_inv, transpose_nonsing_inv, hAt,
    hVt, transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V⁻¹ V, nonsing_inv_mul _ hVu, Matrix.one_mul]
  have hA' : IsUnit (Xᵀ * (V⁻¹ * X)).det := by rwa [← Matrix.mul_assoc]
  rw [show (Xᵀ * (V⁻¹ * X))⁻¹ * (Xᵀ * (V⁻¹ * (X * (Xᵀ * (V⁻¹ * X))⁻¹)))
      = (Xᵀ * (V⁻¹ * X))⁻¹ * (Xᵀ * (V⁻¹ * X)) * (Xᵀ * (V⁻¹ * X))⁻¹ by
        simp only [Matrix.mul_assoc],
    nonsing_inv_mul _ hA', Matrix.one_mul]

/-- **Aitken's theorem, matrix form**: for every `C` with `C X = I`,
`C V Cᵀ − (XᵀV⁻¹X)⁻¹` is positive semidefinite. -/
theorem aitken_matrix (hV : V.PosDef) (hA : IsUnit (Xᵀ * V⁻¹ * X).det) {C : Matrix k n ℝ}
    (hC : C * X = 1) : (C * V * Cᵀ - (Xᵀ * V⁻¹ * X)⁻¹).PosSemidef := by
  have hVt := transpose_of_posDef hV
  have hVu := isUnit_det_of_posDef hV
  set G := glsMat V X with hG
  set D := C - G with hD
  have hDX : D * X = 0 := by rw [hD, Matrix.sub_mul, hC, glsMat_mul hA, sub_self]
  have hDVG : D * V * Gᵀ = 0 := by
    rw [hG, glsMat, transpose_mul, transpose_mul, transpose_nonsing_inv, hVt,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V V⁻¹, mul_nonsing_inv _ hVu, Matrix.one_mul,
      ← Matrix.mul_assoc D X, hDX, Matrix.zero_mul]
  have hGVD : G * V * Dᵀ = 0 := by
    have : (D * V * Gᵀ)ᵀ = G * V * Dᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, hVt, Matrix.mul_assoc]
    rw [← this, hDVG, transpose_zero]
  have hCG : C = G + D := by rw [hD]; abel
  have key : C * V * Cᵀ - (Xᵀ * V⁻¹ * X)⁻¹ = D * V * Dᵀ := by
    rw [← glsMat_mul_mul_transpose hV hA, ← hG, hCG, transpose_add, Matrix.add_mul,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hGVD, hDVG]
    abel
  rw [key]
  simpa [conjTranspose_eq_transpose_of_trivial] using hV.posSemidef.mul_mul_conjTranspose_same D

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ε : Ω → n → ℝ}

/-- **Covariance of GLS**: with `E[εεᵀ] = V`, `Var(β̂_GLS) = (XᵀV⁻¹X)⁻¹`. -/
theorem cov_gls (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (hvar : secondMoments μ ε = V) (hV : V.PosDef) (hA : IsUnit (Xᵀ * V⁻¹ * X).det)
    (β : k → ℝ) :
    cov μ (fun ω => gls V X (X *ᵥ β + ε ω)) = (Xᵀ * V⁻¹ * X)⁻¹ := by
  simp only [gls]
  rw [cov_linear hε hεε hmean, hvar, glsMat_mul_mul_transpose hV hA]

/-- **Aitken's theorem** (Aitken 1935; Hayashi Prop. 1.7): with `E[εεᵀ] = V`
positive definite, GLS is the best linear unbiased estimator: for every `C` with
`C X = I`, `Var(C y) − Var(β̂_GLS)` is positive semidefinite. -/
theorem aitken (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (hvar : secondMoments μ ε = V) (hV : V.PosDef) (hA : IsUnit (Xᵀ * V⁻¹ * X).det)
    {C : Matrix k n ℝ} (hC : C * X = 1) (β : k → ℝ) :
    (cov μ (fun ω => C *ᵥ (X *ᵥ β + ε ω)) - cov μ (fun ω => gls V X (X *ᵥ β + ε ω))).PosSemidef := by
  rw [cov_gls hε hεε hmean hvar hV hA, cov_linear hε hεε hmean, hvar]
  exact aitken_matrix hV hA hC

/-- **OLS is inefficient under non-spherical errors**: `Var(β̂_OLS) − Var(β̂_GLS)`
is positive semidefinite. -/
theorem ols_cov_sub_gls_posSemidef (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (hvar : secondMoments μ ε = V) (hV : V.PosDef) (hA : IsUnit (Xᵀ * V⁻¹ * X).det)
    (hX : IsUnit (Xᵀ * X).det) (β : k → ℝ) :
    (cov μ (fun ω => ols X (X *ᵥ β + ε ω)) - cov μ (fun ω => gls V X (X *ᵥ β + ε ω))).PosSemidef := by
  simp only [ols_eq_mulVec]
  exact aitken hε hεε hmean hvar hV hA (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hX]) β

/-- **GLS is OLS on whitened data** (Hayashi §1.6): if `V = L Lᵀ` with `L`
invertible, then `β̂_GLS(y) = β̂_OLS(L⁻¹X, L⁻¹y)`. (The identity is formal in
Lean's total inverse, so no invertibility hypothesis is needed.) -/
theorem gls_eq_ols_transformed {L : Matrix n n ℝ} (hV : V = L * Lᵀ)
    (y : n → ℝ) : gls V X y = ols (L⁻¹ * X) (L⁻¹ *ᵥ y) := by
  have hVi : V⁻¹ = L⁻¹ᵀ * L⁻¹ := by
    rw [hV, Matrix.mul_inv_rev, transpose_nonsing_inv]
  have hgram : (L⁻¹ * X)ᵀ * (L⁻¹ * X) = Xᵀ * V⁻¹ * X := by
    rw [hVi, transpose_mul]; simp only [Matrix.mul_assoc]
  rw [ols, hgram, gls, glsMat, hVi, transpose_mul, mulVec_mulVec, mulVec_mulVec]
  simp only [Matrix.mul_assoc]

/-! ## Heteroskedasticity-robust covariance -/

/-- The sandwich `(XᵀX)⁻¹ Xᵀ diag(w) X (XᵀX)⁻¹`. -/
noncomputable def sandwich (X : Matrix n k ℝ) (w : n → ℝ) : Matrix k k ℝ :=
  (Xᵀ * X)⁻¹ * (Xᵀ * diagonal w * X) * (Xᵀ * X)⁻¹

/-- The HC0 (White) covariance estimator with residuals `e`. -/
noncomputable def hc0 (X : Matrix n k ℝ) (e : n → ℝ) : Matrix k k ℝ :=
  sandwich X fun i => e i ^ 2

/-- The sandwich is `C₀ diag(w) C₀ᵀ` with `C₀ = (XᵀX)⁻¹Xᵀ`. -/
lemma sandwich_eq (X : Matrix n k ℝ) (w : n → ℝ) :
    sandwich X w = ((Xᵀ * X)⁻¹ * Xᵀ) * diagonal w * ((Xᵀ * X)⁻¹ * Xᵀ)ᵀ := by
  rw [sandwich, transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_mul,
    transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- The sandwich is positive semidefinite for nonnegative weights. -/
theorem sandwich_posSemidef (X : Matrix n k ℝ) {w : n → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (sandwich X w).PosSemidef := by
  rw [sandwich_eq]
  have hd : (diagonal w).PosSemidef := PosSemidef.diagonal hw
  have := hd.mul_mul_conjTranspose_same ((Xᵀ * X)⁻¹ * Xᵀ)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **The White (HC0) estimator is positive semidefinite**. -/
theorem hc0_posSemidef (X : Matrix n k ℝ) (e : n → ℝ) : (hc0 X e).PosSemidef :=
  sandwich_posSemidef X fun i => sq_nonneg (e i)

/-- **Covariance of OLS under heteroskedasticity** (White 1980; Hayashi §2.5):
with uncorrelated errors of variances `σᵢ²` (`E[εεᵀ] = diag σ²`), `Var(β̂_OLS)`
is the sandwich `(XᵀX)⁻¹ Xᵀ diag(σ²) X (XᵀX)⁻¹`. -/
theorem cov_ols_hetero (hε : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    {σ2 : n → ℝ} (hvar : secondMoments μ ε = diagonal σ2) (β : k → ℝ) :
    cov μ (fun ω => ols X (X *ᵥ β + ε ω)) = sandwich X σ2 := by
  simp only [ols_eq_mulVec]
  rw [cov_linear hε hεε hmean, hvar, sandwich_eq]

/-- Entries of the sandwich are linear in the weights. -/
lemma sandwich_apply (X : Matrix n k ℝ) (w : n → ℝ) (a b : k) :
    sandwich X w a b
      = ∑ i, ((Xᵀ * X)⁻¹ * Xᵀ) a i * ((Xᵀ * X)⁻¹ * Xᵀ) b i * w i := by
  rw [sandwich_eq, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, transpose_apply]; ring

omit [IsProbabilityMeasure μ] in
/-- **The infeasible White estimator is unbiased**: with the true errors in
place of residuals, `E[(XᵀX)⁻¹ Xᵀ diag(ε²) X (XᵀX)⁻¹] = Var(β̂_OLS)` under
`E[εεᵀ] = diag σ²`. The feasible HC0 built from OLS residuals is biased in
finite samples (`integral_resid_sq`), which motivates HC2 (`hc2_unbiased`). -/
theorem integral_sandwich_sq (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ)
    {σ2 : n → ℝ} (hvar : secondMoments μ ε = diagonal σ2) (a b : k) :
    ∫ ω, sandwich X (fun i => ε ω i ^ 2) a b ∂μ = sandwich X σ2 a b := by
  simp only [sandwich_apply]
  rw [integral_finsetSum _ fun i _ => by simpa [sq] using (hεε i i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  have := congrFun (congrFun hvar i) i
  simp only [secondMoments, of_apply, diagonal_apply_eq] at this
  simpa [sq] using this

/-! ## Residuals, leverage and HC2 -/

omit [IsProbabilityMeasure μ] in
/-- **Second moments of the residuals**: `e = M y = M ε` and `E[eeᵀ] = M V M`. -/
theorem secondMoments_resid (hX : IsUnit (Xᵀ * X).det)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) (β : k → ℝ) :
    secondMoments μ (fun ω => annihilator X *ᵥ (X *ᵥ β + ε ω))
      = annihilator X * secondMoments μ ε * annihilator X := by
  have he : ∀ ω, annihilator X *ᵥ (X *ᵥ β + ε ω) = annihilator X *ᵥ ε ω := by
    intro ω
    rw [mulVec_add, mulVec_mulVec, annihilator_mul_self hX, zero_mulVec, zero_add]
  ext a b
  simp only [he]
  rw [show secondMoments μ (fun ω => annihilator X *ᵥ ε ω) a b
      = ∫ ω, (annihilator X *ᵥ ε ω) a * (annihilator X *ᵥ ε ω) b ∂μ from rfl,
    integral_mulVec_mul_mulVec hεε, annihilator_transpose]

omit [IsProbabilityMeasure μ] in
/-- **Leverage and residual variance** (MacKinnon–White 1985): under
homoskedasticity `E[εεᵀ] = σ² I`, `E[eᵢ²] = σ² (1 − hᵢᵢ)`. -/
theorem integral_resid_sq (hX : IsUnit (Xᵀ * X).det)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) {σ2 : ℝ}
    (hvar : secondMoments μ ε = σ2 • (1 : Matrix n n ℝ)) (β : k → ℝ) (i : n) :
    ∫ ω, (annihilator X *ᵥ (X *ᵥ β + ε ω)) i ^ 2 ∂μ = σ2 * (1 - hat X i i) := by
  have := congrFun (congrFun (secondMoments_resid hX hεε β) i) i
  rw [hvar] at this
  simp only [secondMoments, of_apply] at this
  simp only [sq]
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, annihilator_idempotent hX]
  simp [annihilator, one_apply_eq, smul_eq_mul]

omit [IsProbabilityMeasure μ] in
/-- **HC2 is unbiased under homoskedasticity** (MacKinnon–White 1985): with
leverage `hᵢᵢ ≠ 1`, `E[eᵢ²/(1 − hᵢᵢ)] = σ²`. -/
theorem hc2_unbiased (hX : IsUnit (Xᵀ * X).det)
    (hεε : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ) {σ2 : ℝ}
    (hvar : secondMoments μ ε = σ2 • (1 : Matrix n n ℝ)) (β : k → ℝ) {i : n}
    (hi : hat X i i ≠ 1) :
    ∫ ω, (annihilator X *ᵥ (X *ᵥ β + ε ω)) i ^ 2 / (1 - hat X i i) ∂μ = σ2 := by
  rw [integral_div, integral_resid_sq hX hεε hvar β i]
  field_simp [sub_ne_zero.mpr (Ne.symm hi)]

/-! ## Newey–West -/

/-- The window indicator `Bₜₘ = 1[t ≤ m ≤ t + L]`, `m < T + L`. -/
def nwWindow (T L : ℕ) : Matrix (Fin T) (Fin (T + L)) ℝ :=
  fun t m => if (t : ℕ) ≤ m ∧ (m : ℕ) ≤ t + L then 1 else 0

/-- The Bartlett kernel matrix `Kₜₛ = (L + 1 − |t − s|)⁺ / (L + 1)`. -/
noncomputable def bartlett (T L : ℕ) : Matrix (Fin T) (Fin T) ℝ :=
  fun t s => ((L + 1 - (max (t : ℕ) s - min (t : ℕ) s) : ℕ) : ℝ) / (L + 1)

/-- The Bartlett matrix factors through overlapping windows: `K = B Bᵀ / (L + 1)`. -/
lemma bartlett_eq (T L : ℕ) : bartlett T L = (1 / ((L : ℝ) + 1)) • (nwWindow T L * (nwWindow T L)ᵀ) := by
  ext t s
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [transpose_apply, nwWindow, ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter fun m : Fin (T + L) =>
      ((t : ℕ) ≤ m ∧ (m : ℕ) ≤ t + L) ∧ ((s : ℕ) ≤ m ∧ (m : ℕ) ≤ s + L)).card
      = (Finset.Icc (max (t : ℕ) s) (min (t : ℕ) s + L)).card := by
    rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
    congr 1
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Finset.mem_Icc]
    constructor
    · rintro ⟨m, hm, rfl⟩; omega
    · intro hm
      exact ⟨⟨m, by have := t.2; have := s.2; omega⟩, by simp; omega, rfl⟩
  rw [hcard, Nat.card_Icc]
  unfold bartlett
  rw [div_eq_mul_one_div, mul_comm]
  congr 2
  omega

/-- The Bartlett kernel matrix is positive semidefinite. -/
theorem bartlett_posSemidef (T L : ℕ) : (bartlett T L).PosSemidef := by
  rw [bartlett_eq]
  have := posSemidef_self_mul_conjTranspose (nwWindow T L)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this.smul (by positivity)

/-- The Newey–West long-run covariance estimator
`Ŝ = Σₜ Σₛ (1 − |t−s|/(L+1))⁺ gₜ gₛᵀ` for moment contributions `g : Fin T → ℝᵖ`. It is unnormalised (it equals `T`
times the usual `Ŝ`) and does not demean `g`; neither affects positive
semidefiniteness. -/
noncomputable def neweyWest {p : Type*} [Fintype p] (T L : ℕ) (g : Matrix (Fin T) p ℝ) :
    Matrix p p ℝ :=
  gᵀ * bartlett T L * g

/-- **The Newey–West estimator is positive semidefinite** (Newey and West 1987,
Thm 1) for every data set and lag length. -/
theorem neweyWest_posSemidef {p : Type*} [Fintype p] (T L : ℕ) (g : Matrix (Fin T) p ℝ) :
    (neweyWest T L g).PosSemidef := by
  simpa [neweyWest, conjTranspose_eq_transpose_of_trivial] using
    (bartlett_posSemidef T L).mul_mul_conjTranspose_same gᵀ

/-- **Why the weights matter**: the unweighted truncated estimator
`Σ_{|t−s| ≤ L} gₜ gₛ` need not be positive semidefinite (`T = 3`, `L = 1`,
`g = (1, −1, 1)` gives `−1`). -/
theorem truncated_not_posSemidef :
    let K : Matrix (Fin 3) (Fin 3) ℝ := fun t s => if max (t : ℕ) s - min (t : ℕ) s ≤ 1 then 1 else 0
    let g : Fin 3 → ℝ := ![1, -1, 1]
    g ⬝ᵥ (K *ᵥ g) < 0 := by
  intro K g
  simp [K, g, dotProduct, mulVec, Fin.sum_univ_three]

/-- **Non-vacuity** of the GLS hypotheses: a two-observation heteroskedastic
design `V = diag(1, 4)` with a constant regressor is positive definite with
`XᵀV⁻¹X` invertible, and the GLS weights `(4/5, 1/5)` differ from OLS's
`(1/2, 1/2)`. -/
theorem gls_witness :
    let V : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, 4]
    let X : Matrix (Fin 2) Unit ℝ := Matrix.of fun _ _ => 1
    V.PosDef ∧ IsUnit (Xᵀ * V⁻¹ * X).det ∧
      glsMat V X = Matrix.of fun _ i => ![4 / 5, 1 / 5] i := by
  intro V X
  have hVi : V⁻¹ = diagonal ![1, 1 / 4] := by
    rw [inv_eq_left_inv]
    ext i j; fin_cases i <;> fin_cases j <;> simp [V]
  have hA : Xᵀ * V⁻¹ * X = Matrix.of fun _ _ => 5 / 4 := by
    rw [hVi]; ext; simp [X, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply]; norm_num
  have hAi : (Matrix.of fun _ _ => (5 / 4 : ℝ) : Matrix Unit Unit ℝ)⁻¹
      = Matrix.of fun _ _ => 4 / 5 := by
    rw [inv_eq_left_inv]; ext; simp [Matrix.mul_apply]
  refine ⟨PosDef.diagonal fun i => by fin_cases i <;> norm_num, ?_, ?_⟩
  · rw [hA, det_unique]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  · rw [glsMat, hA, hVi, hAi]
    ext u i; fin_cases i <;> simp [X, Matrix.mul_apply, diagonal_apply]
    norm_num

end Econ.OLS
