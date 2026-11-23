/-
# Linear instrumental variables and two-stage least squares

Hayashi, *Econometrics* (2000), §3.3–3.8; Wooldridge, *Econometric Analysis of
Cross Section and Panel Data* (2010), §5.1–5.2; Wright (1928).

**The economics.** In `y = x ⬝ β + ε` the regressors `x` may be correlated with
the error (simultaneity, omitted variables, measurement error), so OLS is
inconsistent. Instruments `z` (`L` of them) are *exogenous*, `E[z ε] = 0`, and
*relevant*.

* **Identification (rank condition)** (Hayashi Prop. 3.1; Wooldridge Thm 5.1).
  Exogeneity gives the population moment equations `Σ_zx β = σ_zy`, where
  `Σ_zx = E[z xᵀ]` and `σ_zy = E[z y]`. `β` is the unique solution of these
  equations if and only if `Σ_zx` has full column rank (`Σ_zx b = 0 ⇒ b = 0`).
  If the rank condition fails, some `β' ≠ β` satisfies the same moment
  equations, so `β` is not identified from them.
* **2SLS algebra** (Hayashi §3.8). With data matrices `X` (`n × K`),
  `Z` (`n × L`), `y`: `β̂_2SLS = (Xᵀ P_Z X)⁻¹ Xᵀ P_Z y`. It is OLS of `y` on the
  first-stage fitted values `X̂ = P_Z X` (the "two stages"), and in the
  just-identified case (`L = K`, `ZᵀX` invertible) it is the IV estimator
  `(ZᵀX)⁻¹ Zᵀ y`.

**Encoding.** Population moments are integrals over a probability space; the
`L × K` matrix `Σ_zx` is `Matrix l k ℝ`. "Exogeneity" is `E[z_i ε] = 0` for each
instrument, with the integrability needed for the moments to exist.
-/
module

public import EconLean.Econometrics.OLS

@[expose] public section

namespace Econ.IV

open Matrix MeasureTheory OLS

section Population

variable {Ω : Type*} [MeasurableSpace Ω] {l k : Type*} [Fintype k]

/-- `Σ_zx = E[z xᵀ]`. -/
noncomputable def momentZX (μ : Measure Ω) (z : Ω → l → ℝ) (x : Ω → k → ℝ) : Matrix l k ℝ :=
  Matrix.of fun i j => ∫ ω, z ω i * x ω j ∂μ

/-- `σ_zy = E[z y]`. -/
noncomputable def momentZY (μ : Measure Ω) (z : Ω → l → ℝ) (y : Ω → ℝ) : l → ℝ :=
  fun i => ∫ ω, z ω i * y ω ∂μ

/-- The set of coefficient vectors satisfying the population IV moment equations
`Σ_zx b = σ_zy`. -/
def momentSolutions (μ : Measure Ω) (z : Ω → l → ℝ) (x : Ω → k → ℝ) (y : Ω → ℝ) :
    Set (k → ℝ) :=
  {b | momentZX μ z x *ᵥ b = momentZY μ z y}

variable {μ : Measure Ω}

/-- Exogeneity makes the true `β` solve the moment equations:
`E[z (xᵀβ + ε)] = E[z xᵀ] β + E[z ε] = Σ_zx β`. -/
theorem mem_momentSolutions {z : Ω → l → ℝ} {x : Ω → k → ℝ} {ε : Ω → ℝ} (β : k → ℝ)
    (hzx : ∀ i j, Integrable (fun ω => z ω i * x ω j) μ)
    (hzε : ∀ i, Integrable (fun ω => z ω i * ε ω) μ)
    (hexo : ∀ i, ∫ ω, z ω i * ε ω ∂μ = 0) :
    β ∈ momentSolutions μ z x (fun ω => x ω ⬝ᵥ β + ε ω) := by
  funext i
  simp only [momentZX, momentZY, mulVec, dotProduct, of_apply]
  have hsum : (fun ω => z ω i * (∑ j, x ω j * β j + ε ω))
      = fun ω => (∑ j, β j * (z ω i * x ω j)) + z ω i * ε ω := by
    funext ω; rw [mul_add, Finset.mul_sum]; congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, integral_add (integrable_finsetSum _ fun j _ => (hzx i j).const_mul _) (hzε i),
    integral_finsetSum _ fun j _ => (hzx i j).const_mul _, hexo i, add_zero]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, mul_comm]

/-- **IV identification: the rank condition** (Hayashi Prop. 3.1; Wooldridge
Thm 5.1). Under exogeneity, the true `β` is the *only* solution of the
population moment equations if and only if `Σ_zx` has full column rank. -/
theorem momentSolutions_eq_singleton_iff {z : Ω → l → ℝ} {x : Ω → k → ℝ} {ε : Ω → ℝ}
    (β : k → ℝ) (hzx : ∀ i j, Integrable (fun ω => z ω i * x ω j) μ)
    (hzε : ∀ i, Integrable (fun ω => z ω i * ε ω) μ)
    (hexo : ∀ i, ∫ ω, z ω i * ε ω ∂μ = 0) :
    momentSolutions μ z x (fun ω => x ω ⬝ᵥ β + ε ω) = {β} ↔
      Function.Injective (momentZX μ z x *ᵥ ·) := by
  have hβ := mem_momentSolutions β hzx hzε hexo
  constructor
  · intro h v w hvw
    replace hvw : momentZX μ z x *ᵥ v = momentZX μ z x *ᵥ w := hvw
    -- `β + v − w` also solves the moment equations, so it equals `β`.
    have hmem : β + (v - w) ∈ momentSolutions μ z x (fun ω => x ω ⬝ᵥ β + ε ω) := by
      show momentZX μ z x *ᵥ (β + (v - w)) = _
      rw [mulVec_add, mulVec_sub, hvw, sub_self, add_zero]; exact hβ
    rw [h] at hmem
    have : v - w = 0 := by simpa using hmem
    exact sub_eq_zero.mp this
  · intro hinj
    ext b
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hb
      exact hinj (show momentZX μ z x *ᵥ b = momentZX μ z x *ᵥ β from hb.trans hβ.symm)
    · rintro rfl; exact hβ

end Population

section TwoStage

variable {n k l : Type*} [Fintype n] [Fintype k] [Fintype l] [DecidableEq k]
  [DecidableEq l]

/-- The 2SLS estimator `(Xᵀ P_Z X)⁻¹ Xᵀ P_Z y`. -/
noncomputable def tsls (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ) : k → ℝ :=
  (Xᵀ * hat Z * X)⁻¹ *ᵥ ((Xᵀ * hat Z) *ᵥ y)

/-- **2SLS = OLS on first-stage fitted values.** With `X̂ = P_Z X` (the fitted
values from regressing each regressor on the instruments), `β̂_2SLS` is the OLS
coefficient from regressing `y` on `X̂`. -/
theorem tsls_eq_ols_fitted {X : Matrix n k ℝ} {Z : Matrix n l ℝ}
    (hZ : IsUnit (Zᵀ * Z).det) (y : n → ℝ) :
    tsls X Z y = ols (hat Z * X) y := by
  have hgram : (hat Z * X)ᵀ * (hat Z * X) = Xᵀ * hat Z * X := by
    rw [transpose_mul, hat_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (hat Z) (hat Z),
      hat_idempotent hZ, Matrix.mul_assoc]
  unfold tsls ols
  rw [hgram, transpose_mul, hat_transpose]

/-- **Just-identified case: 2SLS = IV.** If there are as many instruments as
regressors and `ZᵀX` is invertible, `β̂_2SLS = (ZᵀX)⁻¹ Zᵀ y`. -/
theorem tsls_eq_iv {X Z : Matrix n k ℝ} (hZ : IsUnit (Zᵀ * Z).det)
    (hZX : IsUnit (Zᵀ * X).det) (y : n → ℝ) :
    tsls X Z y = (Zᵀ * X)⁻¹ *ᵥ (Zᵀ *ᵥ y) := by
  have hXZ : IsUnit (Xᵀ * Z).det := by
    rw [show Xᵀ * Z = (Zᵀ * X)ᵀ by rw [transpose_mul, transpose_transpose], det_transpose]
    exact hZX
  -- `Xᵀ P_Z X = (XᵀZ)(ZᵀZ)⁻¹(ZᵀX)`, whose inverse is `(ZᵀX)⁻¹(ZᵀZ)(XᵀZ)⁻¹`.
  have hA : Xᵀ * hat Z * X = (Xᵀ * Z) * (Zᵀ * Z)⁻¹ * (Zᵀ * X) := by
    simp only [hat, Matrix.mul_assoc]
  have hinv : (Xᵀ * hat Z * X)⁻¹ = (Zᵀ * X)⁻¹ * (Zᵀ * Z) * (Xᵀ * Z)⁻¹ := by
    rw [hA, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ]
    simp only [Matrix.mul_assoc]
  have key : (Zᵀ * X)⁻¹ * (Zᵀ * Z) * (Xᵀ * Z)⁻¹ * (Xᵀ * Z * (Zᵀ * Z)⁻¹ * Zᵀ)
      = (Zᵀ * X)⁻¹ * Zᵀ := by
    calc _ = (Zᵀ * X)⁻¹ * (Zᵀ * Z) * ((Xᵀ * Z)⁻¹ * (Xᵀ * Z)) * (Zᵀ * Z)⁻¹ * Zᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Zᵀ * X)⁻¹ * ((Zᵀ * Z) * (Zᵀ * Z)⁻¹) * Zᵀ := by
          rw [nonsing_inv_mul _ hXZ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hZ, Matrix.mul_one]
  unfold tsls
  rw [hinv, mulVec_mulVec, mulVec_mulVec,
    show Xᵀ * hat Z = Xᵀ * Z * (Zᵀ * Z)⁻¹ * Zᵀ by simp only [hat, Matrix.mul_assoc], key]

end TwoStage

end Econ.IV
