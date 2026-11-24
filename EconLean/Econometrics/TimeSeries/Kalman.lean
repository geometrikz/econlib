/-
# The Kalman filter: optimal linear updating

Kalman (1960); Hamilton, *Time Series Analysis* (1994), §13.2; Anderson and
Moore, *Optimal Filtering* (1979), §3.1; Durbin and Koopman (2012), §4.3.

**The model.** A state `x` has prior mean `m` and prior error `e = x − m` with
`E[eeᵀ] = P`; it is observed as `y = Hx + v` with noise `E[vvᵀ] = R` uncorrelated
with `e`. A linear update `x̂ = m + K (y − Hm)` has error `x − x̂ = (I − KH)e − Kv`.

**The results.**

* **Error covariance of any gain** (Joseph form): `E[(x − x̂)(x − x̂)ᵀ] =
  (I − KH) P (I − KH)ᵀ + K R Kᵀ` (`secondMoments_update_error`).
* **The Kalman gain is optimal**: with innovation covariance `S = HPHᵀ + R`
  invertible and `K* = PHᵀS⁻¹`, every gain `K` has error covariance exceeding that
  of `K*` by `(K − K*) S (K − K*)ᵀ`, which is positive semidefinite
  (`joseph_sub_gain`, `kalman_gain_optimal`).
* **Posterior covariance**: `P − PHᵀS⁻¹HP` (`joseph_gain`).
* **Prediction step**: with `x' = Fx + w`, `E[ww ᵀ] = Q`, `w` uncorrelated with the
  error, the predicted error covariance is `FPFᵀ + Q` (`secondMoments_predict`).

Iterating predict and update gives the Kalman filter recursion; this file proves
the one-step optimality that the recursion repeats, not the multi-period recursion,
the Riccati steady state, or the Gaussian conditional-expectation form. With `R`
positive definite the gain is also unique (`kalman_gain_unique`). "Covariance"
here means second moments of the errors (MSE matrices), which are covariances
when the errors are mean zero. Gaussianity is not needed:
the gain is optimal among linear updates for any errors with these second
moments.
-/
module

public import EconLean.Econometrics.GaussMarkov
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

namespace Econ.TimeSeries.Kalman

open Matrix MeasureTheory Econ.OLS

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The innovation covariance `S = HPHᵀ + R`. -/
def innovCov (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ) : Matrix m m ℝ :=
  H * P * Hᵀ + R

/-- The Kalman gain `K* = PHᵀS⁻¹`. -/
noncomputable def gain (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ) : Matrix n m ℝ :=
  P * Hᵀ * (innovCov P H R)⁻¹

/-- The Joseph-form error covariance `(I − KH) P (I − KH)ᵀ + K R Kᵀ` of the gain `K`. -/
def joseph (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ) (K : Matrix n m ℝ) :
    Matrix n n ℝ :=
  (1 - K * H) * P * (1 - K * H)ᵀ + K * R * Kᵀ

variable {P : Matrix n n ℝ} {H : Matrix m n ℝ} {R : Matrix m m ℝ}

omit [DecidableEq m] in
/-- Expansion `J(K) = P − KHP − PHᵀKᵀ + KSKᵀ`. -/
lemma joseph_expand (K : Matrix n m ℝ) :
    joseph P H R K = P - K * (H * P) - P * Hᵀ * Kᵀ + K * innovCov P H R * Kᵀ := by
  simp only [joseph, innovCov, transpose_sub, transpose_one, transpose_mul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]
  abel

omit [DecidableEq n] in
/-- `K* S = PHᵀ`. -/
lemma gain_mul_innovCov (hS : IsUnit (innovCov P H R).det) :
    gain P H R * innovCov P H R = P * Hᵀ := by
  rw [gain, Matrix.mul_assoc, nonsing_inv_mul _ hS, Matrix.mul_one]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma innovCov_transpose (hP : Pᵀ = P) (hR : Rᵀ = R) : (innovCov P H R)ᵀ = innovCov P H R := by
  rw [innovCov, transpose_add, transpose_mul, transpose_mul, transpose_transpose, hP, hR,
    Matrix.mul_assoc]

omit [DecidableEq n] in
/-- `S K*ᵀ = HP`. -/
lemma innovCov_mul_gain_transpose (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hS : IsUnit (innovCov P H R).det) :
    innovCov P H R * (gain P H R)ᵀ = H * P := by
  have := congrArg transpose (gain_mul_innovCov (P := P) (H := H) (R := R) hS)
  rw [transpose_mul, transpose_mul, transpose_transpose, hP, innovCov_transpose hP hR] at this
  exact this

/-- **Optimality of the Kalman gain, exact form**: for every gain `K`,
`J(K) − J(K*) = (K − K*) S (K − K*)ᵀ`. -/
theorem joseph_sub_gain (hP : Pᵀ = P) (hR : Rᵀ = R) (hS : IsUnit (innovCov P H R).det)
    (K : Matrix n m ℝ) :
    joseph P H R K - joseph P H R (gain P H R)
      = (K - gain P H R) * innovCov P H R * (K - gain P H R)ᵀ := by
  set G := gain P H R
  set S := innovCov P H R
  have h1 : H * P = S * Gᵀ := (innovCov_mul_gain_transpose hP hR hS).symm
  have h2 : P * Hᵀ = G * S := (gain_mul_innovCov hS).symm
  rw [joseph_expand, joseph_expand, h1, h2]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **Posterior covariance**: `J(K*) = P − PHᵀS⁻¹HP`. -/
theorem joseph_gain (hP : Pᵀ = P) (hR : Rᵀ = R) (hS : IsUnit (innovCov P H R).det) :
    joseph P H R (gain P H R) = P - P * Hᵀ * (innovCov P H R)⁻¹ * (H * P) := by
  have h1 : H * P = innovCov P H R * (gain P H R)ᵀ :=
    (innovCov_mul_gain_transpose hP hR hS).symm
  have h2 : P * Hᵀ = gain P H R * innovCov P H R := (gain_mul_innovCov hS).symm
  rw [show P * Hᵀ * (innovCov P H R)⁻¹ = gain P H R from rfl, joseph_expand, h2,
    Matrix.mul_assoc (gain P H R) (innovCov P H R), ← h1]
  abel

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- The innovation covariance is positive semidefinite when `P` and `R` are. -/
lemma innovCov_posSemidef (hP : P.PosSemidef) (hR : R.PosSemidef) :
    (innovCov P H R).PosSemidef := by
  have := hP.mul_mul_conjTranspose_same H
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this.add hR

/-- **The Kalman gain minimises the error covariance** (Kalman 1960; Anderson–Moore
§3.1): with `P`, `R` positive semidefinite and `S` invertible, `J(K) − J(K*)` is
positive semidefinite for every gain `K`. -/
theorem kalman_gain_optimal (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hS : IsUnit (innovCov P H R).det) (K : Matrix n m ℝ) :
    (joseph P H R K - joseph P H R (gain P H R)).PosSemidef := by
  have hPt : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.1
  have hRt : Rᵀ = R := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hR.1
  rw [joseph_sub_gain hPt hRt hS]
  have := (innovCov_posSemidef (H := H) hP hR).mul_mul_conjTranspose_same (K - gain P H R)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- With measurement noise of positive definite covariance, the innovation
covariance is positive definite. -/
lemma innovCov_posDef (hP : P.PosSemidef) (hR : R.PosDef) : (innovCov P H R).PosDef := by
  have := hP.mul_mul_conjTranspose_same H
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact PosDef.posSemidef_add this hR

omit [DecidableEq n] in
/-- `R` positive definite gives the invertibility hypothesis of the gain results. -/
lemma isUnit_innovCov (hP : P.PosSemidef) (hR : R.PosDef) : IsUnit (innovCov P H R).det :=
  isUnit_iff_ne_zero.mpr (innovCov_posDef hP hR).det_pos.ne'

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
lemma mul_mul_transpose_apply_self (D : Matrix n m ℝ) (S : Matrix m m ℝ) (i : n) :
    (D * S * Dᵀ) i i = D i ⬝ᵥ (S *ᵥ D i) := by
  simp only [Matrix.mul_apply, transpose_apply, mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Uniqueness of the optimal gain**: with `R` positive definite, a gain with
the same error covariance as the Kalman gain is the Kalman gain. -/
theorem kalman_gain_unique (hP : P.PosSemidef) (hR : R.PosDef) {K : Matrix n m ℝ}
    (h : joseph P H R K = joseph P H R (gain P H R)) : K = gain P H R := by
  have hPt : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.1
  have hRt : Rᵀ = R := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hR.1
  have hS := innovCov_posDef (H := H) hP hR
  have h0 := joseph_sub_gain (H := H) hPt hRt (isUnit_innovCov hP hR) K
  rw [h, sub_self] at h0
  rw [← sub_eq_zero]
  ext i j
  by_contra hne
  have hrow : (K - gain P H R) i ≠ 0 := fun h' => hne (by simpa using congrFun h' j)
  have hpos := hS.dotProduct_mulVec_pos hrow
  simp only [star_trivial] at hpos
  have := congrFun (congrFun h0 i) i
  rw [mul_mul_transpose_apply_self] at this
  simp only [Matrix.zero_apply] at this
  linarith

/-! ## Second moments of the update and prediction errors -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq m] in
/-- **Error of a linear update**: with `x = m + e` and `y = Hx + v`, the error of
`x̂ = m + K(y − Hm)` is `(I − KH)e − Kv`, i.e. `[I − KH, −K]` applied to `(e, v)`. -/
lemma update_error (K : Matrix n m ℝ) (mean e : n → ℝ) (v : m → ℝ) :
    (mean + e) - (mean + K *ᵥ (H *ᵥ (mean + e) + v - H *ᵥ mean))
      = fromCols (1 - K * H) (-K) *ᵥ Sum.elim e v := by
  rw [fromCols_mulVec_sumElim]
  simp only [mulVec_add, mulVec_sub, sub_mulVec, one_mulVec, neg_mulVec, ← mulVec_mulVec]
  abel

omit [DecidableEq m] in
/-- **Joseph form**: if the stacked vector `z = (e, v)` has second moments
`[[P, 0], [0, R]]` (prior error uncorrelated with the noise), the update error
`[I − KH, −K] z` has second moments `J(K)`. -/
theorem secondMoments_update_error {z : Ω → n ⊕ m → ℝ}
    (hzz : ∀ i j, Integrable (fun ω => z ω i * z ω j) μ)
    (hz : secondMoments μ z = fromBlocks P 0 0 R) (K : Matrix n m ℝ) :
    secondMoments μ (fun ω => fromCols (1 - K * H) (-K) *ᵥ z ω) = joseph P H R K := by
  ext a b
  rw [show secondMoments μ (fun ω => fromCols (1 - K * H) (-K) *ᵥ z ω) a b
      = ∫ ω, (fromCols (1 - K * H) (-K) *ᵥ z ω) a * (fromCols (1 - K * H) (-K) *ᵥ z ω) b ∂μ
      from rfl, integral_mulVec_mul_mulVec hzz, hz, fromCols_mul_fromBlocks, transpose_fromCols,
    fromCols_mul_fromRows]
  simp [joseph, Matrix.neg_mul, Matrix.mul_neg]

omit [DecidableEq m] in
/-- **Prediction step**: if `(e, w)` has second moments `[[P, 0], [0, Q]]`, the
predicted error `Fe + w` has second moments `FPFᵀ + Q`. -/
theorem secondMoments_predict {z : Ω → n ⊕ n → ℝ}
    (hzz : ∀ i j, Integrable (fun ω => z ω i * z ω j) μ) {Q : Matrix n n ℝ}
    (hz : secondMoments μ z = fromBlocks P 0 0 Q) (F : Matrix n n ℝ) :
    secondMoments μ (fun ω => fromCols F 1 *ᵥ z ω) = F * P * Fᵀ + Q := by
  ext a b
  rw [show secondMoments μ (fun ω => fromCols F 1 *ᵥ z ω) a b
      = ∫ ω, (fromCols F 1 *ᵥ z ω) a * (fromCols F 1 *ᵥ z ω) b ∂μ from rfl,
    integral_mulVec_mul_mulVec hzz, hz, fromCols_mul_fromBlocks, transpose_fromCols,
    fromCols_mul_fromRows]
  simp

/-- **Non-vacuity**: a scalar state with prior variance `1`, `H = 1` and noise
variance `1` has innovation variance `2`, gain `1/2` and posterior variance `1/2`. -/
theorem kalman_witness :
    let P : Matrix Unit Unit ℝ := 1
    let H : Matrix Unit Unit ℝ := 1
    let R : Matrix Unit Unit ℝ := 1
    P.PosSemidef ∧ R.PosSemidef ∧ IsUnit (innovCov P H R).det ∧
      gain P H R = (1 / 2 : ℝ) • 1 ∧ joseph P H R (gain P H R) = (1 / 2 : ℝ) • 1 := by
  intro P H R
  have hS : innovCov P H R = (2 : ℝ) • 1 := by
    simp only [innovCov, P, H, R]; ext; simp; norm_num
  have hSi : (innovCov P H R)⁻¹ = (1 / 2 : ℝ) • 1 := by
    rw [hS, inv_eq_left_inv]; ext; simp
  have hG : gain P H R = (1 / 2 : ℝ) • 1 := by
    rw [gain, hSi]; simp [P, H]
  refine ⟨PosSemidef.one, PosSemidef.one, ?_, hG, ?_⟩
  · rw [hS]; simp
  · rw [hG]; ext; simp [joseph, P, H, R, Matrix.mul_apply]; norm_num

end Econ.TimeSeries.Kalman
