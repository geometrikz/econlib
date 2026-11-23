/-
# Linear GMM: identification, the estimator, and the efficient weighting matrix

Hansen (1982); Hayashi, *Econometrics* (2000), §3.4–3.6; Newey–McFadden (1994),
§2.2.3 and Thm 5.2.

**The economics.** In the linear instrumental-variables model the population
moment conditions are `E[z (y − xᵀβ)] = 0`, i.e. `g(β) = σ − G β = 0` with
`G = Σ_zx` (`L × K`) and `σ = σ_zy`. With more instruments than regressors the
equations are overdetermined, and GMM picks `b` to minimise the quadratic form
`Q_W(b) = g(b)ᵀ W g(b)` for a symmetric positive-definite weighting matrix `W`.

* **Identification** (Hayashi Prop. 3.1 for GMM; Newey–McFadden Lemma 2.3):
  for any positive-definite `W`, `β` is the unique minimiser of the population
  criterion if and only if `G` has full column rank.
* **The estimator** (Hayashi (3.5.6)): when `GᵀWG` is invertible, the unique
  minimiser of `Q_W` is `b̂(W) = (GᵀWG)⁻¹ GᵀW σ`. This holds for population and
  sample moments alike (it is pure algebra), and with exact moments
  `σ = G β` it returns `β`. With sample moments `G = ZᵀX`, `σ = Zᵀy` and
  `W = (ZᵀZ)⁻¹` it is 2SLS (Hayashi §3.8).
* **Efficient weighting** (Hansen 1982 Thm 3.2; Hayashi Prop. 3.5): the
  asymptotic variance of `b̂(W)` is the sandwich
  `Avar(W) = (GᵀWG)⁻¹ GᵀW S WG (GᵀWG)⁻¹`, `S = Var(z ε)`. Choosing `W = S⁻¹`
  gives `(Gᵀ S⁻¹ G)⁻¹`, and `Avar(W) − (Gᵀ S⁻¹ G)⁻¹` is positive semidefinite
  for every admissible `W`.

**Scope.** This file is the algebraic part: the probabilistic statement that
`√n (b̂ − β)` is asymptotically normal with variance `Avar(W)` is not proved here.
-/
module

public import EconLean.Econometrics.IV
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace Econ.GMM

open Matrix

variable {l k : Type*} [Fintype l] [Fintype k]

/-- The linear moment function `g(b) = σ − G b`. -/
def moment (G : Matrix l k ℝ) (σ : l → ℝ) (b : k → ℝ) : l → ℝ :=
  σ - G *ᵥ b

/-- The GMM criterion `Q_W(b) = g(b)ᵀ W g(b)`. -/
def criterion (W : Matrix l l ℝ) (G : Matrix l k ℝ) (σ : l → ℝ) (b : k → ℝ) : ℝ :=
  moment G σ b ⬝ᵥ (W *ᵥ moment G σ b)

lemma transpose_eq_of_posDef {m : Type*} [Fintype m] {A : Matrix m m ℝ} (hA : A.PosDef) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.1

/-- `x ⬝ W y = y ⬝ W x` for symmetric `W`. -/
lemma dotProduct_mulVec_comm {m : Type*} [Fintype m] {A : Matrix m m ℝ} (hA : Aᵀ = A)
    (x y : m → ℝ) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

/-- `(G d) ⬝ y = d ⬝ (Gᵀ y)`. -/
lemma mulVec_dotProduct (G : Matrix l k ℝ) (d : k → ℝ) (y : l → ℝ) :
    (G *ᵥ d) ⬝ᵥ y = d ⬝ᵥ (Gᵀ *ᵥ y) := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- The criterion is nonnegative for a positive-semidefinite weighting matrix. -/
theorem criterion_nonneg {W : Matrix l l ℝ} (hW : W.PosSemidef) (G : Matrix l k ℝ)
    (σ : l → ℝ) (b : k → ℝ) : 0 ≤ criterion W G σ b := by
  simpa [criterion] using hW.dotProduct_mulVec_nonneg (moment G σ b)

/-- With exact moments `σ = Gβ`, the criterion at `b` is the quadratic form of
`G (β − b)`. -/
lemma criterion_of_exact {W : Matrix l l ℝ} {G : Matrix l k ℝ} {β : k → ℝ} (b : k → ℝ) :
    criterion W G (G *ᵥ β) b = (G *ᵥ (β - b)) ⬝ᵥ (W *ᵥ (G *ᵥ (β - b))) := by
  simp [criterion, moment, mulVec_sub]

/-- **GMM identification** (Hayashi Prop. 3.1; Newey–McFadden Lemma 2.3). If the
population moments hold at `β` (`σ = Gβ`) and `W` is positive definite, then `β`
is the unique minimiser of the population criterion (`Q(β) = 0 < Q(b)` for all
`b ≠ β`) if and only if `G` has full column rank. -/
theorem identified_iff {W : Matrix l l ℝ} (hW : W.PosDef) (G : Matrix l k ℝ) (β : k → ℝ) :
    (criterion W G (G *ᵥ β) β = 0 ∧ ∀ b, b ≠ β → criterion W G (G *ᵥ β) β < criterion W G (G *ᵥ β) b)
      ↔ Function.Injective (G *ᵥ ·) := by
  have h0 : criterion W G (G *ᵥ β) β = 0 := by simp [criterion_of_exact]
  constructor
  · rintro ⟨-, h⟩ v w hvw
    replace hvw : G *ᵥ v = G *ᵥ w := hvw
    by_contra hne
    have hb : β + (v - w) ≠ β := by
      intro h'; exact hne (sub_eq_zero.mp (by simpa using h'))
    have := h _ hb
    rw [h0, criterion_of_exact, show β - (β + (v - w)) = -(v - w) by abel, mulVec_neg,
      mulVec_sub, hvw, sub_self, neg_zero, mulVec_zero, dotProduct_zero] at this
    exact lt_irrefl _ this
  · intro hG
    refine ⟨h0, fun b hb => ?_⟩
    rw [h0, criterion_of_exact]
    have hne : G *ᵥ (β - b) ≠ 0 := by
      intro h
      exact hb (sub_eq_zero.mp (hG (by simpa using h)) ).symm
    simpa using hW.dotProduct_mulVec_pos hne

section Estimator

variable [DecidableEq k]

/-- The linear GMM estimator `b̂(W) = (GᵀWG)⁻¹ GᵀW σ`. -/
noncomputable def estimator (W : Matrix l l ℝ) (G : Matrix l k ℝ) (σ : l → ℝ) : k → ℝ :=
  (Gᵀ * W * G)⁻¹ *ᵥ ((Gᵀ * W) *ᵥ σ)

omit [DecidableEq k] in
/-- `GᵀWG` is positive definite when `W` is and `G` has full column rank. -/
lemma posDef_gram {W : Matrix l l ℝ} (hW : W.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) : (Gᵀ * W * G).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hW.conjTranspose_mul_mul_same hG

lemma isUnit_det_gram {W : Matrix l l ℝ} (hW : W.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) : IsUnit (Gᵀ * W * G).det :=
  (isUnit_iff_isUnit_det _).mp (posDef_gram hW hG).isUnit

/-- First-order condition: `GᵀW g(b̂) = 0`. -/
lemma foc {W : Matrix l l ℝ} {G : Matrix l k ℝ} (h : IsUnit (Gᵀ * W * G).det) (σ : l → ℝ) :
    (Gᵀ * W) *ᵥ moment G σ (estimator W G σ) = 0 := by
  rw [moment, estimator, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ h,
    one_mulVec, sub_self]

/-- **Quadratic decomposition of the criterion** around `b̂`:
`Q(b) = Q(b̂) + (b − b̂)ᵀ GᵀWG (b − b̂)`. -/
theorem criterion_eq_add {W : Matrix l l ℝ} (hW : Wᵀ = W) {G : Matrix l k ℝ}
    (h : IsUnit (Gᵀ * W * G).det) (σ : l → ℝ) (b : k → ℝ) :
    criterion W G σ b = criterion W G σ (estimator W G σ)
      + (b - estimator W G σ) ⬝ᵥ ((Gᵀ * W * G) *ᵥ (b - estimator W G σ)) := by
  set e := estimator W G σ
  set r := moment G σ e
  set d := b - e
  have hm : moment G σ b = r - G *ᵥ d := by
    simp only [r, d, moment, mulVec_sub]; abel
  have hfoc : (G *ᵥ d) ⬝ᵥ (W *ᵥ r) = 0 := by
    rw [mulVec_dotProduct, mulVec_mulVec, foc h, dotProduct_zero]
  have hquad : (G *ᵥ d) ⬝ᵥ (W *ᵥ (G *ᵥ d)) = d ⬝ᵥ ((Gᵀ * W * G) *ᵥ d) := by
    rw [mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]
  have hsym : r ⬝ᵥ (W *ᵥ (G *ᵥ d)) = 0 := by rw [dotProduct_mulVec_comm hW, hfoc]
  simp only [criterion, hm, mulVec_sub, sub_dotProduct, dotProduct_sub, hfoc, hsym, hquad]
  ring

/-- **The GMM estimator is the unique minimiser of the criterion** (Hayashi
(3.5.6)): for positive-definite `W` and full-column-rank `G`,
`Q(b̂) < Q(b)` for every `b ≠ b̂`. -/
theorem estimator_isMin {W : Matrix l l ℝ} (hW : W.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) (σ : l → ℝ) (b : k → ℝ) (hb : b ≠ estimator W G σ) :
    criterion W G σ (estimator W G σ) < criterion W G σ b := by
  rw [criterion_eq_add (transpose_eq_of_posDef hW) (isUnit_det_gram hW hG) σ b]
  have := (posDef_gram hW hG).dotProduct_mulVec_pos (sub_ne_zero.mpr hb)
  simp only [star_trivial] at this
  linarith

/-- With exact moments `σ = Gβ` the GMM estimator returns `β`, for any weighting
matrix with `GᵀWG` invertible. -/
theorem estimator_of_exact {W : Matrix l l ℝ} {G : Matrix l k ℝ}
    (h : IsUnit (Gᵀ * W * G).det) (β : k → ℝ) : estimator W G (G *ᵥ β) = β := by
  rw [estimator, mulVec_mulVec, mulVec_mulVec,
    show (Gᵀ * W * G)⁻¹ * (Gᵀ * W) * G = (Gᵀ * W * G)⁻¹ * (Gᵀ * W * G) by
      simp only [Matrix.mul_assoc],
    nonsing_inv_mul _ h, one_mulVec]

/-- **2SLS is GMM** with `W = (ZᵀZ)⁻¹` (Hayashi §3.8): with sample moments
`G = ZᵀX`, `σ = Zᵀy`, the GMM estimator is `β̂_2SLS`. -/
theorem tsls_eq_estimator {n : Type*} [Fintype n] [DecidableEq l] (X : Matrix n k ℝ)
    (Z : Matrix n l ℝ) (y : n → ℝ) :
    IV.tsls X Z y = estimator (Zᵀ * Z)⁻¹ (Zᵀ * X) (Zᵀ *ᵥ y) := by
  simp only [IV.tsls, estimator, OLS.hat, transpose_mul, transpose_transpose, mulVec_mulVec,
    Matrix.mul_assoc]

end Estimator

section Efficient

variable [DecidableEq k] [DecidableEq l]

/-- The sandwich asymptotic variance of `b̂(W)` when `S = Var(z ε)`:
`(GᵀWG)⁻¹ GᵀWSWG (GᵀWG)⁻¹`. -/
noncomputable def avar (W : Matrix l l ℝ) (G : Matrix l k ℝ) (S : Matrix l l ℝ) :
    Matrix k k ℝ :=
  (Gᵀ * W * G)⁻¹ * (Gᵀ * W * S * W * G) * (Gᵀ * W * G)⁻¹

omit [DecidableEq l] in
lemma transpose_inv_gram {W : Matrix l l ℝ} (hW : Wᵀ = W) (G : Matrix l k ℝ) :
    (Gᵀ * W * G)⁻¹ᵀ = (Gᵀ * W * G)⁻¹ := by
  rw [transpose_nonsing_inv, transpose_mul, transpose_mul, transpose_transpose, hW,
    Matrix.mul_assoc]

/-- With the optimal weighting `W = S⁻¹`, the sandwich collapses to
`(Gᵀ S⁻¹ G)⁻¹`. -/
theorem avar_inv {S : Matrix l l ℝ} (hS : S.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) : avar S⁻¹ G S = (Gᵀ * S⁻¹ * G)⁻¹ := by
  have hu := isUnit_det_gram hS.inv hG
  have hSdet : IsUnit S.det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have : Gᵀ * S⁻¹ * S * S⁻¹ * G = Gᵀ * S⁻¹ * G := by
    rw [Matrix.mul_assoc (Gᵀ * S⁻¹), mul_nonsing_inv _ hSdet, Matrix.mul_one]
  rw [avar, this, nonsing_inv_mul _ hu, Matrix.one_mul]

/-- **Efficiency of `W = S⁻¹`** (Hansen 1982 Thm 3.2; Hayashi Prop. 3.5). For any
positive-definite weighting matrix `W`, a positive-definite `S` and full-column-rank
`G`, `Avar(W) − (Gᵀ S⁻¹ G)⁻¹` is positive semidefinite. The proof writes the
difference as `(A − B) S (A − B)ᵀ` with `A = (GᵀWG)⁻¹GᵀW` and
`B = (GᵀS⁻¹G)⁻¹GᵀS⁻¹`. -/
theorem avar_sub_posSemidef {W S : Matrix l l ℝ} (hW : W.PosDef) (hS : S.PosDef)
    {G : Matrix l k ℝ} (hG : Function.Injective (G *ᵥ ·)) :
    (avar W G S - (Gᵀ * S⁻¹ * G)⁻¹).PosSemidef := by
  have hWt := transpose_eq_of_posDef hW
  have hSt := transpose_eq_of_posDef hS
  have hSit : S⁻¹ᵀ = S⁻¹ := transpose_eq_of_posDef hS.inv
  have hSdet : IsUnit S.det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have huW := isUnit_det_gram hW hG
  have huS := isUnit_det_gram hS.inv hG
  set V := (Gᵀ * S⁻¹ * G)⁻¹ with hVdef
  have hVt : Vᵀ = V := transpose_inv_gram hSit G
  set A := (Gᵀ * W * G)⁻¹ * Gᵀ * W with hA
  set B := V * Gᵀ * S⁻¹ with hB
  have hAG : A * G = 1 := by
    rw [hA, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Gᵀ, nonsing_inv_mul _ huW]
  have hBS : B * S = V * Gᵀ := by
    rw [hB, Matrix.mul_assoc, nonsing_inv_mul _ hSdet, Matrix.mul_one]
  have hBG : B * G = 1 := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Gᵀ, hVdef,
      nonsing_inv_mul _ huS]
  have hBSA : B * S * Aᵀ = V := by
    rw [hBS, Matrix.mul_assoc, ← transpose_mul, hAG, transpose_one, Matrix.mul_one]
  have hBSB : B * S * Bᵀ = V := by
    rw [hBS, Matrix.mul_assoc, ← transpose_mul, hBG, transpose_one, Matrix.mul_one]
  have hASB : A * S * Bᵀ = V := by
    rw [Matrix.mul_assoc, ← hSt, ← transpose_mul, hBS, transpose_mul, transpose_transpose,
      ← Matrix.mul_assoc, hAG, Matrix.one_mul, hVt]
  have hASA : A * S * Aᵀ = avar W G S := by
    rw [hA, avar, transpose_mul, transpose_mul, hWt, transpose_inv_gram hWt, transpose_transpose]
    simp only [Matrix.mul_assoc]
  have key : avar W G S - V = (A - B) * S * (A - B)ᵀ := by
    rw [transpose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hASA,
      hASB, hBSA, hBSB]
    abel
  rw [key, ← conjTranspose_eq_transpose_of_trivial]
  exact hS.posSemidef.mul_mul_conjTranspose_same _

end Efficient

end Econ.GMM
