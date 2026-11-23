/-
# Structural VARs: recursive (Cholesky) identification

Sims (1980), *Econometrica* 48; Kilian and Lütkepohl, *Structural Vector
Autoregressive Analysis* (2017), §8.2; Hamilton, *Time Series Analysis* (1994),
§11.4 and §4.4 (triangular factorisation).

**The economics.** A VAR's reduced-form innovations `u_t` are linear
combinations of orthonormal structural shocks, `u_t = B ε_t` with
`Var(ε_t) = I`, so the data reveal only `Σ_u = B Bᵀ`. That leaves `B`
unidentified: `B Q` fits equally well for any orthogonal `Q`
(`observationallyEquivalent`, `not_identified`). Sims' recursive scheme imposes
that `B` is lower triangular with a positive diagonal (shock `j` has no
contemporaneous effect on variables ordered before `j`). Under this restriction
`B` exists and is unique for every positive-definite `Σ_u`: it is the Cholesky
factor (`recursive_existsUnique`).

**Encoding.** Variables are indexed by a finite linear order `n` (e.g.
`Fin k`); lower triangular is Mathlib's `Matrix.IsLowerTriangular`
(`B i j = 0` for `i < j`). Existence is derived from Mathlib's LDL
decomposition.
-/
module

public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Econ.TimeSeries.SVAR

open Matrix

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Recursive (Cholesky) identification restriction: `B` is lower triangular with
a positive diagonal. -/
def IsRecursive (B : Matrix n n ℝ) : Prop :=
  B.IsLowerTriangular ∧ ∀ i, 0 < B i i

omit [Fintype n] in
lemma lower_apply {M : Matrix n n ℝ} (h : M.IsLowerTriangular) {i j : n} (hij : i < j) :
    M i j = 0 :=
  h (by simpa using hij)

/-- **Non-identification without restrictions**: `B` and `BQ` imply the same
reduced-form covariance for every orthogonal `Q`. -/
theorem observationallyEquivalent (B Q : Matrix n n ℝ) (hQ : Q * Qᵀ = 1) :
    (B * Q) * (B * Q)ᵀ = B * Bᵀ := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ, Matrix.one_mul]

/-- **Uniqueness of the recursive factor** (Cholesky uniqueness): two recursive
impact matrices that imply the same covariance are equal. -/
theorem recursive_unique {B₁ B₂ : Matrix n n ℝ} (h₁ : IsRecursive B₁)
    (h₂ : IsRecursive B₂) (h : B₁ * B₁ᵀ = B₂ * B₂ᵀ) : B₁ = B₂ := by
  have hdet₂ : IsUnit B₂.det := by
    rw [det_of_isLowerTriangular _ h₂.1]
    exact (Finset.prod_pos fun i _ => h₂.2 i).ne'.isUnit
  have hdet₂t : IsUnit B₂ᵀ.det := by rwa [det_transpose]
  let _ := invertibleOfIsUnitDet B₂ hdet₂
  set M := B₂⁻¹ * B₁ with hMdef
  have hMlow : M.IsLowerTriangular :=
    (blockTriangular_inv_of_blockTriangular h₂.1).mul h₁.1
  have hB₁ : B₂ * M = B₁ := by rw [hMdef, mul_nonsing_inv_cancel_left _ _ hdet₂]
  have hMM : M * Mᵀ = 1 := by
    rw [hMdef, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, ← Matrix.mul_assoc B₁,
      h, Matrix.mul_assoc, mul_nonsing_inv _ hdet₂t, Matrix.mul_one, nonsing_inv_mul _ hdet₂]
  have hdetM : IsUnit M.det := isUnit_det_of_right_inverse hMM
  let _ := invertibleOfIsUnitDet M hdetM
  have hMt : Mᵀ.IsLowerTriangular := by
    have := blockTriangular_inv_of_blockTriangular (M := M) hMlow
    rwa [inv_eq_right_inv hMM] at this
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact lower_apply hMlow hlt
    · have := lower_apply hMt hlt; simpa using this
  have hdiag : ∀ i, B₁ i i = B₂ i i * M i i := by
    intro i
    rw [← hB₁, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hj; rw [hoff j i hj, mul_zero]
    · simp
  have hpos : ∀ i, 0 < M i i := fun i => by
    have := hdiag i
    have h1 := h₁.2 i; have h2 := h₂.2 i
    by_contra hle; push Not at hle
    nlinarith
  have hone : ∀ i, M i i = 1 := by
    intro i
    have := congrFun (congrFun hMM i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, one_apply_eq] at this
    · simp only [transpose_apply] at this
      nlinarith [hpos i]
    · intro j _ hj; simp [hoff i j (Ne.symm hj)]
    · simp
  have hM1 : M = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [hone, one_apply_eq]
    · rw [hoff i j hij, one_apply_ne hij]
  rw [← hB₁, hM1, Matrix.mul_one]

section Existence

variable [LocallyFiniteOrderBot n]

/-- **Existence of a recursive impact matrix** for every positive-definite
covariance (Cholesky decomposition), obtained from the LDL decomposition
`Σ = L D Lᵀ` by `B = L · diag(√dᵢ · |Lᵢᵢ| / Lᵢᵢ)`. -/
theorem recursive_exists {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∃ B, IsRecursive B ∧ B * Bᵀ = S := by
  -- Facts about the LDL factors.
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same (vecMul_injective_of_isUnit (isUnit_of_invertible _))
  have hd0 : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    have := hD.diag_pos (i := i)
    rwa [LDL.diag, diagonal_apply_eq] at this
  have hLdet0 : IsUnit (LDL.lower hS).det :=
    isUnit_nonsing_inv_det _ (isUnit_det_of_invertible (LDL.lowerInv hS))
  have hLlow := LDL.isLowerTriangular_lower hS
  have hS' : LDL.lower hS * diagonal (LDL.diagEntries hS) * (LDL.lower hS)ᵀ = S := by
    have := LDL.lower_conj_diag hS
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  generalize LDL.lower hS = L at hLdet0 hLlow hS'
  generalize LDL.diagEntries hS = d at hd0 hS'
  have hLii : ∀ i, L i i ≠ 0 := by
    intro i hi
    have := hLdet0.ne_zero
    rw [det_of_isLowerTriangular _ hLlow] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let v : n → ℝ := fun i => Real.sqrt (d i) * |L i i| / L i i
  have hv2 : ∀ i, v i * v i = d i := by
    intro i
    have hsq := Real.mul_self_sqrt (hd0 i).le
    have habs : |L i i| * |L i i| = L i i * L i i := abs_mul_abs_self _
    have hL := hLii i
    calc v i * v i = (Real.sqrt (d i) * Real.sqrt (d i)) * (|L i i| * |L i i|)
          / (L i i * L i i) := by simp only [v]; ring
      _ = d i := by rw [hsq, habs, mul_div_assoc, div_self (mul_ne_zero hL hL), mul_one]
  refine ⟨L * diagonal v, ⟨hLlow.mul (blockTriangular_diagonal _), fun i => ?_⟩, ?_⟩
  · rw [mul_diagonal]
    have : L i i * v i = Real.sqrt (d i) * |L i i| := by
      simp only [v]; field_simp [hLii i]
    rw [this]
    exact mul_pos (Real.sqrt_pos.mpr (hd0 i)) (abs_pos.mpr (hLii i))
  · rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal v),
      diagonal_mul_diagonal, ← Matrix.mul_assoc, ← hS']
    congr 2
    exact congrArg diagonal (funext hv2)

/-- **Recursive identification** (Sims 1980): for every positive-definite
reduced-form covariance `Σ_u` there is exactly one lower-triangular impact
matrix with positive diagonal such that `B Bᵀ = Σ_u`. -/
theorem recursive_existsUnique {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∃! B, IsRecursive B ∧ B * Bᵀ = S := by
  obtain ⟨B, hB, hBS⟩ := recursive_exists hS
  exact ⟨B, ⟨hB, hBS⟩, fun B' ⟨hB', hB'S⟩ =>
    recursive_unique hB' hB (hB'S.trans hBS.symm)⟩

end Existence

/-- **Without restrictions `B` is not identified**: the identity and a rotation
by 90° imply the same covariance `I`; only the first is recursive. -/
theorem not_identified :
    let B₁ : Matrix (Fin 2) (Fin 2) ℝ := 1
    let B₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
    B₁ * B₁ᵀ = B₂ * B₂ᵀ ∧ B₁ ≠ B₂ ∧ IsRecursive B₁ ∧ ¬ IsRecursive B₂ := by
  intro B₁ B₂
  refine ⟨?_, fun h => ?_, ⟨fun i j hij => ?_, fun i => ?_⟩, fun h => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [B₁, B₂, Matrix.mul_apply, Fin.sum_univ_two]
  · have := congrFun (congrFun h 0) 0; simp [B₁, B₂] at this
  · simp only [B₁]; exact one_apply_ne (by simp at hij; exact hij.ne)
  · simp [B₁]
  · have := h.2 0; simp [B₂] at this

/-- **The sign normalisation is needed**: `I` and `diag(−1, 1)` are both lower
triangular and imply the same covariance; only the first has a positive
diagonal. -/
theorem sign_normalization_needed :
    let B₁ : Matrix (Fin 2) (Fin 2) ℝ := 1
    let B₂ : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![-1, 1]
    B₁ * B₁ᵀ = B₂ * B₂ᵀ ∧ B₁ ≠ B₂ ∧ B₁.IsLowerTriangular ∧ B₂.IsLowerTriangular ∧
      IsRecursive B₁ ∧ ¬ IsRecursive B₂ := by
  intro B₁ B₂
  refine ⟨?_, fun h => ?_, blockTriangular_one, blockTriangular_diagonal _,
    ⟨blockTriangular_one, fun i => by simp [B₁]⟩, fun h => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [B₁, B₂]
  · have := congrFun (congrFun h 0) 0; simp [B₁, B₂] at this; norm_num at this
  · have := h.2 0; simp [B₂] at this; norm_num at this

end Econ.TimeSeries.SVAR
