/-
# Structural VARs: long-run and sign restrictions

Blanchard and Quah, "The dynamic effects of aggregate demand and supply
disturbances", *AER* (1989); Faust (1998); Uhlig, "What are the effects of
monetary policy on output?", *JME* (2005); Rubio-Ramírez, Waggoner and Zha,
*REStud* (2010); Kilian and Lütkepohl, *Structural Vector Autoregressive
Analysis* (2017), §10.1 and ch. 13.

**The economics.** As in `SVAR`, the data reveal `Σ_u = B Bᵀ` and nothing more
about the impact matrix `B`.

* **Long-run restrictions** (Blanchard–Quah). In a stable VAR(p)
  `y_t = A₁ y_{t−1} + ⋯ + A_p y_{t−p} + B ε_t`, the cumulative (long-run)
  response of `y` to `ε` is `Ψ B` with `Ψ = (I − A₁ − ⋯ − A_p)⁻¹`. Blanchard and
  Quah identify `B` by requiring `Ψ B` to be lower triangular with a positive
  diagonal (e.g. demand shocks have no long-run effect on output). For every
  positive-definite `Σ_u` and invertible `I − ΣAᵢ` there is exactly one such `B`
  (`longRun_existsUnique`): the long-run impact matrix is the Cholesky factor of
  the long-run covariance `Ψ Σ_u Ψᵀ`.
* **Sign restrictions** (Faust, Uhlig, RWZ). The impact matrices consistent
  with `Σ_u` are exactly `B₀ Q` for one factor `B₀` and all orthogonal `Q`
  (`obsEquiv_iff_orthogonal`). Sign restrictions keep those satisfying sign
  constraints on responses (`identifiedSet_eq`). They **set-identify**: in a
  bivariate example the identified set contains distinct matrices
  (`sign_restrictions_set_identify`), so the restricted responses are not
  point-identified.

**Encoding.** `longRunMultiplier A = (I − Σᵢ Aᵢ)⁻¹`; the identity with the sum of
the moving-average coefficients is in `VAR.lean` (for VAR(1): `Σ_j A^j = (I − A)⁻¹`).
Sign constraints are a set of triples `(i, j, s)` meaning `s · B i j ≥ 0`.

**Scope.** Sign restrictions are on impact responses only; Uhlig (2005) also
restricts responses at horizons `1, …, K` (responses `Φ_h B`), which shrinks the
identified set further. From RWZ (2010) only the rotation characterisation is
used; their rank condition for exact identification under zero restrictions
and the Haar-measure drawing algorithm are not formalised.
-/
module

public import EconLean.Econometrics.TimeSeries.SVAR

@[expose] public section

namespace Econ.TimeSeries.SVAR

open Matrix

variable {n : Type*} [Fintype n] [LinearOrder n]

/-! ### Long-run restrictions -/

/-- The long-run multiplier `(I − A₁ − ⋯ − A_p)⁻¹` of a VAR(p). -/
noncomputable def longRunMultiplier {p : ℕ} (A : Fin p → Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - ∑ i, A i)⁻¹

/-- Long-run (Blanchard–Quah) identification restriction: the long-run impact
matrix `Ψ B` is lower triangular with a positive diagonal. -/
def IsLongRunRecursive (Ψ B : Matrix n n ℝ) : Prop :=
  IsRecursive (Ψ * B)

lemma posDef_congr {S Ψ : Matrix n n ℝ} (hS : S.PosDef) (hΨ : IsUnit Ψ.det) :
    (Ψ * S * Ψᵀ).PosDef := by
  have hinj : Function.Injective (Ψᵀ *ᵥ ·) := by
    have : IsUnit Ψᵀ.det := by rwa [det_transpose]
    exact mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr this)
  simpa [conjTranspose_eq_transpose_of_trivial] using hS.conjTranspose_mul_mul_same hinj

/-- **Uniqueness under long-run restrictions**: if `Ψ` is invertible, two impact
matrices satisfying the long-run restriction and implying the same `Σ_u` are
equal. -/
theorem longRun_unique {Ψ B₁ B₂ : Matrix n n ℝ} (hΨ : IsUnit Ψ.det)
    (h₁ : IsLongRunRecursive Ψ B₁) (h₂ : IsLongRunRecursive Ψ B₂)
    (h : B₁ * B₁ᵀ = B₂ * B₂ᵀ) : B₁ = B₂ := by
  have hL : (Ψ * B₁) * (Ψ * B₁)ᵀ = (Ψ * B₂) * (Ψ * B₂)ᵀ := by
    simp only [transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B₁, h, Matrix.mul_assoc]
  have := recursive_unique h₁ h₂ hL
  have hinv : Ψ⁻¹ * (Ψ * B₁) = Ψ⁻¹ * (Ψ * B₂) := by rw [this]
  rwa [nonsing_inv_mul_cancel_left _ _ hΨ, nonsing_inv_mul_cancel_left _ _ hΨ] at hinv

section LongRun

variable [LocallyFiniteOrderBot n]

/-- **Blanchard–Quah identification** (existence and uniqueness): for a
positive-definite `Σ_u` and an invertible long-run multiplier `Ψ`, exactly one
impact matrix `B` has `B Bᵀ = Σ_u` and lower-triangular long-run impact `Ψ B`
with positive diagonal. It is `B = Ψ⁻¹ C` with `C` the Cholesky factor of
`Ψ Σ_u Ψᵀ`. -/
theorem longRun_existsUnique {S Ψ : Matrix n n ℝ} (hS : S.PosDef) (hΨ : IsUnit Ψ.det) :
    ∃! B, IsLongRunRecursive Ψ B ∧ B * Bᵀ = S := by
  obtain ⟨C, hC, hCC⟩ := recursive_exists (n := n) (posDef_congr hS hΨ)
  have hΨt : IsUnit Ψᵀ.det := by rwa [det_transpose]
  refine ⟨Ψ⁻¹ * C, ⟨?_, ?_⟩, fun B' ⟨hB', hB'S⟩ => longRun_unique hΨ hB' ?_ ?_⟩
  · rw [IsLongRunRecursive, mul_nonsing_inv_cancel_left _ _ hΨ]; exact hC
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc C, hCC, transpose_nonsing_inv,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hΨ,
      Matrix.mul_assoc, mul_nonsing_inv _ hΨt, Matrix.mul_one]
  · rw [IsLongRunRecursive, mul_nonsing_inv_cancel_left _ _ hΨ]; exact hC
  · rw [hB'S, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc C, hCC, transpose_nonsing_inv,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hΨ,
      Matrix.mul_assoc, mul_nonsing_inv _ hΨt, Matrix.mul_one]

/-- **Blanchard–Quah for a VAR(p)**: with `Ψ = (I − A₁ − ⋯ − A_p)⁻¹` and
`I − ΣAᵢ` invertible (no unit root), the long-run restriction identifies `B`. -/
theorem blanchardQuah {p : ℕ} (A : Fin p → Matrix n n ℝ) (hA : IsUnit (1 - ∑ i, A i).det)
    {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∃! B, IsLongRunRecursive (longRunMultiplier A) B ∧ B * Bᵀ = S := by
  refine longRun_existsUnique hS ?_
  rw [longRunMultiplier]
  exact isUnit_nonsing_inv_det_iff.mpr hA

end LongRun

/-! ### Sign restrictions -/

/-- **Observational equivalence = orthogonal rotation** (Uhlig 2005; RWZ 2010):
for an invertible factor `B₀`, `B Bᵀ = B₀ B₀ᵀ` iff `B = B₀ Q` for some
orthogonal `Q`. -/
theorem obsEquiv_iff_orthogonal {B₀ B : Matrix n n ℝ} (hB₀ : IsUnit B₀.det) :
    B * Bᵀ = B₀ * B₀ᵀ ↔ ∃ Q : Matrix n n ℝ, Q * Qᵀ = 1 ∧ B = B₀ * Q := by
  have hB₀t : IsUnit B₀ᵀ.det := by rwa [det_transpose]
  constructor
  · intro h
    refine ⟨B₀⁻¹ * B, ?_, by rw [mul_nonsing_inv_cancel_left _ _ hB₀]⟩
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B, h, transpose_nonsing_inv,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hB₀, Matrix.one_mul,
      mul_nonsing_inv _ hB₀t]
  · rintro ⟨Q, hQ, rfl⟩
    exact observationallyEquivalent B₀ Q hQ

/-- Sign restrictions: each triple `(i, j, s)` requires `s · B i j ≥ 0` (the
impact response of variable `i` to shock `j` has the sign of `s`). -/
def SignOK (R : Set (n × n × ℝ)) (B : Matrix n n ℝ) : Prop :=
  ∀ r ∈ R, 0 ≤ r.2.2 * B r.1 r.2.1

/-- The identified set: impact matrices consistent with `Σ_u` and the sign
restrictions. -/
def identifiedSet (S : Matrix n n ℝ) (R : Set (n × n × ℝ)) : Set (Matrix n n ℝ) :=
  {B | B * Bᵀ = S ∧ SignOK R B}

/-- **The identified set under sign restrictions** is the set of rotations
`B₀ Q` (`Q` orthogonal) of any invertible factor `B₀` of `Σ_u` that satisfy the
sign restrictions (the RWZ algorithm draws `Q` from the Haar measure and keeps
those; the algorithm itself is not formalised). -/
theorem identifiedSet_eq {S B₀ : Matrix n n ℝ} (hB₀ : IsUnit B₀.det) (hS : B₀ * B₀ᵀ = S)
    (R : Set (n × n × ℝ)) :
    identifiedSet S R = {B | ∃ Q : Matrix n n ℝ, Q * Qᵀ = 1 ∧ B = B₀ * Q ∧ SignOK R B} := by
  ext B
  simp only [identifiedSet, Set.mem_ofPred_eq]
  rw [← hS]
  constructor
  · rintro ⟨h, hR⟩
    obtain ⟨Q, hQ, rfl⟩ := (obsEquiv_iff_orthogonal hB₀).mp h
    exact ⟨Q, hQ, rfl, hR⟩
  · rintro ⟨Q, hQ, rfl, hR⟩
    exact ⟨(obsEquiv_iff_orthogonal hB₀).mpr ⟨Q, hQ, rfl⟩, hR⟩

/-- **Sign restrictions set-identify** (Uhlig 2005; Fry and Pagan 2011): with
`Σ_u = I` and the restriction that shock 1 raises both variables on impact,
both `I` and the rotation by 45° lie in the identified set, so the impact
responses are not point-identified. -/
theorem sign_restrictions_set_identify :
    let R : Set (Fin 2 × Fin 2 × ℝ) := {(0, 0, 1), (1, 0, 1)}
    let c : ℝ := Real.sqrt 2 / 2
    let B₂ : Matrix (Fin 2) (Fin 2) ℝ := !![c, -c; c, c]
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ identifiedSet 1 R ∧ B₂ ∈ identifiedSet 1 R ∧
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ B₂ := by
  intro R c B₂
  have hc : c * c = 1 / 2 := by
    simp only [c]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hc0 : 0 ≤ c := by positivity
  refine ⟨⟨by simp, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₂, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  · intro r hr
    simp only [R, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simpa [B₂] using hc0
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [B₂] at this
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    simp only [c] at this
    linarith

end Econ.TimeSeries.SVAR
