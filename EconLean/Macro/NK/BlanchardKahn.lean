/-
# Blanchard–Kahn determinacy for `n` jump variables

Blanchard–Kahn (1980), Prop. 1; Galí ch. 3 appendix; Woodford, *Interest and
Prices*, App. C.

**Setup.** A linear perfect-foresight system `z_{t+1} = M z_t` with
`z_t ∈ ℝⁿ` and **no predetermined variables** (every coordinate is a jump
variable). The system is **determinate** if its only bounded solution is
`z = 0` (`DeterminateN`). An eigenvalue of the real matrix `M` is a complex
`μ` with `M v = μ v` for some nonzero `v ∈ ℂⁿ` (`IsEigenvalue`).

**Result.** `determinateN_iff`: the system is determinate iff **every eigenvalue
of `M` lies strictly outside the unit circle**. This is the Blanchard–Kahn
counting condition when all `n` variables jump: the number of unstable roots
must equal the number of jump variables. (`ThreeEquation.lean` has the `2 × 2`
case in Schur–Cohn form.)

**The Lean.** (⇒) An eigenvalue `|μ| ≤ 1` with eigenvector `v` gives the
bounded, nonzero real solution `z_t = Re(μᵗ w)`, with `w = v` or `w = i v`.
(⇐) If all eigenvalues are outside the unit circle, `M` is invertible and every
point of the spectrum of `N = M⁻¹` has modulus `< 1`. By **Gelfand's formula**
(`spectrum.spectralRadius_eq_gelfandRadius`, `tendsto_gelfandRadius`),
`‖Nᵗ‖ ≤ rᵗ` eventually for some `r < 1`, and `z_0 = Nᵗ z_t` forces `z_0 = 0`.

**Deviations.** Perfect foresight; the case with predetermined variables (where
determinacy needs as many unstable roots as jump variables *and* a rank
condition) is not formalized.
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

namespace Econ
namespace NK

open Matrix Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `z` solves `z_{t+1} = M z_t`. -/
def IsOrbitN (M : Matrix n n ℝ) (z : ℕ → n → ℝ) : Prop := ∀ t, z (t + 1) = M *ᵥ z t

/-- `z` is bounded. -/
def BoundedN (z : ℕ → n → ℝ) : Prop := ∃ B, ∀ t i, |z t i| ≤ B

/-- **Determinacy:** the only bounded solution is zero. -/
def DeterminateN (M : Matrix n n ℝ) : Prop :=
  ∀ z, IsOrbitN M z → BoundedN z → ∀ t, z t = 0

/-- The complexification of a real matrix. -/
def cplx (M : Matrix n n ℝ) : Matrix n n ℂ := M.map (fun x => (x : ℂ))

/-- `μ ∈ ℂ` is an eigenvalue of the real matrix `M`. -/
def IsEigenvalue (M : Matrix n n ℝ) (μ : ℂ) : Prop :=
  ∃ v : n → ℂ, v ≠ 0 ∧ cplx M *ᵥ v = μ • v

omit [DecidableEq n] in
theorem cplx_mulVec (M : Matrix n n ℝ) (v : n → ℝ) :
    cplx M *ᵥ (fun i => (v i : ℂ)) = fun i => ((M *ᵥ v) i : ℂ) := by
  funext i
  exact ((Complex.ofRealHom.map_mulVec M v i)).symm

omit [DecidableEq n] in
/-- **An eigenvalue on or inside the unit circle gives a bounded nonzero solution.** -/
theorem not_determinate_of_eigenvalue {M : Matrix n n ℝ} {μ : ℂ} (hμ : IsEigenvalue M μ)
    (h1 : ‖μ‖ ≤ 1) : ¬ DeterminateN M := by
  obtain ⟨v, hv, hMv⟩ := hμ
  -- choose `w ∈ {v, i v}` with nonzero real part
  obtain ⟨w, hw, hMw⟩ : ∃ w : n → ℂ, (fun i => (w i).re) ≠ 0 ∧ cplx M *ᵥ w = μ • w := by
    by_cases hre : (fun i => (v i).re) = 0
    · refine ⟨Complex.I • v, fun h => hv (funext fun i => ?_), by
        rw [mulVec_smul, hMv, smul_comm]⟩
      have a := congrFun hre i; have b := congrFun h i
      simp at a b
      exact Complex.ext (by simpa using a) (by simpa using b)
    · exact ⟨v, hre, hMv⟩
  intro hdet
  set z : ℕ → n → ℝ := fun t i => (μ ^ t * w i).re
  have hz : IsOrbitN M z := fun t => by
    funext i
    have : ((M *ᵥ z t) i : ℂ) = (cplx M *ᵥ fun j => ((z t j : ℝ) : ℂ)) i := by
      rw [cplx_mulVec]
    -- `M` is real, so it commutes with taking real parts
    have e : (M *ᵥ z t) i = ((cplx M *ᵥ fun j => μ ^ t * w j) i).re := by
      simp only [z, mulVec, dotProduct, cplx, map_apply, Complex.re_sum, Complex.re_ofReal_mul]
    rw [e, show (fun j => μ ^ t * w j) = μ ^ t • w from rfl, mulVec_smul, hMw]
    simp [z, pow_succ]
    ring
  have hb : BoundedN z := ⟨∑ j, ‖w j‖, fun t i => by
    calc |z t i| ≤ ‖μ ^ t * w i‖ := Complex.abs_re_le_norm _
      _ = ‖μ‖ ^ t * ‖w i‖ := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖w i‖ := by gcongr; exact pow_le_one₀ (norm_nonneg _) h1
      _ = ‖w i‖ := one_mul _
      _ ≤ ∑ j, ‖w j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (w j)) (Finset.mem_univ i)⟩
  apply hw
  have := hdet z hz hb 0
  funext i
  simpa [z] using congrFun this i

open scoped Matrix.Norms.Operator

/-- If every eigenvalue lies outside the unit circle, `M` is invertible over `ℂ`. -/
theorem isUnit_cplx {M : Matrix n n ℝ} (h : ∀ μ, IsEigenvalue M μ → 1 < ‖μ‖) :
    IsUnit (cplx M) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_eq_zero_iff.2 h0
  have := h 0 ⟨v, hv, by rw [hMv, zero_smul]⟩
  rw [norm_zero] at this
  exact absurd this (by norm_num)

/-- If every eigenvalue lies outside the unit circle, every spectral value of
`M⁻¹` lies inside it. -/
theorem norm_lt_of_mem_spectrum {M : Matrix n n ℝ} (h : ∀ μ, IsEigenvalue M μ → 1 < ‖μ‖)
    {ν : ℂ} (hν : ν ∈ spectrum ℂ (cplx M)⁻¹) : ‖ν‖ < 1 := by
  have hu := isUnit_cplx h
  have hdet : IsUnit (cplx M).det := (isUnit_iff_isUnit_det _).1 hu
  have hN : IsUnit (cplx M)⁻¹ := isUnit_nonsing_inv_iff.2 hu
  have hν0 : ν ≠ 0 := by
    rintro rfl; exact (spectrum.zero_notMem_iff ℂ).2 hN hν
  rw [spectrum.mem_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hν
  obtain ⟨v, hv, hNv⟩ := exists_mulVec_eq_zero_iff.2 hν
  -- `N v = ν v`, so `M v = ν⁻¹ v`
  have h1 : (cplx M)⁻¹ *ᵥ v = ν • v := by
    rw [sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, sub_eq_zero] at hNv
    exact hNv.symm
  have h2 : cplx M *ᵥ v = ν⁻¹ • v := by
    have : cplx M *ᵥ ((cplx M)⁻¹ *ᵥ v) = v := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    rw [h1, mulVec_smul] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hν0, one_smul, this]
  have := h _ ⟨v, hv, h2⟩
  rw [norm_inv] at this
  have hpos : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  rwa [one_lt_inv₀ hpos] at this

/-- **Blanchard–Kahn with `n` jump variables.** The only bounded solution of
`z_{t+1} = M z_t` is zero iff every (complex) eigenvalue of `M` lies strictly
outside the unit circle. -/
theorem determinateN_iff (M : Matrix n n ℝ) :
    DeterminateN M ↔ ∀ μ, IsEigenvalue M μ → 1 < ‖μ‖ := by
  constructor
  · intro hdet μ hμ
    by_contra h1; push Not at h1
    exact not_determinate_of_eigenvalue hμ h1 hdet
  · intro h z hz ⟨B, hB⟩
    rcases isEmpty_or_nonempty n with hn | hn
    · exact fun t => funext fun i => hn.elim i
    set N := (cplx M)⁻¹
    have hdet : IsUnit (cplx M).det := (isUnit_iff_isUnit_det _).1 (isUnit_cplx h)
    -- spectral radius of `N` is `< 1`
    have hne : (spectrum ℂ N).Nonempty := spectrum.nonempty N
    obtain ⟨k, hk, hkr⟩ := spectrum.exists_nnNorm_eq_spectralRadius_of_nonempty hne
    have hk1 : ‖k‖ < 1 := norm_lt_of_mem_spectrum h hk
    have hg : gelfandRadius N < 1 := by
      have h1 : spectralRadius ℂ N < 1 := by
        rw [← hkr]; exact_mod_cast (show ‖k‖₊ < 1 from hk1)
      rw [spectrum.spectralRadius_eq_gelfandRadius] at h1
      exact (ENNReal.ofReal_lt_one).1 h1
    set r := (gelfandRadius N + 1) / 2
    have hr1 : r < 1 := by simp only [r]; linarith
    have hr0 : 0 < r := by simp only [r]; linarith [gelfandRadius_nonneg N]
    have hev : ∀ᶠ k : ℕ in atTop, ‖N ^ k‖ ≤ r ^ k := by
      have := (tendsto_gelfandRadius N).eventually (gt_mem_nhds (show gelfandRadius N < r by
        simp only [r]; linarith))
      filter_upwards [this, eventually_ge_atTop 1] with k hk hk1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have := Real.rpow_le_rpow (by positivity) hk.le hk0.le
      rwa [← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hk0.ne', Real.rpow_one,
        Real.rpow_natCast] at this
    -- complexified orbit
    set zc : ℕ → n → ℂ := fun t i => (z t i : ℂ)
    have hzc : ∀ t, zc t = cplx M ^ t *ᵥ zc 0 := fun t => by
      induction t with
      | zero => simp
      | succ t ih =>
        have : zc (t + 1) = cplx M *ᵥ zc t := by
          simp only [zc, hz t]; exact (cplx_mulVec M (z t)).symm
        rw [this, ih, mulVec_mulVec, pow_succ']
    have h0 : ∀ t, zc 0 = N ^ t *ᵥ zc t := fun t => by
      have hp : ∀ t : ℕ, N ^ t * cplx M ^ t = 1 := fun t => by
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc N, nonsing_inv_mul _ hdet, one_mul, ih]
      rw [hzc t, mulVec_mulVec, hp, one_mulVec]
    have hzb : ∀ t, ‖zc t‖ ≤ max B 0 := fun t => by
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => ?_
      simp only [zc, Complex.norm_real, Real.norm_eq_abs]
      exact (hB t i).trans (le_max_left _ _)
    have hlim : Tendsto (fun t : ℕ => r ^ t * max B 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).mul_const (max B 0)
    have hle : ∀ᶠ t : ℕ in atTop, ‖zc 0‖ ≤ r ^ t * max B 0 := by
      filter_upwards [hev] with t ht
      rw [h0 t]
      exact (linfty_opNorm_mulVec _ _).trans
        (mul_le_mul ht (hzb t) (norm_nonneg _) (pow_nonneg hr0.le _))
    have hz0 : zc 0 = 0 := norm_le_zero_iff.1 (ge_of_tendsto hlim hle)
    have hz0' : z 0 = 0 := funext fun i => by
      have := congrFun hz0 i; simpa [zc] using this
    intro t
    induction t with
    | zero => exact hz0'
    | succ t ih => rw [hz t, ih, mulVec_zero]

/-- **Non-vacuity.** `M = I/2` (eigenvalue `1/2`) is not determinate: `z_t = 2⁻ᵗ`
is a bounded nonzero solution. -/
example : ¬ DeterminateN (Matrix.diagonal fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  intro h
  have := h (fun t _ => (1 / 2 : ℝ) ^ t) (fun t => by
    funext i; rw [mulVec_diagonal]; show (1 / 2 : ℝ) ^ (t + 1) = 1 / 2 * (1 / 2) ^ t; ring)
    ⟨1, fun t _ => by rw [abs_of_pos (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)⟩ 0
  simpa using congrFun this 0

end NK
end Econ

end
