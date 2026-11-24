/-
# ARMA processes: stationarity and the MA(∞) representation

Hamilton, *Time Series Analysis* (1994), Prop. 1.1 and §3.4–3.7; Brockwell and
Davis, *Time Series: Theory and Methods* (1991), Thm 3.1.1; Lütkepohl (2005),
§2.1.1.

**The model.** An ARMA(p+1, q) process solves
`x_t = c + φ₀ x_{t−1} + ⋯ + φ_p x_{t−p−1} + w_t`, where `w_t = ε_t + Σ θ_k ε_{t−1−k}`
is the moving-average part. Stacking `s_t = (x_t, …, x_{t−p})` gives a VAR(1)
`s_t = c e₀ + C s_{t−1} + w_t e₀` with the companion matrix `C`.

**The results.**

* **Stability via the Gelfand radius**: in any normed ring,
  `Σ ‖aⁿ‖ < ∞ ⟺ lim ‖aⁿ‖^{1/n} < 1` (`summable_norm_pow_iff`), and for a complex
  Banach algebra this is "spectral radius `< 1`" (`spectralRadius_lt_one_iff`).
* **Companion eigenvalues** (Hamilton Prop. 1.1): `r` is an eigenvalue of `C` iff
  `r^{p+1} = Σⱼ φⱼ r^{p−j}` (`mem_spectrum_companion_iff`); equivalently, nonzero
  eigenvalues are the reciprocals of the roots of the lag polynomial
  `φ(z) = 1 − Σⱼ φⱼ z^{j+1}`.
* **Stationarity condition**: the VAR is stable iff every root of `φ(z)` lies
  outside the unit circle (`stable_iff_roots_outside`).
* **MA(∞) representation**: under that condition, for every bounded
  moving-average input, the first coordinate of the VAR's MA(∞) solution solves
  the ARMA recursion and is the only bounded solution (`arma_ma_solves`,
  `arma_unique`).

**Scope.** `IsARMA` is the AR(p+1) recursion with an intercept and a forcing term
`w`; the MA polynomial enters only through `w`, and the ψ-weights `θ(z)/φ(z)` are
not computed. The solution results are pathwise for bounded inputs, as in
`VAR.lean`: they cover bounded noise but not i.i.d. Gaussian noise, whose paths
are a.s. unbounded; the L² "unique stationary solution" of Brockwell–Davis
Thm 3.1.1 is not stated.

**Encoding.** Coefficients are `φ : Fin (p+1) → ℝ` (an AR order of at least 1;
`φ_p = 0` is allowed). The state space is `Fin (p+1) → ℝ` with the sup norm, and
matrices carry the induced `ℓ∞` operator norm.
-/
module

public import EconLean.Econometrics.TimeSeries.VAR
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

@[expose] public section

namespace Econ.TimeSeries.ARMA

open Matrix Filter Topology

/-! ## Stability and the Gelfand radius -/

section Gelfand

variable {R : Type*} [SeminormedRing R]

/-- **Summable powers iff Gelfand radius below one**: `Σ ‖aⁿ‖ < ∞` iff
`lim ‖aⁿ‖^{1/n} < 1`. -/
theorem summable_norm_pow_iff (a : R) :
    Summable (fun n : ℕ => ‖a ^ n‖) ↔ gelfandRadius a < 1 := by
  constructor
  · intro hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hs.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one))
    have h1 : ‖a ^ (N + 1)‖ < 1 := hN (N + 1) (Nat.le_succ N)
    calc gelfandRadius a ≤ ‖a ^ (N + 1)‖ ^ ((N + 1 : ℕ) : ℝ)⁻¹ :=
          gelfandRadius_le_norm_pow a (Nat.succ_ne_zero N)
      _ < 1 := Real.rpow_lt_one (norm_nonneg _) h1 (by positivity)
  · intro h
    set ρ := (gelfandRadius a + 1) / 2
    have hρ : gelfandRadius a < ρ := by simp only [ρ]; linarith
    have hρ0 : 0 ≤ ρ := (gelfandRadius_nonneg a).trans hρ.le
    have hρ1 : ρ < 1 := by simp only [ρ]; linarith
    obtain ⟨C, -, hC⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a hρ
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hC
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left C)

end Gelfand

/-- **Spectral radius below one** in a complex Banach algebra: the Gelfand radius
is below one iff every point of the spectrum has modulus below one. -/
theorem spectralRadius_lt_one_iff {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (a : A) :
    gelfandRadius a < 1 ↔ ∀ r ∈ spectrum ℂ a, ‖r‖ < 1 := by
  have hsr := spectrum.spectralRadius_eq_gelfandRadius a
  constructor
  · intro h r hr
    have h1 : (‖r‖₊ : ENNReal) ≤ spectralRadius ℂ a := by
      unfold spectralRadius
      exact le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ a) => (‖k‖₊ : ENNReal)) r
        (spectrum_subset_quasispectrum ℂ a hr)
    rw [hsr] at h1
    have h2 : ENNReal.ofReal (gelfandRadius a) < 1 := ENNReal.ofReal_lt_one.mpr h
    have h3 : (‖r‖₊ : ENNReal) < 1 := h1.trans_lt h2
    exact_mod_cast h3
  · intro h
    have h1 := spectrum.spectralRadius_lt_of_forall_lt_of_nonempty (r := 1)
      (spectrum.nonempty a) fun k hk => by exact_mod_cast h k hk
    rw [hsr] at h1
    exact ENNReal.ofReal_lt_one.mp (by exact_mod_cast h1)

/-! ## The companion matrix -/

variable {p : ℕ}

/-- The companion matrix of the AR coefficients `φ`: first row `φ`, ones on the
subdiagonal. -/
def companion {K : Type*} [Zero K] [One K] (φ : Fin (p + 1) → K) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) K :=
  Matrix.of fun i j => if (i : ℕ) = 0 then φ j else if (j : ℕ) + 1 = i then 1 else 0

/-- The characteristic equation `r^{p+1} − Σⱼ φⱼ r^{p−j}`. -/
def charEq {K : Type*} [CommRing K] (φ : Fin (p + 1) → K) (r : K) : K :=
  r ^ (p + 1) - ∑ j, φ j * r ^ (p - (j : ℕ))

/-- The AR lag polynomial `φ(z) = 1 − Σⱼ φⱼ z^{j+1}`. -/
def lagPoly {K : Type*} [CommRing K] (φ : Fin (p + 1) → K) (z : K) : K :=
  1 - ∑ j, φ j * z ^ ((j : ℕ) + 1)

section Companion

variable {K : Type*} [Field K]

lemma companion_mulVec_zero (φ : Fin (p + 1) → K) (v : Fin (p + 1) → K) :
    (companion φ *ᵥ v) 0 = ∑ j, φ j * v j := by
  simp [companion, mulVec, dotProduct]

lemma companion_mulVec_succ (φ : Fin (p + 1) → K) (v : Fin (p + 1) → K) (i : Fin p) :
    (companion φ *ᵥ v) i.succ = v i.castSucc := by
  simp only [companion, mulVec, dotProduct, of_apply, Fin.val_succ, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false]
  rw [Finset.sum_eq_single i.castSucc]
  · simp
  · intro j _ hj
    have : ¬ ((j : ℕ) = (i : ℕ)) := by
      intro h; apply hj; ext; simp only [Fin.val_castSucc]; omega
    simp [this]
  · simp

/-- An eigenvector of the companion matrix is determined by its last entry:
`vⱼ = r^{p−j} v_p`. -/
lemma eigvec_eq (φ : Fin (p + 1) → K) {r : K} {v : Fin (p + 1) → K}
    (hv : companion φ *ᵥ v = r • v) (j : Fin (p + 1)) :
    v j = r ^ (p - (j : ℕ)) * v (Fin.last p) := by
  induction j using Fin.reverseInduction with
  | last => simp
  | cast i ih =>
    have h := congrFun hv i.succ
    rw [companion_mulVec_succ, Pi.smul_apply, smul_eq_mul] at h
    rw [h, ih, ← mul_assoc, ← pow_succ']
    congr 2
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega

/-- **Companion eigenvalues** (Hamilton Prop. 1.1): `r` is an eigenvalue of the
companion matrix iff `r^{p+1} = Σⱼ φⱼ r^{p−j}`. -/
theorem exists_eigvec_iff (φ : Fin (p + 1) → K) (r : K) :
    (∃ v ≠ 0, companion φ *ᵥ v = r • v) ↔ charEq φ r = 0 := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hlast : v (Fin.last p) ≠ 0 := by
      intro h; apply hv0; funext j; rw [eigvec_eq φ hv j, h, mul_zero]; rfl
    have h0 := congrFun hv 0
    rw [companion_mulVec_zero, Pi.smul_apply, smul_eq_mul] at h0
    have hsum : ∑ j, φ j * v j = ∑ j, φ j * (r ^ (p - (j : ℕ)) * v (Fin.last p)) :=
      Finset.sum_congr rfl fun j _ => by rw [← eigvec_eq φ hv j]
    have h00 : v 0 = r ^ p * v (Fin.last p) := by simpa using eigvec_eq φ hv 0
    have : charEq φ r * v (Fin.last p) = 0 := by
      simp only [charEq, sub_mul, Finset.sum_mul]
      rw [sub_eq_zero, show r ^ (p + 1) * v (Fin.last p) = r * v 0 by rw [h00]; ring, ← h0,
        hsum]
      exact Finset.sum_congr rfl fun j _ => by ring
    exact (mul_eq_zero.mp this).resolve_right hlast
  · intro h
    refine ⟨fun j => r ^ (p - (j : ℕ)), fun h0 => ?_, ?_⟩
    · have := congrFun h0 (Fin.last p); simp at this
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      cases i using Fin.cases with
      | zero =>
        rw [companion_mulVec_zero]
        simp only [charEq, sub_eq_zero] at h
        simp only [Fin.val_zero, Nat.sub_zero]
        rw [← h, pow_succ']
      | succ i =>
        rw [companion_mulVec_succ, ← pow_succ']
        congr 1
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega

/-- The spectrum of the companion matrix is the zero set of the characteristic
equation. -/
theorem mem_spectrum_companion_iff (φ : Fin (p + 1) → K) (r : K) :
    r ∈ spectrum K (companion φ) ↔ charEq φ r = 0 := by
  rw [← exists_eigvec_iff, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not, ← exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  have hd : (algebraMap K (Matrix (Fin (p + 1)) (Fin (p + 1)) K) r) *ᵥ v = r • v := by
    ext i; simp [algebraMap_eq_diagonal, mulVec_diagonal]
  rw [sub_mulVec, hd, sub_eq_zero, eq_comm]

/-- `charEq φ r = r^{p+1} φ(1/r)` for `r ≠ 0`. -/
lemma charEq_eq_mul_lagPoly (φ : Fin (p + 1) → K) {r : K} (hr : r ≠ 0) :
    charEq φ r = r ^ (p + 1) * lagPoly φ r⁻¹ := by
  simp only [charEq, lagPoly, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ p := Nat.lt_succ_iff.mp j.2
  have hp : r ^ (p + 1) = r ^ (p - (j : ℕ)) * r ^ ((j : ℕ) + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hp, inv_pow]
  field_simp

lemma lagPoly_zero (φ : Fin (p + 1) → K) : lagPoly φ 0 = 1 := by
  simp [lagPoly]

end Companion

/-- **Eigenvalues inside the unit circle iff lag roots outside** (Hamilton
Prop. 1.1): every eigenvalue of the companion matrix has modulus below one iff
every root of `φ(z) = 1 − Σⱼ φⱼ z^{j+1}` has modulus above one. -/
theorem spectrum_lt_one_iff_roots (φ : Fin (p + 1) → ℂ) :
    (∀ r ∈ spectrum ℂ (companion φ), ‖r‖ < 1) ↔ ∀ z, lagPoly φ z = 0 → 1 < ‖z‖ := by
  simp only [mem_spectrum_companion_iff]
  constructor
  · intro h z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [lagPoly_zero] at hz; exact one_ne_zero hz
    have := h z⁻¹ (by rw [charEq_eq_mul_lagPoly φ (inv_ne_zero hz0), inv_inv, hz, mul_zero])
    rw [norm_inv] at this
    exact (inv_lt_one₀ (norm_pos_iff.mpr hz0)).mp this
  · intro h r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hl : lagPoly φ r⁻¹ = 0 := by
      rw [charEq_eq_mul_lagPoly φ hr0] at hr
      exact (mul_eq_zero.mp hr).resolve_left (pow_ne_zero _ hr0)
    have := h _ hl
    rw [norm_inv] at this
    exact (one_lt_inv₀ (norm_pos_iff.mpr hr0)).mp this

/-! ## Real AR coefficients: the stationarity condition -/

section Real

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The companion matrix as an operator on the state space `Fin (p+1) → ℝ`. -/
noncomputable def compCLM (φ : Fin (p + 1) → ℝ) : (Fin (p + 1) → ℝ) →L[ℝ] (Fin (p + 1) → ℝ) :=
  ⟨Matrix.mulVecLin (companion φ), LinearMap.continuous_of_finiteDimensional _⟩

lemma compCLM_apply (φ : Fin (p + 1) → ℝ) (v : Fin (p + 1) → ℝ) :
    compCLM φ v = companion φ *ᵥ v := rfl

lemma compCLM_pow_apply (φ : Fin (p + 1) → ℝ) (n : ℕ) (v : Fin (p + 1) → ℝ) :
    (compCLM φ ^ n) v = (companion φ ^ n) *ᵥ v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    show compCLM φ ((compCLM φ ^ n) v) = _
    rw [ih, compCLM_apply, mulVec_mulVec, ← pow_succ']

lemma norm_compCLM_pow (φ : Fin (p + 1) → ℝ) (n : ℕ) :
    ‖compCLM φ ^ n‖ = ‖companion φ ^ n‖ := by
  rw [linfty_opNorm_eq_opNorm]
  congr 1
  ext1 v
  rw [compCLM_pow_apply]
  rfl

lemma companion_map (φ : Fin (p + 1) → ℝ) :
    companion (fun j => (φ j : ℂ)) = (companion φ).map ((↑) : ℝ → ℂ) := by
  ext i j; simp only [companion, of_apply, map_apply]; split_ifs <;> simp

lemma norm_map_pow (φ : Fin (p + 1) → ℝ) (n : ℕ) :
    ‖(companion φ).map ((↑) : ℝ → ℂ) ^ n‖ = ‖companion φ ^ n‖ := by
  have : (companion φ).map ((↑) : ℝ → ℂ) ^ n = (companion φ ^ n).map (algebraMap ℝ ℂ) :=
    (Matrix.map_pow (companion φ) (algebraMap ℝ ℂ) n).symm
  rw [this, linfty_opNorm_def, linfty_opNorm_def]
  simp

/-- **The stationarity condition** (Hamilton Prop. 1.1; Brockwell–Davis Thm 3.1.1):
the companion VAR of an AR(p+1) with real coefficients is stable (`Σ ‖Cⁿ‖ < ∞`)
iff every complex root of the lag polynomial `φ(z) = 1 − Σⱼ φⱼ z^{j+1}` lies
strictly outside the unit circle. -/
theorem stable_iff_roots_outside (φ : Fin (p + 1) → ℝ) :
    VAR.Stable (compCLM φ) ↔ ∀ z : ℂ, lagPoly (fun j => (φ j : ℂ)) z = 0 → 1 < ‖z‖ := by
  rw [VAR.Stable, summable_norm_pow_iff, ← spectrum_lt_one_iff_roots,
    ← spectralRadius_lt_one_iff, companion_map,
    gelfandRadius_eq_of_norm_pow_eq fun n => (norm_compCLM_pow φ n).trans (norm_map_pow φ n).symm]

end Real

/-! ## ARMA paths and the MA(∞) representation -/

/-- `x` solves the ARMA recursion `x_t = c + Σⱼ φⱼ x_{t−1−j} + w_t`, where `w`
is the moving-average part (e.g. `w_t = ε_t + Σₖ θₖ ε_{t−1−k}`). -/
def IsARMA (c : ℝ) (φ : Fin (p + 1) → ℝ) (w : ℤ → ℝ) (x : ℤ → ℝ) : Prop :=
  ∀ t, x t = c + ∑ j : Fin (p + 1), φ j * x (t - 1 - j) + w t

/-- The stacked state `s_t = (x_t, x_{t−1}, …, x_{t−p})`. -/
def state (x : ℤ → ℝ) (t : ℤ) : Fin (p + 1) → ℝ := fun i => x (t - i)

/-- The first unit vector times `a`. -/
def e0 (a : ℝ) : Fin (p + 1) → ℝ := Pi.single 0 a

/-- **Companion form**: an ARMA path stacks into a path of the companion VAR. -/
theorem isPath_state {c : ℝ} {φ : Fin (p + 1) → ℝ} {w x : ℤ → ℝ} (h : IsARMA c φ w x) :
    VAR.IsPath (e0 c) (compCLM φ) (fun t => e0 (w t)) (state x) := by
  intro t
  funext i
  cases i using Fin.cases with
  | zero =>
    simp only [Pi.add_apply, compCLM_apply, companion_mulVec_zero, e0, Pi.single_eq_same,
      state, Fin.val_zero, Nat.cast_zero, sub_zero]
    rw [h t]
  | succ i =>
    simp only [Pi.add_apply, compCLM_apply, companion_mulVec_succ, e0,
      Pi.single_eq_of_ne (Fin.succ_ne_zero i), state, Fin.val_succ, Fin.val_castSucc]
    simp only [zero_add, add_zero]
    congr 1; push_cast; ring

/-- Conversely, a path of the companion VAR is the stacked state of its first
coordinate, which solves the ARMA recursion. -/
theorem path_first {c : ℝ} {φ : Fin (p + 1) → ℝ} {w : ℤ → ℝ} {y : ℤ → Fin (p + 1) → ℝ}
    (hy : VAR.IsPath (e0 c) (compCLM φ) (fun t => e0 (w t)) y) :
    y = state (fun t => y t 0) ∧ IsARMA c φ w (fun t => y t 0) := by
  have hcoord : ∀ i : Fin (p + 1), ∀ t, y t i = y (t - i) 0 := by
    intro i
    induction i using Fin.induction with
    | zero => intro t; simp
    | succ i ih =>
      intro t
      have := congrFun (hy t) i.succ
      simp only [Pi.add_apply, compCLM_apply, companion_mulVec_succ, e0,
        Pi.single_eq_of_ne (Fin.succ_ne_zero i), zero_add, add_zero] at this
      rw [this, ih]
      congr 1; simp only [Fin.val_succ, Fin.val_castSucc]; push_cast; ring
  refine ⟨funext fun t => funext fun i => hcoord i t, fun t => ?_⟩
  have := congrFun (hy t) 0
  simp only [Pi.add_apply, compCLM_apply, companion_mulVec_zero, e0, Pi.single_eq_same] at this
  show y t 0 = _
  rw [this]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoord j]

lemma norm_e0 (a : ℝ) : ‖(e0 a : Fin (p + 1) → ℝ)‖ = |a| := by
  simp [e0, Pi.norm_single, Real.norm_eq_abs]

lemma norm_state_le {x : ℤ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hx : ∀ t, |x t| ≤ K) (t : ℤ) :
    ‖(state x t : Fin (p + 1) → ℝ)‖ ≤ K :=
  (pi_norm_le_iff_of_nonneg hK).mpr fun i => by rw [Real.norm_eq_abs]; exact hx _

/-- **The MA(∞) solution** (Hamilton §3.4–3.7): under the stationarity condition
and for a bounded moving-average input `w`, the first coordinate of the companion
VAR's MA(∞) process solves the ARMA recursion and is bounded. -/
theorem arma_ma_solves {c : ℝ} {φ : Fin (p + 1) → ℝ} (hφ : VAR.Stable (compCLM φ))
    {w : ℤ → ℝ} {M : ℝ} (hw : ∀ t, |w t| ≤ M) :
    IsARMA c φ w (fun t => VAR.ma (e0 c) (compCLM φ) (fun s => e0 (w s)) t 0) ∧
      ∃ K, ∀ t, |VAR.ma (e0 c) (compCLM φ) (fun s => e0 (w s)) t 0| ≤ K := by
  have hu : ∀ t, ‖(e0 (w t) : Fin (p + 1) → ℝ)‖ ≤ M := fun t => by rw [norm_e0]; exact hw t
  refine ⟨(path_first (VAR.ma_isPath hφ (e0 c) hu)).2, ?_⟩
  obtain ⟨K, hK⟩ := VAR.ma_bounded hφ (e0 c) hu
  exact ⟨K, fun t => (norm_le_pi_norm _ 0).trans (hK t)⟩

/-- **Uniqueness of the stationary solution**: under the stationarity condition,
any two bounded solutions of the ARMA recursion with the same bounded input
coincide. -/
theorem arma_unique {c : ℝ} {φ : Fin (p + 1) → ℝ} (hφ : VAR.Stable (compCLM φ))
    {w x x' : ℤ → ℝ} (hx : IsARMA c φ w x) (hx' : IsARMA c φ w x') {K K' : ℝ}
    (hK : ∀ t, |x t| ≤ K) (hK' : ∀ t, |x' t| ≤ K') : x = x' := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hK0' : 0 ≤ K' := (abs_nonneg _).trans (hK' 0)
  have := VAR.isPath_unique hφ (isPath_state hx) (isPath_state hx')
    (norm_state_le hK0 hK) (norm_state_le hK0' hK')
  funext t
  simpa [state] using congrFun (congrFun this t) 0

/-- **Non-vacuity**: the AR(1) `x_t = x_{t−1}/2 + w_t` is stationary (its lag
root is `z = 2`), while the random walk `x_t = x_{t−1} + w_t` is not (unit root
`z = 1`). -/
theorem ar1_witness :
    VAR.Stable (compCLM (p := 0) fun _ => 1 / 2) ∧ ¬ VAR.Stable (compCLM (p := 0) fun _ => 1) := by
  constructor
  · rw [stable_iff_roots_outside]
    intro z hz
    have : z = 2 := by
      have : (1 : ℂ) - (1 / 2) * z = 0 := by simpa [lagPoly] using hz
      linear_combination -2 * this
    subst this; norm_num
  · rw [stable_iff_roots_outside]
    intro h
    have := h 1 (by simp [lagPoly])
    simp at this

end Econ.TimeSeries.ARMA
