/-
# Autocovariances of autoregressions: the Yule–Walker equations

Yule (1927); Walker (1931); Hamilton, *Time Series Analysis* (1994), §3.4
(eq. 3.4.12, 3.4.29–3.4.30); Brockwell and Davis (1991), §8.1.

**The model.** A mean-zero AR(p+1) `x_t = Σⱼ φⱼ x_{t−1−j} + ε_t` whose second
moments are stationary, `E[x_t x_s] = γ(t − s)`, with innovations orthogonal to
the past, `E[ε_t x_s] = 0` for `s < t`, and `E[ε_t x_t] = σ²`.

**The results.**

* `γ` is even (`autocov_neg`).
* **Yule–Walker equations** (`yule_walker`): `γ(h) = Σⱼ φⱼ γ(h − 1 − j)` for
  `h ≥ 1`, and `γ(0) = Σⱼ φⱼ γ(1 + j) + σ²` (`yule_walker_zero`).
* **Identification**: if the Toeplitz matrix `Γᵢⱼ = γ(i − j)` is invertible, the
  coefficients are `φ = Γ⁻¹ (γ(1), …, γ(p+1))` (`yule_walker_identify`); this is
  the population version of the Yule–Walker estimator.
* **AR(1)**: `γ(h) = φʰ γ(0)` and `γ(0) = σ²/(1 − φ²)` (`ar1_autocov`); a
  nondegenerate innovation `σ² > 0` forces `|φ| < 1` (`ar1_stationary_bound`).

**Notation.** `IsAR (p := p)` has `p + 1` lags, so it is an AR(p+1) in
Hamilton's notation. `Autocov` and `Innovation` are uncentred second moments; they
are the autocovariances when the process has mean zero, and the identities hold
as stated either way.

**Scope.** Stationarity and orthogonality are hypotheses on the second moments
(as in Hamilton's derivation); the construction of a stationary solution from
white noise is not formalised here (see `ARMA.lean` for the bounded pathwise
solution).
-/
module

public import EconLean.Econometrics.TimeSeries.ARMA
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace Econ.TimeSeries.YuleWalker

open MeasureTheory Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℕ}

/-- The AR(p+1) recursion `x_t = Σⱼ φⱼ x_{t−1−j} + ε_t`, pathwise. -/
def IsAR (φ : Fin (p + 1) → ℝ) (x ε : ℤ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = ∑ j : Fin (p + 1), φ j * x (t - 1 - j) ω + ε t ω

/-- Second-moment stationarity: `E[x_t x_s] = γ(t − s)`. -/
def Autocov (μ : Measure Ω) (x : ℤ → Ω → ℝ) (γ : ℤ → ℝ) : Prop :=
  ∀ t s, ∫ ω, x t ω * x s ω ∂μ = γ (t - s)

/-- Innovations orthogonal to the past, with variance `σ²` against the present. -/
def Innovation (μ : Measure Ω) (x ε : ℤ → Ω → ℝ) (σ2 : ℝ) : Prop :=
  (∀ t s, s < t → ∫ ω, ε t ω * x s ω ∂μ = 0) ∧ ∀ t, ∫ ω, ε t ω * x t ω ∂μ = σ2

/-- The autocovariance function is even. -/
lemma autocov_neg {x : ℤ → Ω → ℝ} {γ : ℤ → ℝ} (hγ : Autocov μ x γ) (h : ℤ) : γ (-h) = γ h := by
  have h1 := hγ 0 h
  have h2 := hγ h 0
  simp only [zero_sub, sub_zero] at h1 h2
  rw [← h1, ← h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

/-- Expanding `E[x_t x_s]` through the recursion. -/
lemma integral_ar_mul {φ : Fin (p + 1) → ℝ} {x ε : ℤ → Ω → ℝ} (hx : IsAR φ x ε)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) (t s : ℤ) :
    ∫ ω, x t ω * x s ω ∂μ
      = ∑ j : Fin (p + 1), φ j * ∫ ω, x (t - 1 - j) ω * x s ω ∂μ + ∫ ω, ε t ω * x s ω ∂μ := by
  have : (fun ω => x t ω * x s ω)
      = fun ω => ∑ j : Fin (p + 1), φ j * (x (t - 1 - j) ω * x s ω) + ε t ω * x s ω := by
    funext ω; rw [hx t ω, add_mul, Finset.sum_mul]
    congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, integral_add (integrable_finsetSum _ fun j _ => (hxx _ _).const_mul _) (hεx t s),
    integral_finsetSum _ fun j _ => (hxx _ _).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- **Yule–Walker equations** (Hamilton eq. 3.4.30): `γ(h) = Σⱼ φⱼ γ(h − 1 − j)`
for every lag `h ≥ 1`. -/
theorem yule_walker {φ : Fin (p + 1) → ℝ} {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hx : IsAR φ x ε) (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) {h : ℤ} (hh : 1 ≤ h) :
    γ h = ∑ j : Fin (p + 1), φ j * γ (h - 1 - j) := by
  have e := integral_ar_mul hx hxx hεx h 0
  rw [hε.1 h 0 (by omega), add_zero, hγ, sub_zero] at e
  rw [e]
  exact Finset.sum_congr rfl fun j _ => by rw [hγ, sub_zero]

/-- **Yule–Walker at lag zero** (Hamilton eq. 3.4.29): `γ(0) = Σⱼ φⱼ γ(1 + j) + σ²`. -/
theorem yule_walker_zero {φ : Fin (p + 1) → ℝ} {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hx : IsAR φ x ε) (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) :
    γ 0 = ∑ j : Fin (p + 1), φ j * γ (1 + j) + σ2 := by
  have e := integral_ar_mul hx hxx hεx 0 0
  rw [hε.2 0, hγ, sub_zero] at e
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hγ, sub_zero, show (0 : ℤ) - 1 - j = -(1 + j) by ring, autocov_neg hγ]

/-- The Toeplitz autocovariance matrix `Γᵢⱼ = γ(i − j)`. -/
def toeplitz (γ : ℤ → ℝ) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of fun i j => γ ((i : ℤ) - j)

/-- **Identification by the Yule–Walker system**: `Γ φ = (γ(1), …, γ(p+1))`, so if
`Γ` is invertible the AR coefficients are `Γ⁻¹ (γ(1), …, γ(p+1))`. -/
theorem yule_walker_identify {φ : Fin (p + 1) → ℝ} {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hx : IsAR φ x ε) (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) :
    toeplitz γ *ᵥ φ = (fun i : Fin (p + 1) => γ ((i : ℤ) + 1)) ∧
      (IsUnit (toeplitz (p := p) γ).det →
        φ = (toeplitz γ)⁻¹ *ᵥ fun i : Fin (p + 1) => γ ((i : ℤ) + 1)) := by
  have hsys : toeplitz γ *ᵥ φ = (fun i : Fin (p + 1) => γ ((i : ℤ) + 1)) := by
    funext i
    rw [yule_walker hx hγ hε hxx hεx (h := (i : ℤ) + 1) (by omega)]
    simp only [toeplitz, mulVec, dotProduct, of_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; congr 2; ring
  refine ⟨hsys, fun hu => ?_⟩
  rw [← hsys, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- **AR(1) autocovariances** (Hamilton eq. 3.4.5–3.4.6): `γ(h) = φʰ γ(0)` for
`h ≥ 0` and `(1 − φ²) γ(0) = σ²`, so `γ(0) = σ²/(1 − φ²)` when `φ² ≠ 1`. -/
theorem ar1_autocov {φ : ℝ} {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hx : IsAR (p := 0) (fun _ => φ) x ε) (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) :
    (∀ h : ℕ, γ h = φ ^ h * γ 0) ∧ (1 - φ ^ 2) * γ 0 = σ2 ∧
      (φ ^ 2 ≠ 1 → γ 0 = σ2 / (1 - φ ^ 2)) := by
  have hstep : ∀ h : ℕ, γ ((h : ℤ) + 1) = φ * γ h := by
    intro h
    have := yule_walker hx hγ hε hxx hεx (h := (h : ℤ) + 1) (by omega)
    simpa using this
  have hpow : ∀ h : ℕ, γ h = φ ^ h * γ 0 := by
    intro h
    induction h with
    | zero => simp
    | succ h ih => push_cast; rw [hstep, ih, pow_succ]; ring
  have h0 := yule_walker_zero hx hγ hε hxx hεx
  have h0' : γ 0 = φ * γ 1 + σ2 := by simpa using h0
  have h1 : γ 1 = φ * γ 0 := by simpa using hpow 1
  have hvar : (1 - φ ^ 2) * γ 0 = σ2 := by rw [h1] at h0'; linarith [h0']
  refine ⟨hpow, hvar, fun hφ => ?_⟩
  rw [← hvar]
  field_simp [sub_ne_zero.mpr (Ne.symm hφ)]

/-- **Stationarity forces `|φ| < 1`** (Hamilton §3.4): an AR(1) with stationary
second moments and nondegenerate innovation variance `σ² > 0` has `|φ| < 1`, since
`(1 − φ²) γ(0) = σ²` with `γ(0) = E[x_t²] ≥ 0`. -/
theorem ar1_stationary_bound {φ : ℝ} {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hx : IsAR (p := 0) (fun _ => φ) x ε) (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) (hσ : 0 < σ2) : |φ| < 1 := by
  have hvar := (ar1_autocov hx hγ hε hxx hεx).2.1
  have h0 : 0 ≤ γ 0 := by
    rw [← sub_self (0 : ℤ), ← hγ 0 0]
    exact integral_nonneg fun ω => mul_self_nonneg _
  have h1 : 0 < 1 - φ ^ 2 := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  rw [abs_lt]; constructor <;> nlinarith [sq_nonneg (φ + 1), sq_nonneg (φ - 1)]

end Econ.TimeSeries.YuleWalker
