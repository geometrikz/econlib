/-
# Long-run risk (Bansal–Yaron): the price of long-run consumption risk

Bansal and Yaron (2004), "Risks for the Long Run", JF, §I.A–B;
Bansal, Kiku and Yaron (2012); Campbell, *Financial Decisions and Markets*,
ch. 6.

**Setting.** Epstein–Zin preferences with risk aversion `γ` and IES `ψ`
(`ψ > 0`, `ψ ≠ 1`, `γ ≠ 1`), and `θ = (1 − γ)/(1 − 1/ψ)`. Log consumption
growth has a persistent predictable component:
`g_{t+1} = μ + x_t + σ ε_{t+1}`, `x_{t+1} = ρ x_t + φ_e σ e_{t+1}` with
`ρ ∈ [0, 1)`, `ε, e` independent standard shocks. The log return on wealth
is log-linearized, `r_{a,t+1} = κ₀ + κ₁ z_{t+1} − z_t + g_{t+1}`
(`κ₁ ∈ (0, 1)`), with conjectured log wealth–consumption ratio
`z_t = A₀ + A₁ x_t`. The log SDF is
`m_{t+1} = θ log δ − (θ/ψ) g_{t+1} + (θ − 1) r_{a,t+1}`.

**Results.**
* `logEuler`, `logEuler_affine`, `xCoeff_eq_zero_iff`, `euler_forces_A₁`: the coefficient on `x_t` in the
  (log-normal) Euler equation `E_t[m + r_a] + ½ Var_t = 0` vanishes iff
  `A₁ = (1 − 1/ψ)/(1 − κ₁ρ)`: the variance terms do not depend on `x_t`, so
  this pins down the loading.
* `A₁_pos_iff`: the wealth–consumption ratio rises with expected growth iff
  `ψ > 1` (substitution dominates income).
* `sdf_innov`: the SDF innovation is `−γ σ ε − λ_e σ e` with the **price of
  long-run risk** `λ_e = (γ − 1/ψ) κ₁ φ_e/(1 − κ₁ρ)` (`lamE`).
* `lamE_pos_iff`, `lamE_crra`, `lamE_strictMono_ρ`: long-run risk is priced
  positively iff `γ > 1/ψ` (preference for early resolution of
  uncertainty), not at all under CRRA (`γ = 1/ψ`), and more heavily the more
  persistent the predictable component.
* `byCalibration_lamE`: at the Bansal–Yaron calibration `17 < λ_e < 17.2`.
* `premium_eq`, `wealth_premium_gt`: an asset with shock loadings
  `(β_c, β_e)` earns `−Cov(m, r) = σ²(γ β_c + λ_e β_e)`; for the wealth
  portfolio with `γ > 1/ψ`, `ψ > 1`, `φ_e > 0` this exceeds the
  short-run CRRA-style premium `γ σ²`.

**Deviations.** `xCoeff` is the `x`-slope of the conditional mean
`logEuler`, which is computed by hand from the dynamics (`logEuler_affine`
checks the slope). Homoskedastic case (no stochastic volatility); the
log-linearization constant `κ₁` is a parameter rather than solved
endogenously; covariances are computed from loadings on orthonormal shocks
(the `−Cov` formula is a definition, `premium`); the constant terms of the
Euler equation (which determine `A₀` and the risk-free rate) are not treated.
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

namespace Econ
namespace LongRunRisk

/-- Parameters. -/
structure Params where
  γ : ℝ
  ψ : ℝ
  κ₁ : ℝ
  ρ : ℝ
  φe : ℝ
  σ : ℝ
  hγ : γ ≠ 1
  hψ : 0 < ψ
  hψ1 : ψ ≠ 1
  hκ : 0 < κ₁ ∧ κ₁ < 1
  hρ : 0 ≤ ρ ∧ ρ < 1
  hσ : 0 < σ

namespace Params

variable (P : Params)

/-- `θ = (1 − γ)/(1 − 1/ψ)`. -/
def θ : ℝ := (1 - P.γ) / (1 - 1 / P.ψ)

/-- The equilibrium loading of the wealth–consumption ratio on `x`. -/
def A₁ : ℝ := (1 - 1 / P.ψ) / (1 - P.κ₁ * P.ρ)

/-- The price of long-run risk. -/
def lamE : ℝ := (P.γ - 1 / P.ψ) * P.κ₁ * P.φe / (1 - P.κ₁ * P.ρ)

theorem one_sub_inv_ne : 1 - 1 / P.ψ ≠ 0 := by
  intro h
  have : 1 / P.ψ = 1 := by linarith
  rw [div_eq_one_iff_eq P.hψ.ne'] at this
  exact P.hψ1 this.symm

theorem one_sub_κρ_pos : 0 < 1 - P.κ₁ * P.ρ := by
  have : P.κ₁ * P.ρ < 1 := by nlinarith [P.hκ.1, P.hκ.2, P.hρ.1, P.hρ.2]
  linarith

theorem θ_ne : P.θ ≠ 0 := by
  simp only [θ]
  exact div_ne_zero (sub_ne_zero.2 (Ne.symm P.hγ)) P.one_sub_inv_ne

/-- Coefficient on `x_t` of `E_t[θ log δ − (θ/ψ) g + θ r_a]` for a
conjectured loading `a`. -/
def xCoeff (a : ℝ) : ℝ := -(P.θ / P.ψ) + P.θ * (P.κ₁ * a * P.ρ - a + 1)

/-- `E_t[θ log δ − (θ/ψ) g_{t+1} + θ r_{a,t+1}]` as a function of the state
`x_t = x`, computed from the dynamics: `E_t g_{t+1} = μ + x`,
`E_t z_{t+1} = A₀ + a ρ x`, `z_t = A₀ + a x`. -/
def logEuler (lδ μ κ₀ A₀ a x : ℝ) : ℝ :=
  P.θ * lδ - P.θ / P.ψ * (μ + x) +
    P.θ * (κ₀ + P.κ₁ * (A₀ + a * (P.ρ * x)) - (A₀ + a * x) + (μ + x))

/-- The conditional mean is affine in `x` with slope `xCoeff a`. -/
theorem logEuler_affine (lδ μ κ₀ A₀ a x : ℝ) :
    P.logEuler lδ μ κ₀ A₀ a x = P.logEuler lδ μ κ₀ A₀ a 0 + P.xCoeff a * x := by
  simp only [logEuler, xCoeff]; ring

/-- **Coefficient matching pins down `A₁`.** -/
theorem xCoeff_eq_zero_iff (a : ℝ) : P.xCoeff a = 0 ↔ a = P.A₁ := by
  have hθ := P.θ_ne
  have hd := P.one_sub_κρ_pos.ne'
  simp only [xCoeff, A₁]
  rw [eq_div_iff hd]
  constructor
  · intro h
    have : P.θ * ((1 - 1 / P.ψ) - a * (1 - P.κ₁ * P.ρ)) = 0 := by linear_combination h
    have := (mul_eq_zero.1 this).resolve_left hθ
    linarith
  · intro h
    linear_combination (-P.θ) * h

/-- **The Euler equation holds in every state only if `a = A₁`.** With
homoskedastic shocks the conditional variance term `V` does not depend on
`x`; if `E_t[m + r_a] + V = 0` for every `x`, the loading must be `A₁`. -/
theorem euler_forces_A₁ (lδ μ κ₀ A₀ a V : ℝ)
    (h : ∀ x, P.logEuler lδ μ κ₀ A₀ a x + V = 0) : a = P.A₁ := by
  have h0 := h 0
  have h1 := h 1
  rw [P.logEuler_affine lδ μ κ₀ A₀ a 1] at h1
  exact (P.xCoeff_eq_zero_iff a).1 (by linarith)

/-- **IES above one**: the wealth–consumption ratio rises with expected
growth iff `ψ > 1`. -/
theorem A₁_pos_iff : 0 < P.A₁ ↔ 1 < P.ψ := by
  simp only [A₁]
  rw [div_pos_iff_of_pos_right P.one_sub_κρ_pos, sub_pos, div_lt_one P.hψ]

/-- Innovation in the log return on wealth: `κ₁ A₁ φ_e σ e + σ ε`. -/
def raInnov (ε e : ℝ) : ℝ := P.κ₁ * P.A₁ * (P.φe * P.σ * e) + P.σ * ε

/-- Innovation in the log SDF. -/
def mInnov (ε e : ℝ) : ℝ := -(P.θ / P.ψ) * (P.σ * ε) + (P.θ - 1) * P.raInnov ε e

/-- **The SDF prices short- and long-run risk.** -/
theorem sdf_innov (ε e : ℝ) : P.mInnov ε e = -P.γ * P.σ * ε - P.lamE * P.σ * e := by
  have h1 := P.one_sub_inv_ne
  have h2 := P.one_sub_κρ_pos.ne'
  have hψ := P.hψ.ne'
  have h3 : P.ψ - 1 ≠ 0 := sub_ne_zero.2 P.hψ1
  have h4 : -1 + P.ψ ≠ 0 := by rw [neg_add_eq_sub]; exact h3
  simp only [mInnov, raInnov, θ, A₁, lamE]
  field_simp
  ring

/-- **Long-run risk is priced iff agents prefer early resolution.** -/
theorem lamE_pos_iff (hφ : 0 < P.φe) : 0 < P.lamE ↔ 1 / P.ψ < P.γ := by
  simp only [lamE]
  rw [div_pos_iff_of_pos_right P.one_sub_κρ_pos, mul_assoc,
    mul_pos_iff_of_pos_right (mul_pos P.hκ.1 hφ), sub_pos]

/-- Under CRRA (`γ = 1/ψ`) long-run risk is not priced. -/
theorem lamE_crra (h : P.γ = 1 / P.ψ) : P.lamE = 0 := by
  simp [lamE, h]

/-- **More persistence, a higher price of long-run risk** (holding the
log-linearization constant `κ₁` fixed; in Bansal–Yaron `κ₁` moves with `ρ`
through the mean wealth–consumption ratio). -/
theorem lamE_strictMono_ρ (P' : Params) (hγ : P'.γ = P.γ) (hψ : P'.ψ = P.ψ) (hκ : P'.κ₁ = P.κ₁)
    (hφe : P'.φe = P.φe) (hpos : 1 / P.ψ < P.γ) (hφ : 0 < P.φe) (hρ : P.ρ < P'.ρ) :
    P.lamE < P'.lamE := by
  have hd := P'.one_sub_κρ_pos
  simp only [lamE, hγ, hψ, hκ, hφe] at hd ⊢
  apply div_lt_div_of_pos_left
  · exact mul_pos (mul_pos (by linarith) P.hκ.1) hφ
  · exact hd
  · nlinarith [P.hκ.1]

/-- Risk premium `−Cov(m, r)` of an asset whose log return has loadings
`(β_c, β_e)` on the orthonormal shocks `(σ ε, σ e)`, given SDF loadings. -/
def premium (βc βe : ℝ) : ℝ :=
  -((P.mInnov 1 0 / P.σ) * βc + (P.mInnov 0 1 / P.σ) * βe) * P.σ ^ 2

theorem premium_eq (βc βe : ℝ) :
    P.premium βc βe = P.σ ^ 2 * (P.γ * βc + P.lamE * βe) := by
  have hσ := P.hσ.ne'
  simp only [premium, sdf_innov]
  field_simp
  ring

/-- **The wealth portfolio earns a long-run risk premium** on top of the
CRRA-style short-run premium `γ σ²`. (Sufficient conditions: the excess is
`(γ − 1/ψ)(1 − 1/ψ) κ₁² φ_e²/(1 − κ₁ρ)²`, also positive when `γ < 1/ψ`,
`ψ < 1`.) -/
theorem wealth_premium_gt (hφ : 0 < P.φe) (hpos : 1 / P.ψ < P.γ)
    (hψ1 : 1 < P.ψ) :
    P.γ * P.σ ^ 2 < P.premium 1 (P.κ₁ * P.A₁ * P.φe) := by
  have hσ := P.hσ.ne'
  rw [P.premium_eq]
  have h1 := (P.lamE_pos_iff hφ).2 hpos
  have h2 := (P.A₁_pos_iff).2 hψ1
  have h3 : 0 < P.lamE * (P.κ₁ * P.A₁ * P.φe) := mul_pos h1 (mul_pos (mul_pos P.hκ.1 h2) hφ)
  have h4 : 0 < P.σ ^ 2 := by positivity
  nlinarith

/-- The Bansal–Yaron (2004) calibration: `γ = 10`, `ψ = 1.5`,
`κ₁ = 0.997`, `ρ = 0.979`, `φ_e = 0.044`, `σ = 0.0078`. -/
def byCalibration : Params :=
  ⟨10, 3 / 2, 997 / 1000, 979 / 1000, 44 / 1000, 78 / 10000,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Non-vacuity and magnitude**: at the Bansal–Yaron calibration the price
of long-run risk is about 17.1 (versus `γ = 10` for short-run risk) and the
wealth–consumption ratio loads positively on expected growth. -/
theorem byCalibration_lamE :
    17 < byCalibration.lamE ∧ byCalibration.lamE < 172 / 10 ∧ 0 < byCalibration.A₁ := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [byCalibration, lamE, A₁]

end Params
end LongRunRisk
end Econ

end
