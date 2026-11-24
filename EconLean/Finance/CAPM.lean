/-
# The Capital Asset Pricing Model

Sharpe (1964), Lintner (1965); Cochrane, *Asset Pricing*, ch. 9 (CAPM as a
linear factor model); LeRoy–Werner, *Principles of Financial Economics*,
ch. 13.

**Setting.** Finitely many states `s` with probabilities `π_s > 0` summing to
one; `E`, `Cov`, `Var` are the corresponding moments. A stochastic discount
factor `m` prices every gross return: `E[m R] = 1`, and the gross riskless
rate satisfies `E[m] R_f = 1`. In the CAPM the SDF is affine in the market
return, `m = a − b R_m` (`IsLinearSDF`). This holds, for instance, when a
representative investor with quadratic utility `u'(c) = κ − c` invests
wealth `W` in the market, so `c = W R_m` and `m = β u'(c)/u'(c₀)`
(`linearSDF_of_quadratic`).

**Results.**
* `excess_return_eq`: with a linear SDF, `E R − R_f = R_f b Cov(R, R_m)`.
* `beta_pricing` (**CAPM**): if `Var R_m ≠ 0`, every return satisfies
  `E R_i − R_f = β_i (E R_m − R_f)` with `β_i = Cov(R_i, R_m)/Var(R_m)`.
* `market_premium_pos`: with `b > 0`, `R_f > 0` and a risky market
  (`Var R_m > 0`), the market risk premium is strictly positive.
* `hasDerivAt_quadU`, `quadSDF`, `linearSDF_of_quadratic`: with quadratic
  utility the SDF `β u'(W R_m)/u'(c₀)` is affine in `R_m` with `b > 0`.
* `capm_of_quadratic`: beta pricing and a positive market premium for the
  quadratic-utility economy.

`beta_pricing` is the general "linear SDF ⇒ beta model" result (Cochrane
§9): any return `R_m` in which the SDF is affine serves as the pricing
factor; the quadratic-utility economy makes it the market return.

**Deviations.** One period, finite states; mean–variance portfolio choice and
market clearing are summarized by the linear SDF (the equivalence with
mean–variance efficiency of the market portfolio is not formalized).
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

noncomputable section

namespace Econ
namespace CAPM

open Finset

/-- A full-support probability on a finite state space. -/
structure Prob (σ : Type*) [Fintype σ] where
  π : σ → ℝ
  pos : ∀ s, 0 < π s
  sum_one : ∑ s, π s = 1

namespace Prob

variable {σ : Type*} [Fintype σ] (P : Prob σ)

/-- Expectation. -/
def E (f : σ → ℝ) : ℝ := ∑ s, P.π s * f s

/-- Covariance. -/
def Cov (f g : σ → ℝ) : ℝ := P.E (fun s => f s * g s) - P.E f * P.E g

/-- Variance. -/
def Var (f : σ → ℝ) : ℝ := P.Cov f f

theorem E_const (a : ℝ) : P.E (fun _ => a) = a := by
  simp [E, ← Finset.sum_mul, P.sum_one]

theorem E_affine (a b : ℝ) (f : σ → ℝ) : P.E (fun s => a - b * f s) = a - b * P.E f := by
  simp only [E, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_one, one_mul,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

theorem E_affine_mul (a b : ℝ) (f g : σ → ℝ) :
    P.E (fun s => (a - b * f s) * g s) = a * P.E g - b * P.E (fun s => f s * g s) := by
  simp only [E, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The SDF is affine in the market return. -/
def IsLinearSDF (m Rm : σ → ℝ) (a b : ℝ) : Prop := ∀ s, m s = a - b * Rm s

/-- `m` prices the gross return `R`. -/
def Prices (m R : σ → ℝ) : Prop := P.E (fun s => m s * R s) = 1

/-- **Excess returns and covariance with the market.** -/
theorem excess_return_eq {m Rm R : σ → ℝ} {a b Rf : ℝ} (hm : IsLinearSDF m Rm a b)
    (hRf : P.E m * Rf = 1) (hR : P.Prices m R) :
    P.E R - Rf = Rf * b * P.Cov R Rm := by
  have hm' : m = fun s => a - b * Rm s := funext hm
  have hmE : P.E m = a - b * P.E Rm := by rw [hm', P.E_affine]
  have hmR : P.E (fun s => m s * R s) = a * P.E R - b * P.E (fun s => Rm s * R s) := by
    rw [hm']; exact P.E_affine_mul a b Rm R
  have hcomm : P.E (fun s => R s * Rm s) = P.E (fun s => Rm s * R s) := by
    simp only [E, mul_comm (R _)]
  unfold Prices at hR
  rw [hmR] at hR
  rw [hmE] at hRf
  unfold Cov
  rw [hcomm]
  linear_combination Rf * hR - P.E R * hRf

/-- **The CAPM beta-pricing equation.** -/
theorem beta_pricing {m Rm R : σ → ℝ} {a b Rf : ℝ} (hm : IsLinearSDF m Rm a b)
    (hRf : P.E m * Rf = 1) (hR : P.Prices m R) (hRm : P.Prices m Rm) (hvar : P.Var Rm ≠ 0) :
    P.E R - Rf = P.Cov R Rm / P.Var Rm * (P.E Rm - Rf) := by
  rw [P.excess_return_eq hm hRf hR, P.excess_return_eq hm hRf hRm]
  unfold Var at *
  field_simp

/-- **A positive market risk premium.** -/
theorem market_premium_pos {m Rm : σ → ℝ} {a b Rf : ℝ} (hm : IsLinearSDF m Rm a b)
    (hRf : P.E m * Rf = 1) (hRm : P.Prices m Rm) (hb : 0 < b) (hRf0 : 0 < Rf)
    (hvar : 0 < P.Var Rm) : Rf < P.E Rm := by
  have := P.excess_return_eq hm hRf hRm
  have : 0 < Rf * b * P.Cov Rm Rm := mul_pos (mul_pos hRf0 hb) hvar
  linarith

omit [Fintype σ] in
/-- Quadratic utility `u(c) = −(κ − c)²/2` has marginal utility `κ − c`. -/
theorem hasDerivAt_quadU (κ c : ℝ) :
    HasDerivAt (fun c => -(κ - c) ^ 2 / 2) (κ - c) c := by
  have := ((((hasDerivAt_id c).const_sub κ).fun_pow 2).neg).div_const 2
  convert this using 1
  · simp
  · simp

/-- The SDF of a quadratic-utility investor: `m = β u'(c₁)/u'(c₀)` with
`u'(c) = κ − c` and next-period consumption `c₁ = W R_m` (all wealth in the
market portfolio). -/
def quadSDF (β κ W c₀ : ℝ) (Rm : σ → ℝ) : σ → ℝ := fun s => β * (κ - W * Rm s) / (κ - c₀)

omit [Fintype σ] in
/-- **Quadratic utility gives a linear SDF**: `m = a − b R_m` with
`b = βW/u'(c₀) > 0` when `c₀ < κ` (positive marginal utility today). -/
theorem linearSDF_of_quadratic {Rm : σ → ℝ} {β κ W c₀ : ℝ} (hc₀ : c₀ < κ) (hβ : 0 < β)
    (hW : 0 < W) :
    IsLinearSDF (quadSDF β κ W c₀ Rm) Rm (β * κ / (κ - c₀)) (β * W / (κ - c₀)) ∧
      0 < β * W / (κ - c₀) := by
  have h : κ - c₀ ≠ 0 := by linarith
  exact ⟨fun s => by simp only [quadSDF]; field_simp, div_pos (mul_pos hβ hW) (by linarith)⟩

/-- **The CAPM for the quadratic-utility economy**: beta pricing, and a
strictly positive market risk premium when the market is risky. -/
theorem capm_of_quadratic {Rm R : σ → ℝ} {β κ W c₀ Rf : ℝ} (hc₀ : c₀ < κ) (hβ : 0 < β)
    (hW : 0 < W) (hRf0 : 0 < Rf) (hRf : P.E (quadSDF β κ W c₀ Rm) * Rf = 1)
    (hR : P.Prices (quadSDF β κ W c₀ Rm) R) (hRm : P.Prices (quadSDF β κ W c₀ Rm) Rm)
    (hvar : 0 < P.Var Rm) :
    P.E R - Rf = P.Cov R Rm / P.Var Rm * (P.E Rm - Rf) ∧ Rf < P.E Rm := by
  obtain ⟨hlin, hb⟩ := linearSDF_of_quadratic (Rm := Rm) hc₀ hβ hW
  exact ⟨P.beta_pricing hlin hRf hR hRm hvar.ne', P.market_premium_pos hlin hRf hRm hb hRf0 hvar⟩

end Prob
end CAPM
end Econ

end
