/-
# Rare disasters and the equity premium

Rietz (1988), "The Equity Risk Premium: A Solution", JME; Barro (2006),
"Rare Disasters and Asset Markets in the Twentieth Century", QJE;
Barro–Ursúa (2008).

**Setting (one period, two states).** Consumption grows by `G₁ = g > 0` in
normal times (probability `1 − p`) and by `G₂ = (1 − b) g` in a disaster
(probability `p ∈ (0, 1)`, size `b ∈ (0, 1)`). The SDF is CRRA:
`m = β G^{−γ}` with `γ > 0`. Equity is a claim to consumption: its price is
`E[m G]` and its gross return `R_e = G/E[m G]`; the riskless rate is
`R_f = 1/E[m]`.

**Results.**
* `premium_ratio_eq`: `E[R_e]/R_f = E[G] E[G^{−γ}]/E[G^{1−γ}]`.
* `cov_two_point`: for a two-point distribution,
  `E[XY] − E[X]E[Y] = p(1 − p)(X₁ − X₂)(Y₁ − Y₂)`.
* `premium_pos`: with disasters (`0 < p < 1`, `0 < b < 1`) and `γ > 0`,
  `E[R_e] > R_f`: the equity premium is strictly positive; without disasters
  (`p = 0`) it is zero (`premium_zero`).
* `riskfree_anti_p`: holding `b, g, γ, β` fixed, a higher disaster
  probability strictly raises `E[G^{−γ}]` (`E_mu_strictMono_p`) and so
  strictly **lowers** the riskless rate (precautionary demand for the safe
  asset).

**Strip versus tree.** `equityPrice` prices a one-period consumption strip.
With i.i.d. growth the Lucas tree (a perpetual claim to consumption) has a
constant price–dividend ratio `β E[G^{1−γ}]/(1 − β E[G^{1−γ}])` when
`β E[G^{1−γ}] < 1`, and its expected gross return is again
`E[G]/(β E[G^{1−γ}])`, so `ERe` and `premium_ratio_eq` also describe the
tree (not formalized here).

**Deviations.** One period with a two-point growth distribution and
unlevered equity; Barro's lognormal normal-times shocks, leverage and the
empirical size distribution of disasters are not modelled. `premium_zero`
(no disasters means a deterministic economy) is a sanity check.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

namespace Econ
namespace Disasters

open Real

/-- Parameters. -/
structure Params where
  p : ℝ
  b : ℝ
  g : ℝ
  γ : ℝ
  β : ℝ
  hp : 0 ≤ p ∧ p < 1
  hb : 0 < b ∧ b < 1
  hg : 0 < g
  hγ : 0 < γ
  hβ : 0 < β

namespace Params

variable (P : Params)

/-- Growth in the normal and the disaster state. -/
def G₁ : ℝ := P.g
def G₂ : ℝ := (1 - P.b) * P.g

/-- Expectation of `f(G)`. -/
def E (f : ℝ → ℝ) : ℝ := (1 - P.p) * f P.G₁ + P.p * f P.G₂

theorem G₂_pos : 0 < P.G₂ := mul_pos (by linarith [P.hb.2]) P.hg
theorem G₂_lt : P.G₂ < P.G₁ := by
  simp only [G₁, G₂]; nlinarith [P.hb.1, P.hg]

/-- The equity price `E[m G]`. -/
def equityPrice : ℝ := P.E (fun G => P.β * G ^ (-P.γ) * G)

/-- The riskless rate `1/E[m]`. -/
def Rf : ℝ := 1 / P.E (fun G => P.β * G ^ (-P.γ))

/-- Expected equity return `E[G]/E[m G]`. -/
def ERe : ℝ := P.E id / P.equityPrice

theorem rpow_mul_self {G : ℝ} (hG : 0 < G) : G ^ (-P.γ) * G = G ^ (1 - P.γ) := by
  rw [show 1 - P.γ = -P.γ + 1 by ring, rpow_add hG, rpow_one]

theorem E_pos {f : ℝ → ℝ} (h1 : 0 < f P.G₁) (h2 : 0 < f P.G₂) : 0 < P.E f := by
  unfold E
  rcases P.hp.1.eq_or_lt with h | h
  · rw [← h]; simp; exact h1
  · have := P.hp.2; nlinarith

/-- **The premium ratio.** -/
theorem premium_ratio_eq :
    P.ERe / P.Rf = P.E id * P.E (fun G => G ^ (-P.γ)) / P.E (fun G => G ^ (1 - P.γ)) := by
  have h1 := P.hg; have h2 := P.G₂_pos
  have hEm : 0 < P.E (fun G => G ^ (-P.γ)) := P.E_pos (rpow_pos_of_pos h1 _) (rpow_pos_of_pos h2 _)
  have hEmG : 0 < P.E (fun G => G ^ (1 - P.γ)) :=
    P.E_pos (rpow_pos_of_pos h1 _) (rpow_pos_of_pos h2 _)
  have hp1 : P.equityPrice = P.β * P.E (fun G => G ^ (1 - P.γ)) := by
    simp only [equityPrice, E, mul_assoc, P.rpow_mul_self h1, P.rpow_mul_self h2, G₁] at *
    ring
  have hp2 : P.E (fun G => P.β * G ^ (-P.γ)) = P.β * P.E (fun G => G ^ (-P.γ)) := by
    simp only [E]; ring
  rw [ERe, Rf, hp1, hp2]
  have := P.hβ
  field_simp

/-- Two-point covariance. -/
theorem cov_two_point (X Y : ℝ → ℝ) :
    P.E (fun G => X G * Y G) - P.E X * P.E Y =
      P.p * (1 - P.p) * (X P.G₁ - X P.G₂) * (Y P.G₁ - Y P.G₂) := by
  simp only [E]; ring

/-- **A positive equity premium with disasters.** -/
theorem premium_pos (hp : 0 < P.p) : P.Rf < P.ERe := by
  have h1 : 0 < P.G₁ := P.hg; have h2 := P.G₂_pos
  have hEm : 0 < P.E (fun G => G ^ (-P.γ)) := P.E_pos (rpow_pos_of_pos h1 _) (rpow_pos_of_pos h2 _)
  have hEmG : 0 < P.E (fun G => G ^ (1 - P.γ)) :=
    P.E_pos (rpow_pos_of_pos h1 _) (rpow_pos_of_pos h2 _)
  have hRf : 0 < P.Rf := by
    rw [Rf]; apply div_pos one_pos
    exact P.E_pos (mul_pos P.hβ (rpow_pos_of_pos h1 _)) (mul_pos P.hβ (rpow_pos_of_pos h2 _))
  -- the ratio exceeds one
  have hcov := P.cov_two_point id (fun G => G ^ (-P.γ))
  have hX : P.G₂ < P.G₁ := P.G₂_lt
  have hY : P.G₁ ^ (-P.γ) < P.G₂ ^ (-P.γ) := rpow_lt_rpow_of_neg h2 hX (by linarith [P.hγ])
  have hneg : P.p * (1 - P.p) * (id P.G₁ - id P.G₂) * (P.G₁ ^ (-P.γ) - P.G₂ ^ (-P.γ)) < 0 := by
    have : 0 < P.p * (1 - P.p) * (id P.G₁ - id P.G₂) :=
      mul_pos (mul_pos hp (by linarith [P.hp.2])) (by simp only [id]; linarith)
    exact mul_neg_of_pos_of_neg this (by linarith)
  have hEmGeq : P.E (fun G => id G * G ^ (-P.γ)) = P.E (fun G => G ^ (1 - P.γ)) := by
    simp only [E, id, mul_comm _ (_ ^ (-P.γ)), P.rpow_mul_self h1, P.rpow_mul_self h2]
  have hratio : 1 < P.ERe / P.Rf := by
    rw [P.premium_ratio_eq, one_lt_div hEmG]
    linarith
  rwa [one_lt_div hRf] at hratio

/-- **No disasters, no premium.** -/
theorem premium_zero (hp : P.p = 0) : P.ERe = P.Rf := by
  have h1 : 0 < P.G₁ := P.hg
  have hRf : 0 < P.Rf := by
    rw [Rf]; apply div_pos one_pos
    simp only [E, hp]; simp; exact mul_pos P.hβ (rpow_pos_of_pos h1 _)
  have := P.premium_ratio_eq
  simp only [E, hp, sub_zero, one_mul, zero_mul, add_zero, id] at this
  rw [show P.G₁ ^ (1 - P.γ) = P.G₁ * P.G₁ ^ (-P.γ) by
    rw [mul_comm, P.rpow_mul_self h1]] at this
  rw [div_self (mul_pos (show 0 < P.G₁ from h1) (rpow_pos_of_pos h1 _)).ne',
    div_eq_one_iff_eq hRf.ne'] at this
  exact this

/-- A higher disaster probability raises expected marginal utility `E[G^{−γ}]`. -/
theorem E_mu_strictMono_p (P' : Params) (hb : P'.b = P.b) (hg : P'.g = P.g) (hγ : P'.γ = P.γ)
    (hpp : P.p < P'.p) :
    P.E (fun G => G ^ (-P.γ)) < P'.E (fun G => G ^ (-P'.γ)) := by
  have h2 := P.G₂_pos
  have hY : P.G₁ ^ (-P.γ) < P.G₂ ^ (-P.γ) :=
    rpow_lt_rpow_of_neg h2 P.G₂_lt (by linarith [P.hγ])
  simp only [E, G₁, G₂, hb, hg, hγ] at hY ⊢
  nlinarith

/-- **Disasters lower the riskless rate**: with the same `b`, `g`, `γ`, `β`,
a higher disaster probability strictly lowers `R_f`. -/
theorem riskfree_anti_p (P' : Params) (hb : P'.b = P.b) (hg : P'.g = P.g) (hγ : P'.γ = P.γ)
    (hβ : P'.β = P.β) (hpp : P.p < P'.p) : P'.Rf < P.Rf := by
  have hlt := P.E_mu_strictMono_p P' hb hg hγ hpp
  have hEm : 0 < P.E (fun G => G ^ (-P.γ)) :=
    P.E_pos (rpow_pos_of_pos P.hg _) (rpow_pos_of_pos P.G₂_pos _)
  have hsc : ∀ Q : Params, Q.E (fun G => Q.β * G ^ (-Q.γ)) = Q.β * Q.E (fun G => G ^ (-Q.γ)) :=
    fun Q => by simp only [E]; ring
  rw [Rf, Rf, hsc, hsc, hβ]
  exact one_div_lt_one_div_of_lt (mul_pos P.hβ hEm) (mul_lt_mul_of_pos_left hlt P.hβ)

end Params
end Disasters
end Econ

end
