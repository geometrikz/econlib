/-
# Intermediary asset pricing: the equity constraint (He–Krishnamurthy)

He and Krishnamurthy (2013), "Intermediary Asset Pricing", AER, §I–III
(static mean–variance reduction); Brunnermeier–Eisenbach–Sannikov (2013), §3.

**Setting.** A risky asset in unit supply has excess return with mean `μ`
and variance `σ² > 0`. Households cannot hold it directly; they invest
through intermediaries by buying intermediary equity. Specialists (the
intermediaries' insiders) have wealth `w > 0`; households have wealth
`W ≥ 0`. Because of an agency friction, outside equity can be at most `m`
times inside equity (`m ≥ 0`), so the intermediary's capital is
`K = w + min(W, m w)` (`capital`): households put all their wealth in when
allowed. Pooled capital `K` is managed with mean–variance preferences with
risk aversion `γ > 0` relative to capital: holding `x` units gives
`x μ − γ σ² x²/(2K)` (`obj`).

**Results.**
* `isMax_iff`: the intermediary's optimal holding is `x = K μ/(γ σ²)`.
* `isEq_iff`: market clearing (`x = 1`) holds iff the risk premium is
  `μ = γ σ²/K` (`premium`).
* `premium_constrained`, `premium_unconstrained`: when the equity
  constraint binds (`m w < W`) the premium is `γ σ²/((1 + m) w)`; otherwise
  it is `γ σ²/(w + W)`.
* `premium_strictAnti`: the premium falls strictly with intermediary wealth.
* `constrained_elasticity`: in the constrained region the premium has
  elasticity `−1` in intermediary wealth (`μ(w) w = μ(w') w'`), while
  `unconstrained_redistribution`: in the unconstrained region only total
  wealth `w + W` matters — the distribution of wealth across sectors is
  irrelevant, whereas `constrained_redistribution_matters`: in the
  constrained region shifting wealth to intermediaries at fixed total wealth
  strictly lowers the premium. The intermediary sector's wealth is a state
  variable for risk premia exactly when the constraint binds.
* `sharpe_eq`: the Sharpe ratio is `γ σ/K`.
* `premium_strictAnti` holds household wealth fixed; in the unconstrained
  region it is a total-wealth effect.

**Deviations.** Static mean–variance reduction of the dynamic model:
preferences are mean–variance relative to capital (log utility in HK).
Households put all their wealth into intermediary equity when allowed and
hold the excess `W − m w` in a riskless asset when the constraint binds; HK's
minimum riskless share `λ` is set to `0` (with `λ > 0` the threshold and
unconstrained capital become `(1 − λ) W` and `w + (1 − λ) W`). Household
participation is assumed through `capital`, not derived, and `IsEq` imposes
only the intermediary's optimality and market clearing. `μ` is an expected
excess payoff per unit (no asset price is modelled), so "risk premium" is in
payoff units.
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.MinMax
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

namespace Econ
namespace HeKrishnamurthy

/-- Primitives. -/
structure Env where
  γ : ℝ
  σ : ℝ
  m : ℝ
  W : ℝ
  hγ : 0 < γ
  hσ : 0 < σ
  hm : 0 ≤ m
  hW : 0 ≤ W

namespace Env

variable (E : Env)

/-- Intermediary capital with inside wealth `w`. -/
def capital (w : ℝ) : ℝ := w + min E.W (E.m * w)

/-- Mean–variance objective of pooled capital `K` holding `x` units. -/
def obj (K μ x : ℝ) : ℝ := x * μ - E.γ * E.σ ^ 2 * x ^ 2 / (2 * K)

/-- The equilibrium risk premium. -/
def premium (w : ℝ) : ℝ := E.γ * E.σ ^ 2 / E.capital w

theorem capital_pos {w : ℝ} (hw : 0 < w) : 0 < E.capital w := by
  have : 0 ≤ min E.W (E.m * w) := le_min E.hW (mul_nonneg E.hm hw.le)
  simp only [capital]; linarith

/-- **Optimal holdings.** -/
theorem isMax_iff {K μ x : ℝ} (hK : 0 < K) :
    (∀ y, E.obj K μ y ≤ E.obj K μ x) ↔ x = K * μ / (E.γ * E.σ ^ 2) := by
  have ha : 0 < E.γ * E.σ ^ 2 := mul_pos E.hγ (pow_pos E.hσ 2)
  set a := E.γ * E.σ ^ 2
  set x' := K * μ / a
  -- `obj y = obj x' − a (y − x')²/(2K)`
  have key : ∀ y, E.obj K μ y = E.obj K μ x' - a * (y - x') ^ 2 / (2 * K) := by
    intro y
    have := E.hγ.ne'
    have := E.hσ.ne'
    simp only [obj, x', a]
    field_simp
    ring
  constructor
  · intro h
    have h1 := h x'
    rw [key x, key x'] at h1
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, sub_zero] at h1
    have h2 : a * (x - x') ^ 2 / (2 * K) ≤ 0 := by linarith
    have h3 : 0 ≤ a * (x - x') ^ 2 / (2 * K) := by positivity
    have h4 : a * (x - x') ^ 2 = 0 := by
      have : a * (x - x') ^ 2 / (2 * K) = 0 := le_antisymm h2 h3
      rwa [div_eq_zero_iff, or_iff_left (by positivity)] at this
    have := (mul_eq_zero.1 h4).resolve_left ha.ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · rintro rfl y
    rw [key y, key x']
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, sub_zero]
    have : 0 ≤ a * (y - x') ^ 2 / (2 * K) := by positivity
    linarith

/-- Market clearing: holding the whole unit supply is optimal. -/
def IsEq (w μ : ℝ) : Prop := ∀ y, E.obj (E.capital w) μ y ≤ E.obj (E.capital w) μ 1

/-- **The equilibrium risk premium** is `γ σ²/K`. -/
theorem isEq_iff {w μ : ℝ} (hw : 0 < w) : E.IsEq w μ ↔ μ = E.premium w := by
  have hK := E.capital_pos hw
  have ha : 0 < E.γ * E.σ ^ 2 := mul_pos E.hγ (pow_pos E.hσ 2)
  rw [IsEq, E.isMax_iff hK, premium, eq_div_iff ha.ne', eq_div_iff hK.ne']
  constructor <;> intro h <;> linarith

/-- In the constrained region the premium is `γ σ²/((1 + m) w)`. -/
theorem premium_constrained {w : ℝ} (hc : E.m * w < E.W) :
    E.premium w = E.γ * E.σ ^ 2 / ((1 + E.m) * w) := by
  simp only [premium, capital, min_eq_right hc.le]
  ring_nf

/-- In the unconstrained region the premium is `γ σ²/(w + W)`. -/
theorem premium_unconstrained {w : ℝ} (hc : E.W ≤ E.m * w) :
    E.premium w = E.γ * E.σ ^ 2 / (w + E.W) := by
  simp only [premium, capital, min_eq_left hc]

theorem capital_strictMono : StrictMonoOn E.capital (Set.Ioi 0) := by
  intro w₁ hw₁ w₂ hw₂ h
  simp only [capital]
  have : min E.W (E.m * w₁) ≤ min E.W (E.m * w₂) :=
    min_le_min le_rfl (mul_le_mul_of_nonneg_left h.le E.hm)
  linarith

/-- **Risk premia fall as intermediaries recapitalize.** -/
theorem premium_strictAnti : StrictAntiOn E.premium (Set.Ioi 0) := by
  intro w₁ hw₁ w₂ hw₂ h
  have h1 := E.capital_pos hw₁
  have hc := E.capital_strictMono hw₁ hw₂ h
  exact div_lt_div_of_pos_left (mul_pos E.hγ (pow_pos E.hσ 2)) h1 hc

/-- **Constrained region: unit elasticity.** If the constraint binds at both
wealth levels, `μ(w) w = μ(w') w'`. -/
theorem constrained_elasticity {w w' : ℝ} (hw : 0 < w) (hw' : 0 < w')
    (hc : E.m * w < E.W) (hc' : E.m * w' < E.W) :
    E.premium w * w = E.premium w' * w' := by
  rw [E.premium_constrained hc, E.premium_constrained hc']
  have h1 : 0 < 1 + E.m := by linarith [E.hm]
  field_simp

/-- **Unconstrained region: only total wealth matters.** -/
theorem unconstrained_redistribution (E' : Env) (hγ : E'.γ = E.γ) (hσ : E'.σ = E.σ)
    {w w' : ℝ} (hc : E.W ≤ E.m * w) (hc' : E'.W ≤ E'.m * w') (htot : w + E.W = w' + E'.W) :
    E.premium w = E'.premium w' := by
  rw [E.premium_unconstrained hc, E'.premium_unconstrained hc', hγ, hσ, htot]

/-- **Constrained region: the distribution of wealth matters.** Moving wealth
from households to intermediaries, holding total wealth fixed, strictly
lowers the risk premium when the constraint binds before and after. -/
theorem constrained_redistribution_matters (E' : Env) (hγ : E'.γ = E.γ) (hσ : E'.σ = E.σ)
    (hm : E'.m = E.m) {w w' : ℝ} (hw : 0 < w) (hww : w < w') (hc : E.m * w < E.W)
    (hc' : E'.m * w' < E'.W) (_htot : w + E.W = w' + E'.W) :
    E'.premium w' < E.premium w := by
  rw [E.premium_constrained hc, E'.premium_constrained hc', hγ, hσ, hm]
  have h1 : 0 < 1 + E.m := by linarith [E.hm]
  exact div_lt_div_of_pos_left (mul_pos E.hγ (pow_pos E.hσ 2)) (mul_pos h1 hw)
    (mul_lt_mul_of_pos_left hww h1)

/-- **The Sharpe ratio** `μ/σ = γ σ/K`. -/
theorem sharpe_eq {w : ℝ} (hw : 0 < w) : E.premium w / E.σ = E.γ * E.σ / E.capital w := by
  have := E.capital_pos hw
  have := E.hσ.ne'
  simp only [premium]
  field_simp

/-- **Non-vacuity**: an equilibrium exists for every positive wealth level,
and both regions occur (with `m = 1`, `W = 1`: constrained at `w = 1/2`,
unconstrained at `w = 2`). -/
theorem exists_eq {w : ℝ} (hw : 0 < w) : ∃ μ, E.IsEq w μ :=
  ⟨E.premium w, (E.isEq_iff hw).2 rfl⟩

theorem both_regions :
    ∃ E : Env, E.m * (1 / 2) < E.W ∧ E.W ≤ E.m * 2 :=
  ⟨⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

end Env
end HeKrishnamurthy
end Econ

end
