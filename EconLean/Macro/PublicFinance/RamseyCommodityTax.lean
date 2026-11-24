/-
# Optimal commodity taxation: the Ramsey rule and the inverse elasticity rule

Ramsey (1927), "A Contribution to the Theory of Taxation", EJ; Diamond and
Mirrlees (1971); Atkinson–Stiglitz, *Lectures on Public Economics*, Lecture
12; Salanié, *The Economics of Taxation*, ch. 3.

**Setting.** Goods `i` are produced at constant producer prices `p_i`; the
government sets per-unit taxes `t_i`, so consumer prices are
`q_i = p_i + t_i`. Utility is quasilinear and additively separable, so
demand for good `i` depends only on its own price, `x_i(q_i)`, and consumer
welfare is the sum of consumer surpluses `CS_i(q_i)` with
`CS_i'(q) = −x_i(q)` (Hotelling/Roy). Revenue is `Σ t_i x_i(q_i)`. The
**Ramsey problem**: maximize `Σ CS_i(p_i + t_i)` subject to raising a given
revenue.

**Results.**
* `ramsey_rule`: at any (local) solution, with strictly differentiable
  surplus and demands and nonzero demands, there is a common constant `θ`
  with `t_k x_k'(q_k) = θ x_k(q_k)` for every good: taxes reduce every
  good's demand by the **same proportion** (to first order). Derived from the
  Lagrange multiplier theorem (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`).
* `inverse_elasticity`: equivalently, with own-price elasticity
  `ε_k = −q_k x_k'/x_k`, the ad valorem tax rates satisfy
  `t_k/q_k = c/ε_k` for a common `c`: **tax rates are inversely
  proportional to demand elasticities**.
* `inverse_elasticity_pos`: if the revenue requirement is positive (and
  prices, demands and elasticities are positive), then `c > 0` and a good
  with a more elastic demand is taxed at a strictly lower rate.

**Scope.** With independent demands the Ramsey rule (equal proportional
reduction of compensated demands, Atkinson–Stiglitz Lecture 12) reduces to
the inverse elasticity rule; `ramsey_rule` is this separable case, not the
general rule with cross-price effects.

**Deviations.** Independent demands (quasilinear, additively separable
utility), which is what makes the inverse elasticity form exact; constant
producer prices; first-order conditions only.
-/
module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

noncomputable section

namespace Econ
namespace RamseyTax

open Finset

variable {ι : Type*} [Fintype ι]

/-- Consumer welfare `Σ CS_i(p_i + t_i)`. -/
def welfare (CS : ι → ℝ → ℝ) (p : ι → ℝ) (t : ι → ℝ) : ℝ := ∑ i, CS i (p i + t i)

/-- Tax revenue `Σ t_i x_i(p_i + t_i)`. -/
def revenue (x : ι → ℝ → ℝ) (p : ι → ℝ) (t : ι → ℝ) : ℝ := ∑ i, t i * x i (p i + t i)

theorem hasStrictFDerivAt_coord {g : ℝ → ℝ} {g' a : ℝ} {t₀ : ι → ℝ} (i : ι)
    (hg : HasStrictDerivAt g g' (a + t₀ i)) :
    HasStrictFDerivAt (fun t : ι → ℝ => g (a + t i))
      (g' • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) t₀ := by
  have hin : HasStrictFDerivAt (fun t : ι → ℝ => a + t i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) t₀ :=
    (hasStrictFDerivAt_apply i t₀).const_add a
  have := hg.comp_hasStrictFDerivAt t₀ hin
  simpa [Function.comp_def] using this

variable [DecidableEq ι]

/-- **The Ramsey rule.** -/
theorem ramsey_rule [Nonempty ι] {CS x : ι → ℝ → ℝ} {x' p t₀ : ι → ℝ}
    (hCS : ∀ i, HasStrictDerivAt (CS i) (-x i (p i + t₀ i)) (p i + t₀ i))
    (hx : ∀ i, HasStrictDerivAt (x i) (x' i) (p i + t₀ i))
    (hx0 : ∀ i, x i (p i + t₀ i) ≠ 0)
    (hmax : IsLocalMaxOn (welfare CS p) {t | revenue x p t = revenue x p t₀} t₀) :
    ∃ θ : ℝ, ∀ k, t₀ k * x' k = θ * x k (p k + t₀ k) := by
  have hW : HasStrictFDerivAt (welfare CS p)
      (∑ i, (-x i (p i + t₀ i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) t₀ := by
    have := HasStrictFDerivAt.fun_sum (u := univ) (fun i _ => hasStrictFDerivAt_coord i (hCS i))
    exact this
  have hR : HasStrictFDerivAt (revenue x p)
      (∑ i, (t₀ i • (x' i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) +
        x i (p i + t₀ i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)) t₀ := by
    have := HasStrictFDerivAt.fun_sum (u := univ) (fun i _ =>
      (hasStrictFDerivAt_apply (𝕜 := ℝ) i t₀).mul (hasStrictFDerivAt_coord i (hx i)))
    exact this
  obtain ⟨a, b, hab, heq⟩ := IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inr hmax) hR hW
  have hk : ∀ k, a * (t₀ k * x' k + x k (p k + t₀ k)) + b * (-x k (p k + t₀ k)) = 0 := by
    intro k
    have := congrArg (fun L => L (Pi.single k 1)) heq
    simpa [sum_apply, Pi.single_apply, sum_add_distrib, mul_add] using this
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨k⟩ := ‹Nonempty ι›
    have := hk k
    simp only [zero_mul, zero_add, mul_neg, neg_eq_zero] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hab (by simp [h])
    · exact hx0 k h
  refine ⟨(b - a) / a, fun k => ?_⟩
  have := hk k
  field_simp
  linarith

/-- Own-price elasticity of demand `ε = −q x'/x`. -/
def elasticity (q xq x'q : ℝ) : ℝ := -(q * x'q / xq)

/-- **The inverse elasticity rule.** At a solution of the Ramsey problem the
ad valorem rates are `t_k/q_k = c/ε_k` for a common `c`; when `c > 0`
(positive taxes), more elastic goods are taxed at strictly lower rates. -/
theorem inverse_elasticity [Nonempty ι] {CS x : ι → ℝ → ℝ} {x' p t₀ : ι → ℝ}
    (hCS : ∀ i, HasStrictDerivAt (CS i) (-x i (p i + t₀ i)) (p i + t₀ i))
    (hx : ∀ i, HasStrictDerivAt (x i) (x' i) (p i + t₀ i))
    (hx0 : ∀ i, x i (p i + t₀ i) ≠ 0) (hq : ∀ i, p i + t₀ i ≠ 0) (hx'0 : ∀ i, x' i ≠ 0)
    (hmax : IsLocalMaxOn (welfare CS p) {t | revenue x p t = revenue x p t₀} t₀) :
    ∃ c : ℝ, (∀ k, t₀ k / (p k + t₀ k) =
        c / elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k)) ∧
      (0 < c → ∀ k l, 0 < elasticity (p l + t₀ l) (x l (p l + t₀ l)) (x' l) →
        elasticity (p l + t₀ l) (x l (p l + t₀ l)) (x' l) <
          elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k) →
        t₀ k / (p k + t₀ k) < t₀ l / (p l + t₀ l)) := by
  obtain ⟨θ, hθ⟩ := ramsey_rule hCS hx hx0 hmax
  have hform : ∀ k, t₀ k / (p k + t₀ k) =
      -θ / elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k) := by
    intro k
    have h1 := hx0 k; have h2 := hq k; have h3 := hx'0 k
    have := hθ k
    have e : -θ / elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k) =
        θ * x k (p k + t₀ k) / ((p k + t₀ k) * x' k) := by
      simp only [elasticity]; field_simp
    rw [e, div_eq_div_iff h2 (mul_ne_zero h2 h3)]
    linear_combination (p k + t₀ k) * this
  refine ⟨-θ, hform, fun hc k l hl hlk => ?_⟩
  rw [hform k, hform l]
  exact div_lt_div_of_pos_left hc hl hlk

/-- **The inverse elasticity rule with positive taxes.** If the required
revenue is positive, prices, demands and elasticities are positive, then the
common constant is positive, `t_k/q_k = c/ε_k` with `c > 0`, and goods with
more elastic demand are taxed at strictly lower ad valorem rates. -/
theorem inverse_elasticity_pos [Nonempty ι] {CS x : ι → ℝ → ℝ} {x' p t₀ : ι → ℝ}
    (hCS : ∀ i, HasStrictDerivAt (CS i) (-x i (p i + t₀ i)) (p i + t₀ i))
    (hx : ∀ i, HasStrictDerivAt (x i) (x' i) (p i + t₀ i))
    (hq : ∀ i, 0 < p i + t₀ i) (hxpos : ∀ i, 0 < x i (p i + t₀ i))
    (hε : ∀ i, 0 < elasticity (p i + t₀ i) (x i (p i + t₀ i)) (x' i))
    (hrev : 0 < revenue x p t₀)
    (hmax : IsLocalMaxOn (welfare CS p) {t | revenue x p t = revenue x p t₀} t₀) :
    ∃ c : ℝ, 0 < c ∧ (∀ k, t₀ k / (p k + t₀ k) =
        c / elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k)) ∧
      (∀ k l, elasticity (p l + t₀ l) (x l (p l + t₀ l)) (x' l) <
          elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k) →
        t₀ k / (p k + t₀ k) < t₀ l / (p l + t₀ l)) := by
  have hx'0 : ∀ i, x' i ≠ 0 := by
    intro i h; have := hε i; simp [elasticity, h] at this
  obtain ⟨c, hc, hord⟩ := inverse_elasticity hCS hx (fun i => (hxpos i).ne')
    (fun i => (hq i).ne') hx'0 hmax
  have cpos : 0 < c := by
    by_contra hc0
    push Not at hc0
    have : revenue x p t₀ ≤ 0 := by
      apply sum_nonpos
      intro i _
      have h1 : t₀ i / (p i + t₀ i) ≤ 0 := by rw [hc i]; exact div_nonpos_of_nonpos_of_nonneg hc0 (hε i).le
      have h2 : t₀ i ≤ 0 := by
        by_contra h; push Not at h; exact absurd h1 (not_le.2 (div_pos h (hq i)))
      exact mul_nonpos_of_nonpos_of_nonneg h2 (hxpos i).le
    linarith
  exact ⟨c, cpos, hc, fun k l hlk => hord cpos k l (hε l) hlk⟩

end RamseyTax
end Econ

end
