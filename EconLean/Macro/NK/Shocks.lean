/-
# The New Keynesian model with shocks: divine coincidence and optimal discretion

Galí, *Monetary Policy, Inflation, and the Business Cycle*, ch. 4–5;
Blanchard–Galí (2007); Clarida–Galí–Gertler (1999).

**Setup.** The three-equation model of `Macro/NK/ThreeEquation.lean` with two
exogenous (perfect-foresight) shock paths: the natural rate `rⁿ_t` in the IS
curve and a cost-push shock `u_t` in the Phillips curve:

* `x_t = x_{t+1} − (i_t − π_{t+1} − rⁿ_t)/σ`,
* `π_t = β π_{t+1} + κ x_t + u_t`.

The central bank's period loss is `π_t² + λ x_t²` (Woodford's second-order
approximation to household welfare), so the first best is `π = x = 0`.

**Results.**
* `zero_isShockEquilibrium`, `divine_coincidence`: without cost-push shocks,
  the rule `i_t = rⁿ_t + φ_π π_t + φ_x x_t` supports `π = x = 0`, and if the
  Bullard–Mitra condition holds it is the **only** bounded equilibrium. Stabilizing
  inflation also stabilizes the welfare-relevant output gap (Blanchard–Galí's
  "divine coincidence").
* `no_firstBest_of_costPush`: with a cost-push shock no policy attains `π = x = 0`
  (immediate from the Phillips curve at the shock date, whatever the policy).
* `discretion_static`: given expectations, the discretionary central bank's
  problem `min π² + λ x²` s.t. `π = κ x + v` has the unique solution
  `x = −κ v/(λ + κ²)`, `π = λ v/(λ + κ²)`: the **targeting rule** `x = −(κ/λ) π`.
* `discretion_unique`: with an AR(1) cost-push path `u_t = ρᵗ u₀`, `|ρ| ≤ 1`,
  the unique bounded path satisfying the Phillips curve and the targeting rule is
  `π_t = λ u_t / (κ² + λ(1 − βρ))`, `x_t = −κ u_t / (κ² + λ(1 − βρ))`
  (Galí eq. (5.6)).

**Deviations.** Perfect foresight: shocks are deterministic sequences known in
advance (the AR(1) path is the expected path). Discretion is modelled through its
first-order condition (the targeting rule, imposed as a hypothesis rather than
derived from the dynamic discretion game), the standard Markov solution.
`Model` carries the invariants `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_x ≥ 0`.
-/
module

public import EconLean.Macro.NK.ThreeEquation

@[expose] public section

noncomputable section

namespace Econ
namespace NK
namespace Model

variable (E : Model)

/-- Equilibrium with a natural-rate path `rn` and a cost-push path `u`. -/
def IsShockEquilibrium (rn u x p i : ℕ → ℝ) : Prop :=
  ∀ t, x t = x (t + 1) - (i t - p (t + 1) - rn t) / E.σ ∧
    p t = E.β * p (t + 1) + E.κ * x t + u t

/-- The interest rate follows a Taylor rule that tracks the natural rate. -/
def FollowsRule (rn x p i : ℕ → ℝ) : Prop := ∀ t, i t = rn t + E.φπ * p t + E.φx * x t

/-- **The first best is an equilibrium** when there are no cost-push shocks:
`π = x = 0` with `i = rⁿ` satisfies the model and the rule. -/
theorem zero_isShockEquilibrium (rn : ℕ → ℝ) :
    E.IsShockEquilibrium rn 0 0 0 rn ∧ E.FollowsRule rn 0 0 rn := by
  refine ⟨fun t => ⟨?_, ?_⟩, fun t => ?_⟩ <;> simp

/-- Under the rule and without cost-push shocks, deviations solve the
homogeneous model of `ThreeEquation.lean`. -/
theorem isEquilibrium_of_shock {rn x p i : ℕ → ℝ} (h : E.IsShockEquilibrium rn 0 x p i)
    (hr : E.FollowsRule rn x p i) : E.IsEquilibrium x p fun t => i t - rn t := by
  intro t
  obtain ⟨h1, h2⟩ := h t
  refine ⟨?_, by simpa using h2, show i t - rn t = _ by rw [hr t]; ring⟩
  rw [h1]; ring

/-- **Divine coincidence.** Without cost-push shocks, if the Taylor rule
(tracking the natural rate) satisfies `κ(φ_π − 1) + (1 − β)φ_x > 0`, every
bounded equilibrium has `π_t = x_t = 0` for all `t`: the first best is the
unique bounded outcome. -/
theorem divine_coincidence (hdet : 0 < E.κ * (E.φπ - 1) + (1 - E.β) * E.φx)
    {rn x p i : ℕ → ℝ} (h : E.IsShockEquilibrium rn 0 x p i) (hr : E.FollowsRule rn x p i)
    (hb : ∃ B, ∀ t, |x t| ≤ B ∧ |p t| ≤ B) : ∀ t, x t = 0 ∧ p t = 0 := by
  obtain ⟨B, hB⟩ := hb
  have hdet' := E.taylor_principle.2 hdet
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0).1
  have := hdet' x p (fun t => i t - rn t) (E.isEquilibrium_of_shock h hr)
    ⟨B + (E.φπ + E.φx) * B, fun t => ⟨by nlinarith [(hB t).1, E.hφπ, E.hφx],
      by nlinarith [(hB t).2, E.hφπ, E.hφx], ?_⟩⟩
  · exact fun t => ⟨(this t).1, (this t).2.1⟩
  · have e : i t - rn t = E.φπ * p t + E.φx * x t := by rw [hr t]; ring
    rw [e]
    calc |E.φπ * p t + E.φx * x t| ≤ |E.φπ * p t| + |E.φx * x t| := abs_add_le _ _
      _ = E.φπ * |p t| + E.φx * |x t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg E.hφπ, abs_of_nonneg E.hφx]
      _ ≤ E.φπ * B + E.φx * B := by
          gcongr
          · exact E.hφπ
          · exact (hB t).2
          · exact E.hφx
          · exact (hB t).1
      _ ≤ _ := by nlinarith [mul_nonneg (add_nonneg E.hφπ E.hφx) hB0]

/-- **Cost-push shocks break the divine coincidence.** If `u_t ≠ 0` at some
date, no interest-rate path attains `π = x = 0` at all dates. -/
theorem no_firstBest_of_costPush {rn u : ℕ → ℝ} {t : ℕ} (hu : u t ≠ 0) {x p i : ℕ → ℝ}
    (h : E.IsShockEquilibrium rn u x p i) : ¬ ∀ s, x s = 0 ∧ p s = 0 := by
  intro h0
  have := (h t).2
  rw [(h0 t).2, (h0 (t + 1)).2, (h0 t).1] at this
  exact hu (by linarith)

end Model

/-- **Optimal discretion, one period.** Given the private sector's expectations,
the Phillips curve reads `π = κ x + v`. Minimizing `π² + λ x²` (`λ > 0`) over
`x`: the unique minimizer is `x* = −κ v/(λ + κ²)`, so that `π* = λ v/(λ + κ²)`
and the **targeting rule** `x* = −(κ/λ) π*` holds. -/
theorem discretion_static {κ lam v : ℝ} (hlam : 0 < lam) :
    let xs := -κ * v / (lam + κ ^ 2)
    (∀ x, (κ * xs + v) ^ 2 + lam * xs ^ 2 ≤ (κ * x + v) ^ 2 + lam * x ^ 2) ∧
    (∀ x, (κ * x + v) ^ 2 + lam * x ^ 2 = (κ * xs + v) ^ 2 + lam * xs ^ 2 → x = xs) ∧
    κ * xs + v = lam * v / (lam + κ ^ 2) ∧ xs = -(κ / lam) * (κ * xs + v) := by
  intro xs
  have hD : 0 < lam + κ ^ 2 := by positivity
  -- the loss is `(λ + κ²)(x − x*)²` plus a constant
  have key : ∀ x, (κ * x + v) ^ 2 + lam * x ^ 2 =
      (lam + κ ^ 2) * (x - xs) ^ 2 + ((κ * xs + v) ^ 2 + lam * xs ^ 2) := fun x => by
    simp only [xs]; field_simp; ring
  refine ⟨fun x => by rw [key x]; nlinarith [sq_nonneg (x - xs)], fun x hx => ?_, ?_, ?_⟩
  · rw [key x] at hx
    have : (lam + κ ^ 2) * (x - xs) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left hD.ne')
    linarith
  · simp only [xs]; field_simp; ring
  · simp only [xs]; field_simp; ring

/-- **Optimal discretion with an AR(1) cost-push path** (Galí eq. (5.6)). Let
`u_t = ρᵗ u₀` with `|ρ| ≤ 1`, `β ∈ (0,1)`, `κ, λ > 0`. The unique bounded path
satisfying the Phillips curve `π_t = β π_{t+1} + κ x_t + u_t` and the targeting
rule `x_t = −(κ/λ) π_t` is `π_t = λ u_t/D`, `x_t = −κ u_t/D` with
`D = κ² + λ(1 − βρ)`. -/
theorem discretion_unique {β κ lam ρ u₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) {x p : ℕ → ℝ}
    (hpc : ∀ t, p t = β * p (t + 1) + κ * x t + ρ ^ t * u₀)
    (htr : ∀ t, x t = -(κ / lam) * p t) (hb : ∃ B, ∀ t, |p t| ≤ B) :
    ∀ t, p t = lam * (ρ ^ t * u₀) / (κ ^ 2 + lam * (1 - β * ρ)) ∧
      x t = -κ * (ρ ^ t * u₀) / (κ ^ 2 + lam * (1 - β * ρ)) := by
  have hβρ : β * ρ < 1 := by
    have := neg_abs_le ρ; have := le_abs_self ρ
    nlinarith [abs_nonneg ρ]
  have hD : 0 < κ ^ 2 + lam * (1 - β * ρ) := by nlinarith
  set D := κ ^ 2 + lam * (1 - β * ρ)
  set ps : ℕ → ℝ := fun t => lam * (ρ ^ t * u₀) / D
  -- the candidate solves `a π_t = β π_{t+1} + u_t` with `a = 1 + κ²/λ`
  set a := 1 + κ ^ 2 / lam
  have ha : 1 < a := by have : 0 < κ ^ 2 / lam := by positivity
                        linarith
  have hps : ∀ t, a * ps t = β * ps (t + 1) + ρ ^ t * u₀ := fun t => by
    simp only [ps, a, pow_succ]; field_simp; ring
  have hp : ∀ t, a * p t = β * p (t + 1) + ρ ^ t * u₀ := fun t => by
    have := hpc t; rw [htr t] at this; simp only [a]; field_simp at this ⊢; linarith
  -- the difference grows at rate `a/β > 1`
  set d : ℕ → ℝ := fun t => p t - ps t
  have hd : ∀ t, d (t + 1) = (a / β) * d t := fun t => by
    simp only [d]; field_simp; linarith [hp t, hps t]
  have hgeom : ∀ t, d t = (a / β) ^ t * d 0 := fun t => by
    induction t with
    | zero => simp
    | succ t ih => rw [hd, ih, pow_succ]; ring
  obtain ⟨B, hB⟩ := hb
  have hr : 1 < |a / β| := by
    rw [abs_of_pos (by positivity), one_lt_div hβ₀]; linarith
  have hps_b : ∀ t, |ps t| ≤ lam * |u₀| / D := fun t => by
    simp only [ps, abs_div, abs_mul, abs_pow, abs_of_pos hlam, abs_of_pos hD]
    gcongr
    calc |ρ| ^ t * |u₀| ≤ 1 * |u₀| := by
          gcongr; exact pow_le_one₀ (abs_nonneg _) hρ
      _ = |u₀| := one_mul _
  have h0 : d 0 = 0 := eq_zero_of_geom hr (C := B + lam * |u₀| / D) fun t => by
    rw [← hgeom]
    exact (abs_sub _ _).trans (add_le_add (hB t) (hps_b t))
  intro t
  have hpt : p t = ps t := by
    have := hgeom t; rw [h0, mul_zero] at this; simp only [d] at this; linarith
  refine ⟨hpt, ?_⟩
  rw [htr t, hpt]; simp only [ps]; field_simp

/-- **Non-vacuity.** With `σ = 1`, `κ = 1/10`, `β = 99/100`, `φ_π = 3/2`,
`φ_x = 0`, the divine-coincidence hypothesis holds. -/
example : 0 < (1 / 10 : ℝ) * (3 / 2 - 1) + (1 - 99 / 100) * 0 := by norm_num

end NK
end Econ

end
