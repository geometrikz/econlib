/-
# Zero capital taxation in the long run (Chamley–Judd) and its caveat (Straub–Werning)

Chamley (1986), "Optimal Taxation of Capital Income in General Equilibrium
with Infinite Lives", Econometrica; Judd (1985), J. Public Econ.;
Straub and Werning (2020), "Positive Long-Run Capital Taxation: Chamley–Judd
Revisited", AER; Ljungqvist–Sargent, *Recursive Macroeconomic Theory*, ch. 16.

**Setting (primal approach).** A representative household with discount
factor `β ∈ (0,1)` saves in capital with pre-tax net return `rₜ = F_k − δ`;
capital income at `t` is taxed at `τₜ`. Write `ucₜ > 0` for the household's
marginal utility along the Ramsey allocation and `Wcₜ > 0` for the marginal
value of consumption in the planner's pseudo-utility
`W = u + Φ·(implementability term)`. The Ramsey allocation satisfies two
intertemporal conditions (`IsRamseyFOC`):

* household Euler equation: `ucₜ = β uc_{t+1} (1 + (1 − τ_{t+1}) r_{t+1})`;
* planner's capital first-order condition: `Wcₜ = β Wc_{t+1} (1 + r_{t+1})`
  (the planner faces the undistorted return).

**Results.**
* `chamley_judd`: if the allocation converges to an interior steady state
  (`uc`, `Wc`, `r`, `τ` converge, with positive limits of `uc`, `Wc` and a
  nonzero limiting return), the limiting capital tax is zero. The convergence
  of the multiplier-weighted marginal value `Wc` is an assumption, and it is
  exactly the assumption Straub–Werning show can fail.
* `ratio_unbounded` (the Straub–Werning caveat): if the capital tax stays
  bounded away from zero, `τₜ ≥ τ̲ > 0`, and the return stays bounded away
  from zero, then `ucₜ/Wcₜ` grows without bound. So the convergence
  hypothesis in `chamley_judd` is not innocuous: Straub and Werning exhibit
  Ramsey plans (e.g. CRRA with `σ > 1`) along which the marginal-utility
  ratio does not settle, and the optimal capital tax stays positive forever.
* `wedge_unbounded`: a constant capital tax `τ > 0` is an implicit tax on
  date-`T` consumption that grows geometrically,
  `((1 + r)/(1 + (1 − τ) r))^T → ∞`: the intuition behind Chamley–Judd.

**Deviations.** The Ramsey problem itself (maximization over implementable
allocations) is not formalized; its two intertemporal first-order
conditions are taken as the hypothesis `IsRamseyFOC`. We do not construct a
Straub–Werning economy; `ratio_unbounded` shows precisely which hypothesis
their counterexamples violate.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

@[expose] public section

noncomputable section

namespace Econ
namespace ChamleyJudd

open Filter Topology

/-- The two intertemporal optimality conditions of a Ramsey plan. -/
def IsRamseyFOC (β : ℝ) (uc Wc r τ : ℕ → ℝ) : Prop :=
  ∀ t, uc t = β * uc (t + 1) * (1 + (1 - τ (t + 1)) * r (t + 1)) ∧
    Wc t = β * Wc (t + 1) * (1 + r (t + 1))

/-- **Chamley–Judd.** If a Ramsey plan converges to an interior steady state,
the long-run tax on capital income is zero. -/
theorem chamley_judd {β : ℝ} (hβ : 0 < β) {uc Wc r τ : ℕ → ℝ} (h : IsRamseyFOC β uc Wc r τ)
    {ucs Wcs rs τs : ℝ} (hucs : 0 < ucs) (hWcs : 0 < Wcs) (hrs : rs ≠ 0)
    (huc : Tendsto uc atTop (𝓝 ucs)) (hWc : Tendsto Wc atTop (𝓝 Wcs))
    (hr : Tendsto r atTop (𝓝 rs)) (hτ : Tendsto τ atTop (𝓝 τs)) :
    τs = 0 := by
  have sh : ∀ {f : ℕ → ℝ} {a}, Tendsto f atTop (𝓝 a) → Tendsto (fun t => f (t + 1)) atTop (𝓝 a) :=
    fun hf => hf.comp (tendsto_add_atTop_nat 1)
  have e1 : ucs = β * ucs * (1 + (1 - τs) * rs) := by
    have hR : Tendsto (fun t => β * uc (t + 1) * (1 + (1 - τ (t + 1)) * r (t + 1))) atTop
        (𝓝 (β * ucs * (1 + (1 - τs) * rs))) :=
      ((sh huc).const_mul β).mul (tendsto_const_nhds.add
        ((tendsto_const_nhds.sub (sh hτ)).mul (sh hr)))
    exact tendsto_nhds_unique huc (hR.congr fun t => ((h t).1).symm)
  have e2 : Wcs = β * Wcs * (1 + rs) := by
    have hR : Tendsto (fun t => β * Wc (t + 1) * (1 + r (t + 1))) atTop
        (𝓝 (β * Wcs * (1 + rs))) :=
      ((sh hWc).const_mul β).mul (tendsto_const_nhds.add (sh hr))
    exact tendsto_nhds_unique hWc (hR.congr fun t => ((h t).2).symm)
  have a1 : β * (1 + (1 - τs) * rs) = 1 := by
    have : ucs * (β * (1 + (1 - τs) * rs) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hucs.ne'
    · linarith
  have a2 : β * (1 + rs) = 1 := by
    have : Wcs * (β * (1 + rs) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hWcs.ne'
    · linarith
  have : β * (τs * rs) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hβ.ne'
  · rcases mul_eq_zero.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 hrs

/-- **The Straub–Werning caveat.** If the capital tax and the return stay
bounded away from zero, `τₜ ≥ τ̲ > 0` (with `τₜ ≤ 1`) and `rₜ ≥ r̲ > 0`, then the ratio of
marginal utility to the planner's marginal value of consumption is unbounded,
so the plan cannot converge to an interior steady state with `uc`, `Wc`
bounded and bounded away from zero. A permanently positive capital tax is
therefore consistent with the Ramsey first-order conditions exactly when the
convergence hypothesis of `chamley_judd` fails. -/
theorem ratio_unbounded {β : ℝ} {uc Wc r τ : ℕ → ℝ} (h : IsRamseyFOC β uc Wc r τ)
    (huc : ∀ t, 0 < uc t) (hWc : ∀ t, 0 < Wc t)
    {τl rl : ℝ} (hτl : 0 < τl) (hτ : ∀ t, τl ≤ τ t ∧ τ t ≤ 1)
    (hrl : 0 < rl) (hr : ∀ t, rl ≤ r t) :
    ∀ M, ∃ t, M < uc t / Wc t := by
  -- one-period growth factor of `uc/Wc` is at least `q > 1`
  set q := (1 + rl) / (1 + (1 - τl) * rl) with hq
  have hτl1 : τl ≤ 1 := (hτ 0).1.trans (hτ 0).2
  have hden : 0 < 1 + (1 - τl) * rl := by nlinarith
  have hq1 : 1 < q := by
    rw [hq, one_lt_div hden]; nlinarith
  have step : ∀ t, q * (uc t / Wc t) ≤ uc (t + 1) / Wc (t + 1) := by
    intro t
    obtain ⟨h1, h2⟩ := h t
    obtain ⟨ht1, ht2⟩ := hτ (t + 1)
    have hr1 := hr (t + 1)
    have hβ : 0 < β := by
      have := hWc t; rw [h2] at this
      have p1 := hWc (t + 1)
      have p2 : 0 < 1 + r (t + 1) := by linarith
      by_contra hb; push Not at hb
      have : β * Wc (t + 1) * (1 + r (t + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hb p1.le) p2.le
      linarith
    set x := r (t + 1); set s := τ (t + 1)
    have dpos : 0 < 1 + (1 - s) * x := by nlinarith
    -- `uc t/Wc t = ratio(t+1) · (1+(1-s)x)/(1+x)`
    have e : uc t / Wc t = uc (t + 1) / Wc (t + 1) * ((1 + (1 - s) * x) / (1 + x)) := by
      rw [h1, h2]; field_simp
    rw [e]
    have hR : 0 ≤ uc (t + 1) / Wc (t + 1) := (div_pos (huc _) (hWc _)).le
    -- `q · (1+(1-s)x)/(1+x) ≤ 1`
    have key : q * ((1 + (1 - s) * x) / (1 + x)) ≤ 1 := by
      rw [hq, div_mul_div_comm, div_le_one (mul_pos hden (by linarith))]
      -- (1+rl)(1+(1-s)x) ≤ (1+(1-τl)rl)(1+x)
      nlinarith [mul_le_mul_of_nonneg_left hr1 hτl.le,
        mul_nonneg (mul_nonneg hrl.le (hrl.le.trans hr1)) (by linarith : (0:ℝ) ≤ s - τl),
        mul_le_mul_of_nonneg_right ht1 (hrl.le.trans hr1)]
    calc q * (uc (t + 1) / Wc (t + 1) * ((1 + (1 - s) * x) / (1 + x)))
        = (q * ((1 + (1 - s) * x) / (1 + x))) * (uc (t + 1) / Wc (t + 1)) := by ring
      _ ≤ 1 * (uc (t + 1) / Wc (t + 1)) := mul_le_mul_of_nonneg_right key hR
      _ = _ := one_mul _
  have grow : ∀ t, q ^ t * (uc 0 / Wc 0) ≤ uc t / Wc t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc q ^ (t + 1) * (uc 0 / Wc 0) = q * (q ^ t * (uc 0 / Wc 0)) := by ring
        _ ≤ q * (uc t / Wc t) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ _ := step t
  intro M
  have h0 : 0 < uc 0 / Wc 0 := div_pos (huc 0) (hWc 0)
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (M / (uc 0 / Wc 0)) hq1
  refine ⟨t, lt_of_lt_of_le ?_ (grow t)⟩
  rwa [div_lt_iff₀ h0] at ht

/-- **The exploding intertemporal wedge.** A constant tax `τ ∈ (0, 1]` on
capital income with net return `r > 0` taxes consumption at date `T`
relative to date `0` by the factor `((1 + r)/(1 + (1 − τ) r))^T`, which is
unbounded in `T`. -/
theorem wedge_unbounded {τ r : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 < r) (M : ℝ) :
    ∃ T : ℕ, M < ((1 + r) / (1 + (1 - τ) * r)) ^ T := by
  have hden : 0 < 1 + (1 - τ) * r := by nlinarith
  exact pow_unbounded_of_one_lt M (by rw [one_lt_div hden]; nlinarith)

end ChamleyJudd
end Econ

end
