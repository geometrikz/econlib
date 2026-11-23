/-
# Motivated beliefs: optimal expectations

Reference. M. Brunnermeier and J. Parker (2005), "Optimal Expectations",
*AER* 95(4), Propositions 1–2; see also R. Bénabou and J. Tirole (2016),
"Mindful Economics", *JEP* 30(3).

An agent holds a subjective probability `p ∈ [0, 1]` of a good state whose
true probability is `q`. Beliefs affect well-being in two ways:
* **anticipatory utility** `A(p)`: savoring the future under belief `p`;
* **realized utility** `R(p)`: the true expected payoff of the action chosen
  under belief `p`. Since actions are chosen optimally given beliefs, correct
  beliefs are best for realized utility: `R` is maximized at `p = q`.

Optimal expectations maximize `W(p) = A(p) + R(p)`. This is Brunnermeier and
Parker's argument in reduced form: `R` is taken as a primitive maximized at
`q`, rather than built from an action chosen under `p` and evaluated under `q`.

**Results.**
* `rational_not_optimal` (Brunnermeier–Parker Proposition 1): if
  `q ∈ (0, 1)`, `R` is differentiable at `q` and maximized there, and
  `A'(q) ≠ 0`, then rational beliefs `p = q` are **not** optimal: the
  first-order loss in realized utility from distorting beliefs is zero, but
  the gain in anticipation is first order.
* `exists_better_belief`: in particular some belief in `[0, 1]` gives
  strictly higher well-being than the truth.
* Example (`example_optimal`, `example_optimism`): with `A(p) = p` (anticipation
  of a prize worth 1) and quadratic decision loss `R(p) = −(p − q)²`, the
  optimal belief is `p* = q + 1/2 > q`, which lies in `[0, 1]` for
  `0 ≤ q ≤ 1/2`: the agent is optimistic.
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

namespace Econ

namespace MotivatedBeliefs

open Set

/-- **Brunnermeier–Parker (2005), Proposition 1.** If realized utility `R`
is maximized at the true probability `q ∈ (0, 1)` and anticipatory utility
`A` has nonzero slope there, rational beliefs do not maximize well-being
`A + R` on `[0, 1]`. -/
theorem rational_not_optimal {A R : ℝ → ℝ} {q a : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hA : HasDerivAt A a q) (hR : DifferentiableAt ℝ R q) (hRmax : IsMaxOn R (Icc 0 1) q)
    (ha : a ≠ 0) : ¬ IsMaxOn (fun p => A p + R p) (Icc 0 1) q := by
  have hnhds : Icc (0 : ℝ) 1 ∈ nhds q := Icc_mem_nhds hq.1 hq.2
  have hr : deriv R q = 0 := (hRmax.isLocalMax hnhds).hasDerivAt_eq_zero hR.hasDerivAt
  intro hW
  have := (hW.isLocalMax hnhds).hasDerivAt_eq_zero (hA.add hR.hasDerivAt)
  exact ha (by linarith)

/-- Some belief strictly beats the truth. -/
theorem exists_better_belief {A R : ℝ → ℝ} {q a : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hA : HasDerivAt A a q) (hR : DifferentiableAt ℝ R q) (hRmax : IsMaxOn R (Icc 0 1) q)
    (ha : a ≠ 0) : ∃ p ∈ Icc (0 : ℝ) 1, A q + R q < A p + R p := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  exact rational_not_optimal hq hA hR hRmax ha fun p hp => h p hp

/-- Example well-being: anticipation `p`, decision loss `(p − q)²`. -/
def W (q p : ℝ) : ℝ := p - (p - q) ^ 2

/-- The unconstrained optimal belief is `q + 1/2` (it lies in `[0, 1]` when
`0 ≤ q ≤ 1/2`, see `example_optimism`). -/
theorem example_optimal (q p : ℝ) : W q p ≤ W q (q + 1 / 2) := by
  unfold W; nlinarith [sq_nonneg (p - q - 1 / 2)]

/-- Optimal expectations are optimistic: `p* = q + 1/2 > q`, and the optimal
belief lies in `[0, 1]` when `0 ≤ q ≤ 1/2`. -/
theorem example_optimism {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    q < q + 1 / 2 ∧ q + 1 / 2 ∈ Icc (0 : ℝ) 1 ∧ W q q < W q (q + 1 / 2) := by
  refine ⟨by linarith, ⟨by linarith, by linarith⟩, ?_⟩
  unfold W; nlinarith

/-- Non-vacuity: the hypotheses of `rational_not_optimal` hold in the example
with `q = 1/4`, so rational beliefs are not optimal there. -/
example : ¬ IsMaxOn (fun p : ℝ => p + -(p - 1 / 4) ^ 2) (Icc 0 1) (1 / 4) := by
  refine rational_not_optimal (A := fun p => p) (R := fun p => -(p - 1 / 4) ^ 2) (a := 1)
    ⟨by norm_num, by norm_num⟩ (hasDerivAt_id' _) ?_ ?_ one_ne_zero
  · refine HasDerivAt.differentiableAt (f' := -(2 * (1 / 4 - 1 / 4))) ?_
    have h1 : HasDerivAt (fun p : ℝ => p - 1 / 4) 1 (1 / 4) :=
      (hasDerivAt_id' (1 / 4 : ℝ)).sub_const (1 / 4)
    have h2 : HasDerivAt (fun p : ℝ => (p - 1 / 4) ^ 2) (↑2 * (1 / 4 - 1 / 4) ^ (2 - 1) * 1)
        (1 / 4) := h1.fun_pow 2
    convert h2.neg using 1; norm_num
  · intro p _; simp only [Set.mem_ofPred_eq, sub_self]; nlinarith [sq_nonneg (p - 1 / 4)]

end MotivatedBeliefs

end Econ
