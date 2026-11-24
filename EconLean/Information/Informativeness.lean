/-
# The informativeness principle (Holmström 1979; Grossman–Hart 1983)

Holmström (1979), Shavell (1979); Bolton–Dewatripont, *Contract Theory*, §4.4;
Laffont–Martimort, §4.6. An agent chooses an action `a ∈ A` at private cost `c a`; the
principal observes an outcome `x ∈ X` and an extra signal `y ∈ Y`, jointly distributed as
`f a x y`. As in `MoralHazard`, contracts are written in **utility terms**: `ν x y` is the
agent's utility after `(x, y)`, which costs the principal `φ (ν x y)`, with `φ = u⁻¹`
convex on an interval `U` of utility levels (the agent is risk averse).

The outcome `x` is a **sufficient statistic** for `(x, y)` with respect to the action if
`f a x y = g a x · h x y`, where the conditional law `h x ·` of the signal given the outcome
does not depend on the action.

* `informativeness_principle`: if `x` is sufficient, replacing any contract `ν` by its
  conditional expectation `ν̄ x = ∑_y h x y ν x y`, which ignores `y` and stays in `U`, gives
  the agent the same
  expected utility under **every** action (so it satisfies the same participation and
  incentive constraints) and costs the principal weakly less under every action (Jensen).
  Hence some optimal contract does not condition on a signal that carries no further
  information about the action.
* `informativeness_strict`: if `φ` is strictly convex and the contract really varies with `y`
  at an outcome that the implemented action reaches with positive probability, the saving is
  strict: conditioning on an uninformative signal only adds risk.

The converse half of Holmström's principle (a signal that is *not* garbled by `x` has
strictly positive value under the first-order approach) is not formalized.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

namespace Econ

open Finset

variable {A X Y : Type*} [Fintype X] [Fintype Y]

/-- The agent's expected utility from the contract `ν` under action `a`, net of effort cost. -/
def agentValue (f : A → X → Y → ℝ) (c : A → ℝ) (ν : X → Y → ℝ) (a : A) : ℝ :=
  ∑ x, ∑ y, f a x y * ν x y - c a

/-- The principal's expected payment for the contract `ν` under action `a`. -/
def principalCost (f : A → X → Y → ℝ) (φ : ℝ → ℝ) (ν : X → Y → ℝ) (a : A) : ℝ :=
  ∑ x, ∑ y, f a x y * φ (ν x y)

/-- `ν` **implements** `a` with reservation utility `ū`: IR and IC against every action. -/
def Implements (f : A → X → Y → ℝ) (c : A → ℝ) (ū : ℝ) (ν : X → Y → ℝ) (a : A) : Prop :=
  ū ≤ agentValue f c ν a ∧ ∀ a', agentValue f c ν a' ≤ agentValue f c ν a

/-- The contract that pays the conditional expectation of `ν` given the outcome. -/
def condContract (h : X → Y → ℝ) (ν : X → Y → ℝ) : X → Y → ℝ := fun x _ => ∑ y, h x y * ν x y

/-- Under sufficiency, the conditional-expectation contract gives the same expected utility
under every action. -/
lemma agentValue_condContract {f : A → X → Y → ℝ} {g : A → X → ℝ} {h : X → Y → ℝ}
    (hsuff : ∀ a x y, f a x y = g a x * h x y) (hh1 : ∀ x, ∑ y, h x y = 1) (c : A → ℝ)
    (ν : X → Y → ℝ) (a : A) : agentValue f c (condContract h ν) a = agentValue f c ν a := by
  simp only [agentValue, condContract, hsuff]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_mul, ← mul_sum, hh1 x, mul_one, mul_sum]
  exact sum_congr rfl fun y _ => by ring

/-- **The informativeness principle** (Holmström 1979). If the outcome is a sufficient
statistic for (outcome, signal) with respect to the action, the contract `ν̄ = E[ν | x]`, which
ignores the signal, implements whatever `ν` implements and costs weakly less under every
action. -/
theorem informativeness_principle {f : A → X → Y → ℝ} {g : A → X → ℝ} {h : X → Y → ℝ}
    (hsuff : ∀ a x y, f a x y = g a x * h x y) (hg : ∀ a x, 0 ≤ g a x)
    (hh0 : ∀ x y, 0 ≤ h x y) (hh1 : ∀ x, ∑ y, h x y = 1) {U : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ U φ) {ν : X → Y → ℝ} (hν : ∀ x y, ν x y ∈ U) (c : A → ℝ) :
    (∀ x y, condContract h ν x y ∈ U) ∧
      (∀ a, agentValue f c (condContract h ν) a = agentValue f c ν a) ∧
      (∀ ū a, Implements f c ū ν a → Implements f c ū (condContract h ν) a) ∧
      ∀ a, principalCost f φ (condContract h ν) a ≤ principalCost f φ ν a := by
  have hval := agentValue_condContract hsuff hh1 c ν
  refine ⟨fun x _ => hφ.1.sum_mem (fun y _ => hh0 x y) (hh1 x) fun y _ => hν x y, hval, fun ū a ⟨hIR, hIC⟩ => ⟨by rw [hval]; exact hIR, fun a' => by
    rw [hval, hval]; exact hIC a'⟩, fun a => ?_⟩
  simp only [principalCost, condContract, hsuff]
  refine sum_le_sum fun x _ => ?_
  rw [← sum_mul, ← mul_sum, hh1 x, mul_one]
  -- Jensen with weights `h x ·`.
  have hj : φ (∑ y, h x y • ν x y) ≤ ∑ y, h x y • φ (ν x y) :=
    hφ.map_sum_le (fun y _ => hh0 x y) (hh1 x) fun y _ => hν x y
  simp only [smul_eq_mul] at hj
  calc g a x * φ (∑ y, h x y * ν x y) ≤ g a x * ∑ y, h x y * φ (ν x y) :=
        mul_le_mul_of_nonneg_left hj (hg a x)
    _ = ∑ y, g a x * h x y * φ (ν x y) := by rw [mul_sum]; exact sum_congr rfl fun y _ => by ring

/-- **Strict version**: with `φ` strictly convex, if at some outcome `x₀` reached with
positive probability under `a` the contract varies across two signals of positive conditional
probability, ignoring the signal strictly lowers the principal's cost under `a`. -/
theorem informativeness_strict {f : A → X → Y → ℝ} {g : A → X → ℝ} {h : X → Y → ℝ}
    (hsuff : ∀ a x y, f a x y = g a x * h x y) (hg : ∀ a x, 0 ≤ g a x)
    (hh0 : ∀ x y, 0 ≤ h x y) (hh1 : ∀ x, ∑ y, h x y = 1) {U : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConvexOn ℝ U φ) {ν : X → Y → ℝ} (hν : ∀ x y, ν x y ∈ U) (a : A) {x₀ : X}
    (hx₀ : 0 < g a x₀) {y₁ y₂ : Y} (hy₁ : 0 < h x₀ y₁) (hy₂ : 0 < h x₀ y₂)
    (hne : ν x₀ y₁ ≠ ν x₀ y₂) :
    principalCost f φ (condContract h ν) a < principalCost f φ ν a := by
  simp only [principalCost, condContract, hsuff]
  have term : ∀ x, g a x * φ (∑ y, h x y * ν x y) ≤ ∑ y, g a x * h x y * φ (ν x y) := fun x => by
    have hj : φ (∑ y, h x y • ν x y) ≤ ∑ y, h x y • φ (ν x y) :=
      hφ.convexOn.map_sum_le (fun y _ => hh0 x y) (hh1 x) fun y _ => hν x y
    simp only [smul_eq_mul] at hj
    calc g a x * φ (∑ y, h x y * ν x y) ≤ g a x * ∑ y, h x y * φ (ν x y) :=
          mul_le_mul_of_nonneg_left hj (hg a x)
      _ = ∑ y, g a x * h x y * φ (ν x y) := by
          rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  have hstrict : g a x₀ * φ (∑ y, h x₀ y * ν x₀ y) < ∑ y, g a x₀ * h x₀ y * φ (ν x₀ y) := by
    set t := univ.filter fun y => 0 < h x₀ y
    have hsub : ∀ k : Y → ℝ, ∑ y ∈ t, h x₀ y * k y = ∑ y, h x₀ y * k y := fun k =>
      sum_filter_of_ne fun y _ hy => lt_of_le_of_ne (hh0 x₀ y) fun h0 => hy (by rw [← h0, zero_mul])
    have ht1 : ∑ y ∈ t, h x₀ y = 1 := by
      have := hsub fun _ => 1
      simp only [mul_one] at this
      rw [this, hh1]
    have hj' := hφ.map_sum_lt (t := t) (w := h x₀) (p := ν x₀)
      (fun y hy => (mem_filter.1 hy).2) ht1 (fun y _ => hν x₀ y)
      ⟨y₁, mem_filter.2 ⟨mem_univ _, hy₁⟩, y₂, mem_filter.2 ⟨mem_univ _, hy₂⟩, hne⟩
    simp only [smul_eq_mul, hsub] at hj'
    have hj : φ (∑ y, h x₀ y • ν x₀ y) < ∑ y, h x₀ y • φ (ν x₀ y) := by
      simpa only [smul_eq_mul] using hj'
    simp only [smul_eq_mul] at hj
    calc g a x₀ * φ (∑ y, h x₀ y * ν x₀ y) < g a x₀ * ∑ y, h x₀ y * φ (ν x₀ y) :=
          mul_lt_mul_of_pos_left hj hx₀
      _ = ∑ y, g a x₀ * h x₀ y * φ (ν x₀ y) := by
          rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  calc ∑ x, ∑ y, g a x * h x y * φ (∑ y, h x y * ν x y)
      = ∑ x, g a x * φ (∑ y, h x y * ν x y) := by
        refine sum_congr rfl fun x _ => ?_
        rw [← sum_mul, ← mul_sum, hh1 x, mul_one]
    _ < ∑ x, ∑ y, g a x * h x y * φ (ν x y) :=
        sum_lt_sum (fun x _ => term x) ⟨x₀, mem_univ _, hstrict⟩

/-- Witness: one action, one outcome, a fair coin as signal, `φ = exp` (CARA-type cost) and a
contract paying utility `0` or `1` by the coin: ignoring the coin is strictly cheaper. -/
example : principalCost (A := Unit) (X := Unit) (Y := Bool) (fun _ _ _ => 1 / 2) Real.exp
      (condContract (fun _ _ => 1 / 2) fun _ y => if y then 1 else 0) () <
    principalCost (A := Unit) (X := Unit) (Y := Bool) (fun _ _ _ => 1 / 2) Real.exp
      (fun _ y => if y then 1 else 0) () :=
  informativeness_strict (g := fun _ _ => 1) (fun _ _ _ => by ring) (fun _ _ => zero_le_one)
    (fun _ _ => by norm_num) (fun _ => by simp) strictConvexOn_exp
    (fun _ _ => Set.mem_univ _) () (x₀ := ()) one_pos (y₁ := true) (y₂ := false) (by norm_num)
    (by norm_num) (by simp)

end Econ
