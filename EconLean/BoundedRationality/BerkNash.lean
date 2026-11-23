/-
# Berk–Nash equilibrium: optimization with a misspecified model

Reference. I. Esponda and D. Pouzo (2016), "Berk–Nash Equilibrium: A
Framework for Modeling Agents With Misspecified Models", *Econometrica*
84(3). We formalize the single-agent case (their §2 examples and the
correctly-specified benchmark, Proposition 1 and Remark 1 style).

**The model.** An agent chooses an action `x : X`; an outcome `y : Y` is drawn
from the *true* distribution `Q x`; the payoff is `π x y`. The agent does not
know `Q`. She has a *subjective model*: a finite family of distributions
`Qθ θ x`, `θ : Θ`, all with full support, and a belief `μ` over `Θ`.
Given a mixed action `σ`, the fit of parameter `θ` is the weighted
Kullback–Leibler divergence

    K(σ, θ) = Σ_x σ x · KL(Q x ‖ Qθ θ x).

`(σ, μ)` is a **Berk–Nash equilibrium** if
1. (*optimality*) every action played with positive probability maximizes
   subjective expected payoff under `μ`; and
2. (*consistency*) `μ` puts weight only on parameters minimizing `K(σ, ·)`:
   beliefs are the best fit to the data the agent's own behavior generates.

**Results.**
* `K_nonneg`: `K ≥ 0` (Gibbs' inequality);
* `K_correct`: if the model is **correctly specified** (`Qθ θ* = Q`), then
  `θ*` attains `K = 0` and so minimizes `K`;
* `isBerkNash_of_correct`: in a correctly specified model, every objectively
  optimal action, with belief concentrated on `θ*`, is a Berk–Nash equilibrium;
* `optimal_of_isBerkNash`: conversely, if the model is correctly specified and
  *identified* (a parameter fits perfectly only if it equals the truth at
  every action), every Berk–Nash action is objectively optimal: Berk–Nash
  reduces to optimization;
* `misspecified_example`: with a misspecified model, a Berk–Nash equilibrium
  can choose an objectively worse action.

**Scope.** Existence of Berk–Nash equilibrium (EP Theorem 1) needs Kakutani's
fixed point theorem, which Mathlib lacks; it is not formalized. Games with
several players are not covered.
-/
module

public import EconLean.Behavioral.RationalInattention

@[expose] public section

namespace Econ

namespace BoundedRationality

open Finset Real Logit RationalInattention

variable {X Y Θ : Type*} [Fintype X] [Fintype Y] [Fintype Θ]

/-- A single-agent decision problem with a subjective model. -/
structure SubjectiveProblem (X Y Θ : Type*) [Fintype X] [Fintype Y] [Fintype Θ] where
  /-- true outcome distribution given the action -/
  Q : X → Y → ℝ
  /-- the agent's parametric model -/
  Qθ : Θ → X → Y → ℝ
  /-- payoff -/
  π : X → Y → ℝ
  /-- true distributions are probability vectors -/
  Q_prob : ∀ x, IsProb (Q x)
  /-- model distributions are probability vectors -/
  Qθ_prob : ∀ θ x, IsProb (Qθ θ x)
  /-- model distributions have full support (so `K` is finite). This is
  stronger than Esponda–Pouzo, who allow `K = +∞`. -/
  Qθ_pos : ∀ θ x y, 0 < Qθ θ x y

namespace SubjectiveProblem

variable (M : SubjectiveProblem X Y Θ)

/-- Weighted KL divergence of the model `θ` from the truth, on the actions
played under `σ`. -/
noncomputable def K (σ : X → ℝ) (θ : Θ) : ℝ := ∑ x, σ x * kl (M.Q x) (M.Qθ θ x)

/-- Subjective expected payoff of action `x` under belief `μ`. -/
def subjEU (μ : Θ → ℝ) (x : X) : ℝ := ∑ θ, μ θ * ∑ y, M.Qθ θ x y * M.π x y

/-- True expected payoff of action `x`. -/
def trueEU (x : X) : ℝ := ∑ y, M.Q x y * M.π x y

/-- Berk–Nash equilibrium. -/
def IsBerkNash (σ : X → ℝ) (μ : Θ → ℝ) : Prop :=
  IsProb σ ∧ IsProb μ ∧
    (∀ x, 0 < σ x → ∀ x', M.subjEU μ x' ≤ M.subjEU μ x) ∧
    (∀ θ, 0 < μ θ → ∀ θ', M.K σ θ ≤ M.K σ θ')

/-- `σ` is objectively optimal: it plays only true-payoff maximizers. -/
def IsOptimal (σ : X → ℝ) : Prop := IsProb σ ∧ ∀ x, 0 < σ x → ∀ x', M.trueEU x' ≤ M.trueEU x

/-- The model is correctly specified at `θ*`. -/
def CorrectAt (θs : Θ) : Prop := ∀ x, M.Qθ θs x = M.Q x

theorem K_nonneg [Nonempty Y] {σ : X → ℝ} (hσ : IsProb σ) (θ : Θ) : 0 ≤ M.K σ θ :=
  sum_nonneg fun x _ =>
    mul_nonneg (hσ.1 x) (kl_nonneg (M.Q_prob x) (M.Qθ_prob θ x) (M.Qθ_pos θ x))

/-- **Correct specification ⟹ the true parameter fits perfectly.** -/
theorem K_correct [Nonempty Y] {θs : Θ} (h : M.CorrectAt θs) {σ : X → ℝ} (hσ : IsProb σ) :
    M.K σ θs = 0 ∧ ∀ θ, M.K σ θs ≤ M.K σ θ := by
  have h0 : M.K σ θs = 0 := by
    unfold K
    exact sum_eq_zero fun x _ => by
      rw [h x, (kl_eq_zero_iff (M.Q_prob x) (M.Q_prob x) (by rw [← h x]; exact M.Qθ_pos θs x)).2 rfl,
        mul_zero]
  exact ⟨h0, fun θ => h0 ▸ M.K_nonneg hσ θ⟩

/-- Point-mass belief on `θ*`. -/
def pointBelief [DecidableEq Θ] (θs : Θ) : Θ → ℝ := fun θ => if θ = θs then 1 else 0

theorem pointBelief_isProb [DecidableEq Θ] (θs : Θ) : IsProb (pointBelief θs) :=
  ⟨fun θ => by unfold pointBelief; split_ifs <;> norm_num, by simp [pointBelief]⟩

theorem subjEU_pointBelief [DecidableEq Θ] {θs : Θ} (h : M.CorrectAt θs) (x : X) :
    M.subjEU (pointBelief θs) x = M.trueEU x := by
  simp [subjEU, pointBelief, trueEU, h x]

/-- **Correctly specified models: optimal play is Berk–Nash.** -/
theorem isBerkNash_of_correct [Nonempty Y] [DecidableEq Θ] {θs : Θ} (h : M.CorrectAt θs)
    {σ : X → ℝ} (hσ : M.IsOptimal σ) : M.IsBerkNash σ (pointBelief θs) := by
  refine ⟨hσ.1, pointBelief_isProb θs, ?_, ?_⟩
  · intro x hx x'
    rw [M.subjEU_pointBelief h, M.subjEU_pointBelief h]
    exact hσ.2 x hx x'
  · intro θ hθ θ'
    have : θ = θs := by by_contra hne; simp [pointBelief, hne] at hθ
    subst this
    exact (M.K_correct h hσ.1).2 θ'

/-- A parameter that fits perfectly *on the actions played* equals the truth
at *every* action: the model is identified by the agent's own behavior. -/
def Identified (σ : X → ℝ) : Prop := ∀ θ, M.K σ θ = 0 → ∀ x, M.Qθ θ x = M.Q x

/-- **Correctly specified and identified ⟹ Berk–Nash actions are optimal.** -/
theorem optimal_of_isBerkNash [Nonempty Y] {θs : Θ} (h : M.CorrectAt θs) {σ : X → ℝ}
    {μ : Θ → ℝ} (hBN : M.IsBerkNash σ μ) (hid : M.Identified σ) : M.IsOptimal σ := by
  obtain ⟨hσ, hμ, hopt, hcons⟩ := hBN
  -- every parameter the agent believes in fits perfectly, so equals the truth
  have hfit : ∀ θ, 0 < μ θ → ∀ x, M.Qθ θ x = M.Q x := by
    intro θ hθ
    apply hid θ
    have := hcons θ hθ θs
    rw [(M.K_correct h hσ).1] at this
    exact le_antisymm this (M.K_nonneg hσ θ)
  -- hence subjective = true expected payoffs
  have heu : ∀ x, M.subjEU μ x = M.trueEU x := by
    intro x
    unfold subjEU
    have : ∀ θ ∈ univ, μ θ * ∑ y, M.Qθ θ x y * M.π x y = μ θ * M.trueEU x := by
      intro θ _
      rcases lt_or_eq_of_le (hμ.1 θ) with hpos | hzero
      · rw [hfit θ hpos x]; rfl
      · rw [← hzero]; simp
    rw [sum_congr rfl this, ← sum_mul, hμ.2, one_mul]
  refine ⟨hσ, fun x hx x' => ?_⟩
  rw [← heu, ← heu]
  exact hopt x hx x'

/-! ### A misspecified example

Two actions; outcome `1` is a success. Action `0` succeeds with true
probability `1/2`, action `1` (which costs `1/10`) with `7/10`, so action `1`
is truly better (`3/5 > 1/2`). The agent's model wrongly assumes the action does
not affect the success probability, and only entertains success probabilities
`2/5` (`θ = 0`) or `9/20` (`θ = 1`): **every** model is wrong, including at the
action actually played. Playing action `0`, the best-fitting model is `θ = 1`
(`9/20` is closer to the observed `1/2`); under it both actions succeed equally
often, so the cheaper action `0` is optimal. Thus `(action 0, θ = 1)` is a
Berk–Nash equilibrium in which the KL-minimizing belief sustains a truly
worse action. -/

/-- True success probability of each action, as a distribution on `{fail, success}`. -/
noncomputable def exQ : Fin 2 → Fin 2 → ℝ := fun x y =>
  if x = 0 then 1 / 2 else (if y = 1 then 7 / 10 else 3 / 10)

/-- Model success probability of parameter `θ`, the same for both actions. -/
noncomputable def exS : Fin 2 → ℝ := fun θ => if θ = 0 then 2 / 5 else 9 / 20

/-- The (misspecified) model: success probability `exS θ` whatever the action. -/
noncomputable def exQθ : Fin 2 → Fin 2 → Fin 2 → ℝ := fun θ _ y =>
  if y = 1 then exS θ else 1 - exS θ

/-- Payoff: `1` for a success, minus the cost `1/10` of action `1`. -/
noncomputable def exπ : Fin 2 → Fin 2 → ℝ := fun x y =>
  (if y = 1 then 1 else 0) - (if x = 1 then 1 / 10 else 0)

/-- The example as a subjective decision problem. -/
noncomputable def example1 : SubjectiveProblem (Fin 2) (Fin 2) (Fin 2) where
  Q := exQ
  Qθ := exQθ
  π := exπ
  Q_prob := fun x => ⟨fun y => by unfold exQ; split_ifs <;> norm_num,
    by fin_cases x <;> norm_num [exQ, Fin.sum_univ_two]⟩
  Qθ_prob := fun θ x => ⟨fun y => by unfold exQθ exS; split_ifs <;> norm_num,
    by norm_num [exQθ, Fin.sum_univ_two]⟩
  Qθ_pos := fun θ x y => by unfold exQθ exS; split_ifs <;> norm_num

/-- The model is misspecified: no parameter is correct. -/
theorem example1_misspecified (θ : Fin 2) : ¬ example1.CorrectAt θ := by
  intro h
  have := congrFun (h 0) 1
  fin_cases θ <;> simp [example1, exQθ, exS, exQ] at this <;> norm_num at this

/-- **Misspecification sustains a suboptimal choice**: always choosing action
`0` with belief concentrated on the best-fitting `θ = 1` is a Berk–Nash
equilibrium, yet action `1` has strictly higher true expected payoff. -/
theorem misspecified_example :
    example1.IsBerkNash (fun x => if x = 0 then 1 else 0) (fun θ => if θ = 1 then 1 else 0) ∧
      example1.trueEU 0 < example1.trueEU 1 := by
  refine ⟨⟨⟨fun x => by dsimp only; split_ifs <;> norm_num, by simp⟩,
    ⟨fun θ => by dsimp only; split_ifs <;> norm_num, by simp⟩, ?_, ?_⟩, ?_⟩
  · -- optimality: under `θ = 1` action `0` gives `9/20`, action `1` gives `9/20 − 1/10`
    intro x hx x'
    have hx0 : x = 0 := by by_contra h; simp [h] at hx
    subst hx0
    fin_cases x' <;> norm_num [subjEU, example1, exQθ, exS, exπ, Fin.sum_univ_two]
  · -- consistency: `θ = 1` fits the data from action `0` best
    intro θ hθ θ'
    have hθ1 : θ = 1 := by by_contra h; simp [h] at hθ
    subst hθ1
    -- `K σ θ = KL((1/2,1/2) ‖ (1 − s, s))`; compare `log (9/20) + log (11/20) ≥ log (2/5) + log (3/5)`
    have key : Real.log (2 / 5) + Real.log (3 / 5) ≤ Real.log (9 / 20) + Real.log (11 / 20) := by
      rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    fin_cases θ'
    · simp [K, kl, example1, exQ, exQθ, exS, Fin.sum_univ_two]
      norm_num
      linarith
    · exact le_rfl
  · norm_num [trueEU, example1, exQ, exπ, Fin.sum_univ_two]

end SubjectiveProblem

end BoundedRationality

end Econ
