/-
# Frozen statements: Ramsey–Cass–Koopmans and stochastic DP foundations (M5/M8, F10–F13)

Headline statements of `Macro/DP/Monotone.lean`, `Macro/Growth/Ramsey.lean`,
`Macro/DP/Stochastic.lean`, `Macro/DP/MarkovChain.lean` and the new
`euler_transversality_along` in `Macro/DP/SequenceProblem.lean`, copied verbatim
after they passed two rounds of context-isolated adversarial review (2026-11-23;
record in `Audit/REVIEW-ramsey-stochastic.md`). Each is closed by the library
theorem, so if a library statement is ever weakened, this file stops compiling.
Lightweight stand-in for `leanprover/comparator`. Do not edit a statement here
without a new review.
-/
module

public import EconLean.Macro.Growth.Ramsey
public import EconLean.Macro.DP.Stochastic
public import EconLean.Macro.DP.MarkovChain

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ BoundedContinuousFunction Matrix

section Monotone

theorem frozen_policy_monotone {X : Type*} [TopologicalSpace X] [LinearOrder X]
    (P : DynProg X)
    (hΓ : ∀ x x' y y', x < x' → y ∈ P.Γ x → y' ∈ P.Γ x' → y' < y → y' ∈ P.Γ x ∧ y ∈ P.Γ x')
    (hF : ∀ x x' y y', x < x' → y' < y → y ∈ P.Γ x → y' ∈ P.Γ x → y ∈ P.Γ x' → y' ∈ P.Γ x' →
      P.F x' y' - P.F x y' < P.F x' y - P.F x y)
    {x x' y y' : X} (hx : x < x') (hy : y ∈ P.policy x) (hy' : y' ∈ P.policy x') : y ≤ y' :=
  P.policy_monotone hΓ hF hx hy hy'

theorem frozen_orbit_tendsto_fixedPoint {a b : ℝ} {g : Icc a b → Icc a b} (hg : Monotone g)
    (hc : Continuous g) (x₀ : Icc a b) :
    ∃ k : Icc a b, g k = k ∧ Tendsto (planOf g x₀) atTop (𝓝 k) :=
  orbit_tendsto_fixedPoint hg hc x₀

end Monotone

section Euler

theorem frozen_euler_transversality_along {E : Type*} [AddCommGroup E] [Module ℝ E]
    [PartialOrder E] {F : E → E → ℝ} {Γ : E → Set E} {β : ℝ}
    (hβ : 0 ≤ β) (Fx Fy : E → E → E →ₗ[ℝ] ℝ)
    {x₀ : E} {xs : ℕ → E}
    (hconc : ∀ t x' y', y' ∈ Γ x' → F x' y' ≤ F (xs t) (xs (t + 1)) +
      Fx (xs t) (xs (t + 1)) (x' - xs t) + Fy (xs t) (xs (t + 1)) (y' - xs (t + 1)))
    (hΓ : ∀ x y, y ∈ Γ x → 0 ≤ y)
    (hFx : ∀ t z, 0 ≤ z → 0 ≤ Fx (xs t) (xs (t + 1)) z)
    (hxs : IsFeasiblePlan Γ x₀ xs)
    (heuler : ∀ t, Fy (xs t) (xs (t + 1)) + β • Fx (xs (t + 1)) (xs (t + 2)) = 0)
    (htvc : Tendsto (fun t => β ^ t * Fx (xs t) (xs (t + 1)) (xs t)) atTop (𝓝 0)) :
    IsOptimalPlan Γ F β x₀ xs :=
  euler_transversality_along hβ Fx Fy hconc hΓ hFx hxs heuler htvc

end Euler

section Ramsey

variable (M : RCKModel)

theorem frozen_exists_monotone_policy :
    ∃ g : M.S → M.S, (∀ k, M.toDynProg.policy k = {g k}) ∧ Continuous g ∧ Monotone g :=
  M.exists_monotone_policy

theorem frozen_optimal_capital_converges (k₀ : M.S) :
    ∃ g : M.S → M.S, (∀ k, M.toDynProg.policy k = {g k}) ∧ Continuous g ∧ Monotone g ∧
      M.toDynProg.payoff (planOf g k₀) = M.toDynProg.value k₀ ∧
      (∀ x, IsFeasiblePlan M.toDynProg.Γ k₀ x →
        (M.toDynProg.payoff x = M.toDynProg.value k₀ ↔ x = planOf g k₀)) ∧
      (Monotone (planOf g k₀) ∨ Antitone (planOf g k₀)) ∧
      ∃ kinf : M.S, g kinf = kinf ∧ Tendsto (planOf g k₀) atTop (𝓝 kinf) :=
  M.optimal_capital_converges k₀

theorem frozen_modified_golden_rule {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k})
    {k : M.S} (hfix : g k = k) (hk0 : 0 < (k : ℝ))
    (hc : (k : ℝ) < M.f k) {u' f' : ℝ} (hu : HasDerivAt M.u u' (M.f k - k))
    (hf : HasDerivAt M.f f' k) : M.β * f' = 1 :=
  M.modified_golden_rule hg hfix hk0 hc hu hf

theorem frozen_steady_state_of_modified_golden_rule {g : M.S → M.S}
    (hg : ∀ k, M.toDynProg.policy k = {g k}) {k : M.S} (hc : (k : ℝ) < M.f k)
    {u' f' : ℝ} (hu : HasDerivAt M.u u' (M.f k - k)) (hf : HasDerivAt M.f f' k)
    (hmgr : M.β * f' = 1) : g k = k :=
  M.steady_state_of_modified_golden_rule hg hc hu hf hmgr

theorem frozen_modified_golden_rule_unique {k₁ k₂ f₁ f₂ : ℝ} (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂)
    (hd₁ : HasDerivAt M.f f₁ k₁) (hd₂ : HasDerivAt M.f f₂ k₂)
    (he₁ : M.β * f₁ = 1) (he₂ : M.β * f₂ = 1) : k₁ = k₂ :=
  M.modified_golden_rule_unique h₁ h₂ hd₁ hd₂ he₁ he₂

end Ramsey

section Stochastic

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] [DiscreteTopology Z]
  [Fintype Z] (P : StochDynProg X Z)

theorem frozen_stoch_contracting : ContractingWith ⟨P.β, P.β_pos.le⟩ P.bellmanOp :=
  P.contracting

theorem frozen_stoch_bellman_equation (s : X × Z) :
    IsGreatest ((fun y => P.F s y + P.β * ∑ z', P.Q s.2 z' * P.value (y, z')) '' P.Γ s)
      (P.value s) :=
  P.bellman_equation s

theorem frozen_stoch_value_unique (w : X × Z →ᵇ ℝ)
    (hw : ∀ s, IsGreatest ((fun y => P.F s y + P.β * ∑ z', P.Q s.2 z' * w (y, z')) '' P.Γ s)
      (w s)) : w = P.value :=
  P.value_unique w hw

theorem frozen_stoch_iterate_converges (v₀ : X × Z →ᵇ ℝ) :
    Tendsto (fun n => P.bellmanOp^[n] v₀) atTop (𝓝 P.value) ∧
      ∀ n, dist (P.bellmanOp^[n] v₀) P.value ≤ dist v₀ (P.bellmanOp v₀) * P.β ^ n / (1 - P.β) :=
  P.iterate_converges v₀

theorem frozen_stoch_policy :
    (∀ s, (P.policy s).Nonempty ∧ IsCompact (P.policy s)) ∧ UpperHemicontinuous P.policy :=
  P.policy_nonempty_compact_uhc

end Stochastic

section Markov

variable {Z : Type*} [Fintype Z]

theorem frozen_exists_invariant [Nonempty Z] {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) :
    ∃ π, IsInvariant Q π :=
  exists_invariant hQ

theorem frozen_doeblin [Nonempty Z] [DecidableEq Z] {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ z z', ε ≤ Q z z') :
    ∃ π, IsInvariant Q π ∧ (∀ π', IsInvariant Q π' → π' = π) ∧ ∀ μ ∈ Distributions Z, ∀ n : ℕ,
      l1Dist (μ ᵥ* (Q ^ n)) π ≤ 2 * (1 - Fintype.card Z * ε) ^ n :=
  doeblin hQ hε0 hε

end Markov

end Econ.Audit
