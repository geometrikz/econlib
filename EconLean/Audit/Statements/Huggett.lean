/-
# Frozen statements: Huggett's endowment economy

Headline statements of `Macro/HA/Huggett.lean` (and the generalized market-
clearing theorem in `Macro/HA/Aiyagari.lean`). Copied verbatim after the
context-isolated adversarial review (record in `Audit/REVIEW-huggett.md`).
Each statement is closed by the library theorem, so this file stops compiling
if a library statement is ever weakened.
-/
module

public import EconLean.Macro.HA.Huggett

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ MeasureTheory ProbabilityTheory

theorem frozen_exists_asset_market_clearing_of_supply {Z : Type*} [Fintype Z]
    [TopologicalSpace Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]
    {rlo rhi : ℝ} (hr : rlo ≤ rhi) (M : ParamSavings (Icc rlo rhi) Z)
    (Kd : ℝ → ℝ) (hKd : ContinuousOn Kd (Icc rlo rhi))
    (hlo : ∀ (g : M.S × Z → M.S) (hg : Measurable g),
      (∀ s, (M.slice ⟨rlo, le_rfl, hr⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (M.S × Z), Kernel.Invariant (policyKernel M.Q g hg) μ ∧
        ∫ s, M.assets s ∂(μ : Measure (M.S × Z)) ≤ Kd rlo)
    (hhi : ∀ (g : M.S × Z → M.S) (hg : Measurable g),
      (∀ s, (M.slice ⟨rhi, hr, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (M.S × Z), Kernel.Invariant (policyKernel M.Q g hg) μ ∧
        Kd rhi ≤ ∫ s, M.assets s ∂(μ : Measure (M.S × Z))) :
    ∃ r : Icc rlo rhi, ∃ (g : M.S × Z → M.S) (hg : Measurable g) (π : ProbabilityMeasure (M.S × Z)),
      (∀ s, (M.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel M.Q g hg) π ∧
      ∫ s, M.assets s ∂(π : Measure (M.S × Z)) = Kd r :=
  M.exists_asset_market_clearing_of_supply hr Kd hKd hlo hhi

section Household

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] {M : StochSavings Z}

theorem frozen_le_policy_at {g : M.S × Z → M.S} (hg : ∀ s, M.toStochDynProg.policy s = {g s})
    (s : M.S × Z) (m : M.S) (hm : (m : ℝ) ≤ M.h s.1 s.2)
    (hmono : ∀ z' (a b : M.S), (a : ℝ) ≤ b → M.h a z' ≤ M.h b z')
    (hgain : ∀ (y : M.S) (x : Z → M.S), (y : ℝ) < m → (∀ z', (x z' : ℝ) ≤ M.h y z') →
      M.u (M.h s.1 s.2 - y) - M.u (M.h s.1 s.2 - m) <
        M.β * ∑ z', M.Q s.2 z' * (M.u (M.h m z' - x z') - M.u (M.h y z' - x z'))) :
    (m : ℝ) ≤ g s :=
  StochSavings.le_policy_at hg s m hm hmono hgain

end Household

section Huggett

variable {Z : Type*} [Fintype Z] (E : HuggettEconomy Z) [TopologicalSpace Z] [DiscreteTopology Z]

theorem frozen_huggett_policy_lo {g : E.household.S × Z → E.household.S}
    (hg : ∀ s, (E.household.slice E.lo).toStochDynProg.policy s = {g s})
    (s : E.household.S × Z) : (g s : ℝ) = 0 :=
  E.policy_lo hg s

theorem frozen_huggett_supply_ge_of_save [MeasurableSpace Z] [BorelSpace Z] [DecidableEq Z]
    (g : E.household.S × Z → E.household.S)
    (hg : Measurable g) (zh : Z) (m : ℝ) (hsave : ∀ b, m ≤ g (b, zh))
    (μ : ProbabilityMeasure (E.household.S × Z))
    (hμ : Kernel.Invariant (policyKernel E.household.Q g hg) μ) :
    m * E.qbar zh ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)) :=
  E.supply_ge_of_save g hg zh m hsave μ hμ

theorem frozen_huggett_exists_equilibrium [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice E.hi).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z),
        Kernel.Invariant (policyKernel E.household.Q g hg) μ ∧
        E.φ ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z))) :
    ∃ r : Icc (-1 : ℝ) E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.household.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.φ ∧ -1 < (r : ℝ) :=
  E.exists_stationary_equilibrium hhi

theorem frozen_huggett_exists_equilibrium_slack [MeasurableSpace Z] [BorelSpace Z]
    [Nonempty Z]
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice E.hi).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z),
        Kernel.Invariant (policyKernel E.household.Q g hg) μ ∧
        E.φ ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)))
    (hrhi : E.rhi < 0) {ybar : ℝ} (hyb : ∀ z, E.y z ≤ ybar)
    (hAk : (ybar + E.φ) / (-E.rhi) < E.kbar) :
    ∃ r : Icc (-1 : ℝ) E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.household.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.φ ∧
      (∀ s, (g s : ℝ) < E.kbar) ∧
      (π : Measure (E.household.S × Z)) {s | (ybar + E.φ) / (-E.rhi) < (s.1 : ℝ)} = 0 ∧
      -1 < (r : ℝ) ∧ (r : ℝ) < 0 :=
  E.exists_stationary_equilibrium_slack hhi hrhi hyb hAk

end Huggett

theorem frozen_huggett_equilibrium :
    ∃ r : Icc (-1 : ℝ) HuggettEconomy.huggettExample.rhi,
    ∃ (g : HuggettEconomy.huggettExample.household.S × Fin 2 →
        HuggettEconomy.huggettExample.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (HuggettEconomy.huggettExample.household.S × Fin 2)),
      (∀ s, (HuggettEconomy.huggettExample.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel HuggettEconomy.huggettExample.household.Q g hg) π ∧
      ∫ s, HuggettEconomy.huggettExample.household.assets s
        ∂(π : Measure (HuggettEconomy.huggettExample.household.S × Fin 2)) = 1 / 10 ∧
      (∀ s, (g s : ℝ) < 25) ∧
      (π : Measure (HuggettEconomy.huggettExample.household.S × Fin 2)) {s | (21 : ℝ) < s.1} = 0 ∧
      -1 < (r : ℝ) ∧ (r : ℝ) < 0 :=
  HuggettEconomy.huggett_equilibrium

end Econ.Audit
