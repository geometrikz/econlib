/-
# Frozen statements: Aiyagari equilibrium with a non-binding cap

Headline statements of `Macro/HA/AiyagariSlack.lean`, copied verbatim after the
context-isolated adversarial review (record in `Audit/REVIEW-aiyagari-slack.md`).
Each statement is closed by the library theorem, so this file stops compiling
if a library statement is ever weakened.
-/
module

public import EconLean.Macro.HA.AiyagariSlack

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ MeasureTheory ProbabilityTheory

theorem frozen_wage_eq_mul_kOfR (F : CDFirm) {r : ℝ} (hr : -F.δ < r) :
    F.wage r = (1 - F.α) * (r + F.δ) / F.α * F.kOfR r :=
  F.wage_eq_mul_kOfR hr

theorem frozen_wage_anti (F : CDFirm) {r r' : ℝ} (hr : -F.δ < r) (hrr : r ≤ r') : F.wage r' ≤ F.wage r :=
  F.wage_anti hr hrr

section Economy

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] (E : AiyagariEconomy Z)

theorem frozen_aiyagari_policy_le_max (hrhi : E.rhi < 0) {ebar : ℝ} (heb : ∀ z, E.e z ≤ ebar)
    (r : Icc E.rlo E.rhi) {g : E.household.S × Z → E.household.S}
    (hg : ∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) (s : E.household.S × Z) :
    (g s : ℝ) ≤ max (E.firm.wage E.rlo * ebar / (-E.rhi)) s.1 ∧
      (E.firm.wage E.rlo * ebar / (-E.rhi) < s.1 → (g s : ℝ) < s.1) :=
  E.policy_le_max hrhi heb r hg s

variable [MeasurableSpace Z] [BorelSpace Z]

theorem frozen_aiyagari_supply_ge_of_save [DecidableEq Z] (g : E.household.S × Z → E.household.S)
    (hg : Measurable g) (zh : Z) (m : ℝ) (hsave : ∀ a, m ≤ g (a, zh))
    (μ : ProbabilityMeasure (E.household.S × Z))
    (hμ : Kernel.Invariant (policyKernel E.household.Q g hg) μ) :
    m * E.qbar zh ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)) :=
  E.supply_ge_of_save g hg zh m hsave μ hμ

theorem frozen_aiyagari_exists_equilibrium_slack [Nonempty Z] [DecidableEq Z]
    (hlo : E.kbar ≤ E.firm.capDemand E.L E.rlo)
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z), Kernel.Invariant (policyKernel E.Q g hg) μ ∧
        E.firm.capDemand E.L E.rhi ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)))
    (hrhi : E.rhi < 0) {ebar : ℝ} (heb : ∀ z, E.e z ≤ ebar)
    (hAk : E.firm.wage E.rlo * ebar / (-E.rhi) < E.kbar) :
    ∃ r : Icc E.rlo E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.firm.capDemand E.L r ∧
      ∫ s, E.e s.2 ∂(π : Measure (E.household.S × Z)) = E.L ∧
      E.firm.α * ((∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) / E.L) ^
        (E.firm.α - 1) = r + E.firm.δ ∧
      E.firm.wage r = (1 - E.firm.α) *
        ((∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) / E.L) ^ E.firm.α ∧
      ∫ s, ((1 + (r : ℝ)) * (s.1 : ℝ) + E.firm.wage r * E.e s.2 - (g s : ℝ))
          ∂(π : Measure (E.household.S × Z)) +
        E.firm.δ * ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) =
        E.firm.output (∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) E.L ∧
      (∀ s, (g s : ℝ) < E.kbar) ∧
      (π : Measure (E.household.S × Z))
        {s | E.firm.wage E.rlo * ebar / (-E.rhi) < (s.1 : ℝ)} = 0 ∧
      -E.firm.δ < (r : ℝ) ∧ (r : ℝ) < 0 :=
  E.exists_stationary_equilibrium_slack hlo hhi hrhi heb hAk

end Economy

open AiyagariEconomy in
theorem frozen_slack_saving
    (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S)
    (hg : ∀ s, (slackEconomy.household.slice ⟨slackEconomy.rhi, slackEconomy.rlo_le, le_rfl⟩
      ).toStochDynProg.policy s = {g s})
    (a : slackEconomy.household.S) : CDFirm.tenth.kOfR (-1 / 20) ≤ g (a, 1) :=
  slack_saving g hg a

open AiyagariEconomy in
theorem frozen_slack_equilibrium :
    ∃ r : Icc slackEconomy.rlo slackEconomy.rhi,
    ∃ (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (slackEconomy.household.S × Fin 2)),
      (∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel slackEconomy.Q g hg) π ∧
      ∫ s, slackEconomy.household.assets s ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.firm.capDemand slackEconomy.L r ∧
      ∫ s, slackEconomy.e s.2 ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.L ∧
      slackEconomy.firm.α * ((∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2))) / slackEconomy.L) ^
        (slackEconomy.firm.α - 1) = r + slackEconomy.firm.δ ∧
      slackEconomy.firm.wage r = (1 - slackEconomy.firm.α) *
        ((∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2))) / slackEconomy.L) ^
            slackEconomy.firm.α ∧
      ∫ s, ((1 + (r : ℝ)) * (s.1 : ℝ) + slackEconomy.firm.wage r * slackEconomy.e s.2 -
          (g s : ℝ)) ∂(π : Measure (slackEconomy.household.S × Fin 2)) +
        slackEconomy.firm.δ * ∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.firm.output (∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2))) slackEconomy.L ∧
      0 < ∫ s, slackEconomy.household.assets s ∂(π : Measure (slackEconomy.household.S × Fin 2)) ∧
      (∀ s, (g s : ℝ) < slackEconomy.kbar) ∧
      (π : Measure (slackEconomy.household.S × Fin 2))
        {s | 9 / 10 * slackEconomy.kbar < (s.1 : ℝ)} = 0 ∧
      -slackEconomy.firm.δ < (r : ℝ) ∧ (r : ℝ) < 0 :=
  slack_equilibrium

end Econ.Audit
