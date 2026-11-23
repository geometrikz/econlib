/-
# Frozen statements: behavioral round 11

Headline statements of `BoundedRationality/KMRChain.lean`,
`BoundedRationality/BayesianLearning.lean` and
`Behavioral/VariationalPreferences.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-11.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.KMRChain
public import EconLean.BoundedRationality.BayesianLearning
public import EconLean.Behavioral.VariationalPreferences

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXI

section KMRChain
open Econ.StochasticStability Econ.StochasticStability.BirthDeath Finset Filter Topology
variable {up down : ℕ → ℝ} {N : ℕ}

theorem frozen_sum_P {z : ℕ} (hz : z ≤ N) : ∑ z' ∈ range (N + 1), P up down N z z' = 1 := by
  first
  | exact @Econ.StochasticStability.BirthDeath.sum_P ..
  | (apply @Econ.StochasticStability.BirthDeath.sum_P <;> assumption)

theorem frozen_P_nonneg (hup : ∀ z ≤ N, 0 ≤ up z) (hdown : ∀ z ≤ N, 0 ≤ down z)
    (hsum : ∀ z ≤ N, up z + down z ≤ 1) {z : ℕ} (hz : z ≤ N) (z' : ℕ) :
    0 ≤ P up down N z z' := by
  first
  | exact @Econ.StochasticStability.BirthDeath.P_nonneg ..
  | (apply @Econ.StochasticStability.BirthDeath.P_nonneg <;> assumption)

theorem frozen_pi_detailedBalance {z : ℕ} (hd : down (z + 1) ≠ 0) :
    pi up down N z * up z = pi up down N (z + 1) * down (z + 1) := by
  first
  | exact @Econ.StochasticStability.BirthDeath.pi_detailedBalance ..
  | (apply @Econ.StochasticStability.BirthDeath.pi_detailedBalance <;> assumption)

theorem frozen_pi_isStationaryDist (hup : ∀ z < N, 0 ≤ up z)
    (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z) : IsStationaryDist up down N (pi up down N) := by
  first
  | exact @Econ.StochasticStability.BirthDeath.pi_isStationaryDist ..
  | (apply @Econ.StochasticStability.BirthDeath.pi_isStationaryDist <;> assumption)

theorem frozen_flux_balance {μ : ℕ → ℝ} (hμ : IsStationaryDist up down N μ) :
    ∀ z < N, μ (z + 1) * down (z + 1) = μ z * up z := by
  first
  | exact @Econ.StochasticStability.BirthDeath.flux_balance ..
  | (apply @Econ.StochasticStability.BirthDeath.flux_balance <;> assumption)

theorem frozen_eq_pi (hup : ∀ z < N, 0 ≤ up z) (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z)
    {μ : ℕ → ℝ} (hμ : IsStationaryDist up down N μ) : ∀ z ≤ N, μ z = pi up down N z := by
  first
  | exact @Econ.StochasticStability.BirthDeath.eq_pi ..
  | (apply @Econ.StochasticStability.BirthDeath.eq_pi <;> assumption)

end KMRChain

section KMRChain
open Econ.StochasticStability Econ.StochasticStability.Coord Finset Filter Topology
variable (G : Econ.StochasticStability.Coord)

theorem frozen_kmr_P_nonneg {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℕ} (hz : z ≤ N)
    (z' : ℕ) : 0 ≤ BirthDeath.P (G.kup N ε) (G.kdown N ε) N z z' := by
  first
  | exact @Econ.StochasticStability.Coord.kmr_P_nonneg ..
  | (apply @Econ.StochasticStability.Coord.kmr_P_nonneg <;> assumption)

theorem frozen_kmr_isStationaryDist {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    BirthDeath.IsStationaryDist (G.kup N ε) (G.kdown N ε) N
      (BirthDeath.pi (G.kup N ε) (G.kdown N ε) N) := by
  first
  | exact @Econ.StochasticStability.Coord.kmr_isStationaryDist ..
  | (apply @Econ.StochasticStability.Coord.kmr_isStationaryDist <;> assumption)

theorem frozen_kmr_selects_riskDominant (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → ℕ → ℝ,
      (∀ ε, 0 < ε → ε ≤ 1 → BirthDeath.IsStationaryDist (G.kup N ε) (G.kdown N ε) N (μ ε)) →
      Tendsto (fun ε => μ ε N) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.Coord.kmr_selects_riskDominant ..
  | (apply @Econ.StochasticStability.Coord.kmr_selects_riskDominant <;> assumption)

theorem frozen_kmr_tendsto_zero (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → ℕ → ℝ,
      (∀ ε, 0 < ε → ε ≤ 1 → BirthDeath.IsStationaryDist (G.kup N ε) (G.kdown N ε) N (μ ε)) →
      ∀ z < N, Tendsto (fun ε => μ ε z) (𝓝[>] 0) (𝓝 0) := by
  first
  | exact @Econ.StochasticStability.Coord.kmr_tendsto_zero ..
  | (apply @Econ.StochasticStability.Coord.kmr_tendsto_zero <;> assumption)

end KMRChain

section KMRChain
open Econ.StochasticStability Finset Filter Topology


theorem frozen_stagHunt_kmr : ∀ᶠ N : ℕ in atTop,
    Tendsto (fun ε => BirthDeath.pi (stagHunt.kup N ε) (stagHunt.kdown N ε) N N)
      (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.stagHunt_kmr ..
  | (apply @Econ.StochasticStability.stagHunt_kmr <;> assumption)

end KMRChain

section BayesianLearning
open Econ.BayesianLearning Finset Filter Topology Real MeasureTheory ProbabilityTheory Function
variable {Θ O : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype O]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace O] [MeasurableSingletonClass O]

theorem frozen_tendsto_posterior_of_llr {p0 : Θ → ℝ} {q : Θ → O → ℝ} {x : ℕ → O} {θs : Θ}
    (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o)
    (h : ∀ θ, θ ≠ θs → ∃ c < 0,
      Tendsto (fun n : ℕ => (∑ k ∈ range n, llr q θ θs (x k)) / n) atTop (𝓝 c)) :
    ∀ θ, Tendsto (fun n => posterior p0 q x n θ) atTop (𝓝 (if θ = θs then 1 else 0)) := by
  first
  | exact @Econ.BayesianLearning.tendsto_posterior_of_llr ..
  | (apply @Econ.BayesianLearning.tendsto_posterior_of_llr <;> assumption)

theorem frozen_ae_tendsto_llr {X : ℕ → Ω → O} {q : Θ → O → ℝ} {θs : Θ} (hX : IsIID X μ (q θs))
    (hq : ∀ θ o, 0 < q θ o) (θ : Θ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ range n, llr q θ θs (X k ω)) / n) atTop
      (𝓝 (-RationalInattention.kl (q θs) (q θ))) := by
  first
  | exact @Econ.BayesianLearning.ae_tendsto_llr ..
  | (apply @Econ.BayesianLearning.ae_tendsto_llr <;> assumption)

theorem frozen_kl_pos {q : Θ → O → ℝ} (hq : ∀ θ o, 0 < q θ o) (hsum : ∀ θ, ∑ o, q θ o = 1)
    {θ θs : Θ} (hid : q θ ≠ q θs) : 0 < RationalInattention.kl (q θs) (q θ) := by
  first
  | exact @Econ.BayesianLearning.kl_pos ..
  | (apply @Econ.BayesianLearning.kl_pos <;> assumption)

theorem frozen_posterior_consistent {X : ℕ → Ω → O} {p0 : Θ → ℝ} {q : Θ → O → ℝ} {θs : Θ}
    (hX : IsIID X μ (q θs)) (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o)
    (hsum : ∀ θ, ∑ o, q θ o = 1) (hid : ∀ θ, θ ≠ θs → q θ ≠ q θs) :
    ∀ᵐ ω ∂μ, ∀ θ, Tendsto (fun n => posterior p0 q (fun k => X k ω) n θ) atTop
      (𝓝 (if θ = θs then 1 else 0)) := by
  first
  | exact @Econ.BayesianLearning.posterior_consistent ..
  | (apply @Econ.BayesianLearning.posterior_consistent <;> assumption)

theorem frozen_predictive_merges {X : ℕ → Ω → O} {p0 : Θ → ℝ} {q : Θ → O → ℝ} {θs : Θ}
    (hX : IsIID X μ (q θs)) (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o)
    (hsum : ∀ θ, ∑ o, q θ o = 1) (hid : ∀ θ, θ ≠ θs → q θ ≠ q θs) :
    ∀ᵐ ω ∂μ, ∀ o, Tendsto (fun n => predictive p0 q (fun k => X k ω) n o) atTop
      (𝓝 (q θs o)) := by
  first
  | exact @Econ.BayesianLearning.predictive_merges ..
  | (apply @Econ.BayesianLearning.predictive_merges <;> assumption)

end BayesianLearning

section VariationalPreferences
open Econ.Variational Finset
variable {S : Type*} [Fintype S] [DecidableEq S] {I : (S → ℝ) → ℝ}

theorem frozen_exists_supergradient (hI : IsVariationalFunctional I) (f : S → ℝ) :
    ∃ p, Logit.IsProb p ∧ ∀ g, I g - dot p g ≤ I f - dot p f := by
  first
  | exact @Econ.Variational.exists_supergradient ..
  | (apply @Econ.Variational.exists_supergradient <;> assumption)

theorem frozen_le_dot_add_cost {p : S → ℝ} (hp : InDom I p) (f : S → ℝ) :
    I f ≤ dot p f + cost I p := by
  first
  | exact @Econ.Variational.le_dot_add_cost ..
  | (apply @Econ.Variational.le_dot_add_cost <;> assumption)

theorem frozen_exists_eq_dot_add_cost (hI : IsVariationalFunctional I) (f : S → ℝ) :
    ∃ p, Logit.IsProb p ∧ InDom I p ∧ I f = dot p f + cost I p := by
  first
  | exact @Econ.Variational.exists_eq_dot_add_cost ..
  | (apply @Econ.Variational.exists_eq_dot_add_cost <;> assumption)

theorem frozen_cost_nonneg (hI : IsVariationalFunctional I) {p : S → ℝ} (hp : InDom I p) : 0 ≤ cost I p := by
  first
  | exact @Econ.Variational.cost_nonneg ..
  | (apply @Econ.Variational.cost_nonneg <;> assumption)

theorem frozen_exists_cost_eq_zero (hI : IsVariationalFunctional I) :
    ∃ p, Logit.IsProb p ∧ InDom I p ∧ cost I p = 0 := by
  first
  | exact @Econ.Variational.exists_cost_eq_zero ..
  | (apply @Econ.Variational.exists_cost_eq_zero <;> assumption)

theorem frozen_isProb_of_inDom (hI : IsVariationalFunctional I) {p : S → ℝ} (hp : InDom I p) :
    Logit.IsProb p := by
  first
  | exact @Econ.Variational.isProb_of_inDom ..
  | (apply @Econ.Variational.isProb_of_inDom <;> assumption)

theorem frozen_cost_convex : ConvexOn ℝ {p : S → ℝ | InDom I p} (cost I) := by
  first
  | exact @Econ.Variational.cost_convex ..
  | (apply @Econ.Variational.cost_convex <;> assumption)

theorem frozen_cost_expected_self (q : S → ℝ) :
    InDom (fun f => dot q f) q ∧ cost (fun f => dot q f) q = 0 := by
  first
  | exact @Econ.Variational.cost_expected_self ..
  | (apply @Econ.Variational.cost_expected_self <;> assumption)

theorem frozen_expected_inDom_iff (q p : S → ℝ) : InDom (fun f => dot q f) p ↔ p = q := by
  first
  | exact @Econ.Variational.expected_inDom_iff ..
  | (apply @Econ.Variational.expected_inDom_iff <;> assumption)

end VariationalPreferences

end Econ.Audit.BehavioralXI
