/-
# Frozen statements: behavioral round 10

Headline statements of `BoundedRationality/FictitiousPlay.lean` and
`BoundedRationality/StochasticStability.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-10.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.FictitiousPlay
public import EconLean.BoundedRationality.StochasticStability

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralX

section FictitiousPlay
open Econ.FictitiousPlay Function Finset Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

theorem frozen_sum_freq (h : ℕ → ∀ j, S j) {T : ℕ} (hT : 0 < T) (i : I) :
    ∑ a, freq h T i a = 1 := by
  first
  | exact @Econ.FictitiousPlay.sum_freq ..
  | (apply @Econ.FictitiousPlay.sum_freq <;> assumption)

theorem frozen_freq_eq_zero_of_worse_at_limit {u : I → (∀ j, S j) → ℝ} {h : ℕ → ∀ j, S j}
    (hfp : IsFP u h) {σ : ∀ i, S i → ℝ} (hσ : Tendsto (freq h) atTop (𝓝 σ)) {i : I}
    {b t : S i} (hbt : pureDev u σ i b < pureDev u σ i t) : σ i b = 0 := by
  first
  | exact @Econ.FictitiousPlay.freq_eq_zero_of_worse_at_limit ..
  | (apply @Econ.FictitiousPlay.freq_eq_zero_of_worse_at_limit <;> assumption)

theorem frozen_isMixedNash_of_tendsto {u : I → (∀ j, S j) → ℝ} {h : ℕ → ∀ j, S j} (hfp : IsFP u h)
    {σ : ∀ i, S i → ℝ} (hσ : Tendsto (freq h) atTop (𝓝 σ)) : IsMixedNash u σ := by
  first
  | exact @Econ.FictitiousPlay.isMixedNash_of_tendsto ..
  | (apply @Econ.FictitiousPlay.isMixedNash_of_tendsto <;> assumption)

theorem frozen_isFP_const {u : I → (∀ j, S j) → ℝ} {s : ∀ j, S j} (hs : IsNash u s) :
    IsFP u fun _ => s := by
  first
  | exact @Econ.FictitiousPlay.isFP_const ..
  | (apply @Econ.FictitiousPlay.isFP_const <;> assumption)

theorem frozen_tendsto_freq_const (s : ∀ j, S j) :
    Tendsto (freq fun _ => s) atTop (𝓝 (pureProfile s)) := by
  first
  | exact @Econ.FictitiousPlay.tendsto_freq_const ..
  | (apply @Econ.FictitiousPlay.tendsto_freq_const <;> assumption)

end FictitiousPlay

section StochasticStability
open Econ.StochasticStability Filter Topology


theorem frozen_tendsto_weightA_of_bounds {rA rB : ℕ} (h : rB < rA) {pAB pBA : ℝ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c * ε ^ rA ≤ pAB ε ∧ pAB ε ≤ C * ε ^ rA ∧ c * ε ^ rB ≤ pBA ε ∧ pBA ε ≤ C * ε ^ rB) :
    Tendsto (fun ε => pBA ε / (pAB ε + pBA ε)) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.tendsto_weightA_of_bounds ..
  | (apply @Econ.StochasticStability.tendsto_weightA_of_bounds <;> assumption)

theorem frozen_riskDominant_selected_of_bounds (G : Coord) (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ (pAB pBA : ℝ → ℝ) (c C : ℝ), 0 < c →
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε ^ G.resistA N ≤ pAB ε ∧ pAB ε ≤ C * ε ^ G.resistA N ∧
        c * ε ^ G.resistB N ≤ pBA ε ∧ pBA ε ≤ C * ε ^ G.resistB N) →
      Tendsto (fun ε => pBA ε / (pAB ε + pBA ε)) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.riskDominant_selected_of_bounds ..
  | (apply @Econ.StochasticStability.riskDominant_selected_of_bounds <;> assumption)

theorem frozen_stationaryA_balance {rA rB : ℕ} {ε : ℝ} (hε : 0 < ε) :
    stationaryA rA rB ε * ε ^ rA = (1 - stationaryA rA rB ε) * ε ^ rB := by
  first
  | exact @Econ.StochasticStability.stationaryA_balance ..
  | (apply @Econ.StochasticStability.stationaryA_balance <;> assumption)

theorem frozen_tendsto_stationaryA {rA rB : ℕ} (h : rB < rA) :
    Tendsto (stationaryA rA rB) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.tendsto_stationaryA ..
  | (apply @Econ.StochasticStability.tendsto_stationaryA <;> assumption)

theorem frozen_riskDominant_selected_twoState (G : Coord) (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop,
      Tendsto (stationaryA (G.resistA N) (G.resistB N)) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.riskDominant_selected_twoState ..
  | (apply @Econ.StochasticStability.riskDominant_selected_twoState <;> assumption)

theorem frozen_stagHunt_selected : ∀ᶠ N : ℕ in atTop,
    Tendsto (stationaryA (stagHunt.resistA N) (stagHunt.resistB N)) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.stagHunt_selected ..
  | (apply @Econ.StochasticStability.stagHunt_selected <;> assumption)

end StochasticStability

section StochasticStability
open Econ.StochasticStability Econ.StochasticStability.Coord Filter Topology
variable (G : Econ.StochasticStability.Coord)

theorem frozen_bestA_iff (x : ℝ) : G.payB x ≤ G.payA x ↔ G.pstar ≤ x := by
  first
  | exact @Econ.StochasticStability.Coord.bestA_iff ..
  | (apply @Econ.StochasticStability.Coord.bestA_iff <;> assumption)

theorem frozen_bestB_iff (x : ℝ) : G.payA x ≤ G.payB x ↔ x ≤ G.pstar := by
  first
  | exact @Econ.StochasticStability.Coord.bestB_iff ..
  | (apply @Econ.StochasticStability.Coord.bestB_iff <;> assumption)

theorem frozen_riskDominant_iff : G.RiskDominant ↔ G.pstar < 1 / 2 := by
  first
  | exact @Econ.StochasticStability.Coord.riskDominant_iff ..
  | (apply @Econ.StochasticStability.Coord.riskDominant_iff <;> assumption)

theorem frozen_resistB_spec {N : ℕ} (hN : 0 < N) :
    G.payB (G.resistB N / N) ≤ G.payA (G.resistB N / N) ∧
      ∀ m : ℕ, m < G.resistB N → G.payA (m / N) < G.payB (m / N) := by
  first
  | exact @Econ.StochasticStability.Coord.resistB_spec ..
  | (apply @Econ.StochasticStability.Coord.resistB_spec <;> assumption)

theorem frozen_resistA_spec {N : ℕ} (hN : 0 < N) :
    G.payA ((N - G.resistA N : ℝ) / N) ≤ G.payB ((N - G.resistA N : ℝ) / N) ∧
      ∀ m : ℕ, m < G.resistA N → G.payB ((N - m : ℝ) / N) < G.payA ((N - m : ℝ) / N) := by
  first
  | exact @Econ.StochasticStability.Coord.resistA_spec ..
  | (apply @Econ.StochasticStability.Coord.resistA_spec <;> assumption)

theorem frozen_resistB_lt_resistA (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, G.resistB N < G.resistA N := by
  first
  | exact @Econ.StochasticStability.Coord.resistB_lt_resistA ..
  | (apply @Econ.StochasticStability.Coord.resistB_lt_resistA <;> assumption)

end StochasticStability

end Econ.Audit.BehavioralX
