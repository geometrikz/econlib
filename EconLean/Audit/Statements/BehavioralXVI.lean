/-
# Frozen statements: behavioral round 16

Headline statements of `BoundedRationality/KMRDarwin.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-16.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.KMRDarwin

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXVI

section KMRDarwin
open Econ.StochasticStability Finset Filter Topology Matrix
variable {Z : Type*} [Fintype Z] [DecidableEq Z]

theorem frozen_flux_cut {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) {μ : Z → ℝ} (hμ : IsInvariant Q μ)
    (S : Finset Z) :
    ∑ x ∈ S, ∑ y ∈ Sᶜ, μ x * Q x y = ∑ y ∈ Sᶜ, ∑ x ∈ S, μ y * Q y x := by
  first
  | exact @Econ.StochasticStability.flux_cut ..
  | (apply @Econ.StochasticStability.flux_cut <;> assumption)

end KMRDarwin

section KMRDarwin
open Econ.StochasticStability Coord Finset Filter Topology Matrix
variable (G : Coord)

theorem frozen_darwin_isStochastic (N : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsStochastic (G.darwin N ε) := by
  first
  | exact @Econ.StochasticStability.Coord.darwin_isStochastic ..
  | (apply @Econ.StochasticStability.Coord.darwin_isStochastic <;> assumption)

theorem frozen_darwin_exists_invariant (N : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ μ, IsInvariant (G.darwin N ε) μ := by
  first
  | exact @Econ.StochasticStability.Coord.darwin_exists_invariant ..
  | (apply @Econ.StochasticStability.Coord.darwin_exists_invariant <;> assumption)

theorem frozen_darwin_last_ge {N : ℕ} (hN : 0 < N) (hm : 2 * G.resistB N ≤ N) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1) {μ : Fin (N + 1) → ℝ} (hμ : IsInvariant (G.darwin N ε) μ) :
    (1 - ε) ^ N - 2 ^ N * ε ^ (N + 1 - 2 * G.resistB N) ≤ μ (Fin.last N) := by
  first
  | exact @Econ.StochasticStability.Coord.darwin_last_ge ..
  | (apply @Econ.StochasticStability.Coord.darwin_last_ge <;> assumption)

theorem frozen_darwin_selects (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → Fin (N + 1) → ℝ,
      (∀ ε, 0 < ε → ε < 1 → IsInvariant (G.darwin N ε) (μ ε)) →
      Tendsto (fun ε => μ ε (Fin.last N)) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.Coord.darwin_selects ..
  | (apply @Econ.StochasticStability.Coord.darwin_selects <;> assumption)

theorem frozen_darwin_tendsto_zero (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → Fin (N + 1) → ℝ,
      (∀ ε, 0 < ε → ε < 1 → IsInvariant (G.darwin N ε) (μ ε)) →
      ∀ z ≠ Fin.last N, Tendsto (fun ε => μ ε z) (𝓝[>] 0) (𝓝 0) := by
  first
  | exact @Econ.StochasticStability.Coord.darwin_tendsto_zero ..
  | (apply @Econ.StochasticStability.Coord.darwin_tendsto_zero <;> assumption)

end KMRDarwin

section KMRDarwin
open Econ.StochasticStability Coord Finset Filter Topology Matrix


theorem frozen_stagHunt_darwin : ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → Fin (N + 1) → ℝ,
    (∀ ε, 0 < ε → ε < 1 → IsInvariant (stagHunt.darwin N ε) (μ ε)) →
    Tendsto (fun ε => μ ε (Fin.last N)) (𝓝[>] 0) (𝓝 1) := by
  first
  | exact @Econ.StochasticStability.stagHunt_darwin ..
  | (apply @Econ.StochasticStability.stagHunt_darwin <;> assumption)

end KMRDarwin

end Econ.Audit.BehavioralXVI
