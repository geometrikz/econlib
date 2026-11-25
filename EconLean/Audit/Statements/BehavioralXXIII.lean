/-
# Frozen statements: behavioral round 23

Headline statements of `Behavioral/RDURiskAttitude.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-23.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.RDURiskAttitude

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXIII

section RDURiskAttitude
open Econ.RankDependent Finset Filter Topology


theorem frozen_G_binLot (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : G (binLot t ht0 ht1) 1 = t := by
  first
  | exact @Econ.RankDependent.G_binLot ..
  | (apply @Econ.RankDependent.G_binLot <;> assumption)

theorem frozen_rdu_binLot {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) (u : ℕ → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rdu w u (binLot t ht0 ht1) = u 0 + w t * (u 1 - u 0) := by
  first
  | exact @Econ.RankDependent.rdu_binLot ..
  | (apply @Econ.RankDependent.rdu_binLot <;> assumption)

theorem frozen_eu_binLot (u : ℕ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eu u (binLot t ht0 ht1) = u 0 + t * (u 1 - u 0) := by
  first
  | exact @Econ.RankDependent.eu_binLot ..
  | (apply @Econ.RankDependent.eu_binLot <;> assumption)

theorem frozen_rdu_le_eu_iff {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≤ t) ↔
      ∀ (n : ℕ) (u : ℕ → ℝ), MonotoneOnGrid n u → ∀ p : Lottery n, rdu w u p ≤ eu u p := by
  first
  | exact @Econ.RankDependent.rdu_le_eu_iff ..
  | (apply @Econ.RankDependent.rdu_le_eu_iff <;> assumption)

theorem frozen_eu_le_rdu_iff {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, t ≤ w t) ↔
      ∀ (n : ℕ) (u : ℕ → ℝ), MonotoneOnGrid n u → ∀ p : Lottery n, eu u p ≤ rdu w u p := by
  first
  | exact @Econ.RankDependent.eu_le_rdu_iff ..
  | (apply @Econ.RankDependent.eu_le_rdu_iff <;> assumption)

theorem frozen_rdu_le_u_mean {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hpess : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≤ t) {n : ℕ} {x : ℕ → ℝ} {U : ℝ → ℝ}
    (hU : ConcaveOn ℝ Set.univ U) (hUx : MonotoneOnGrid n (U ∘ x)) (p : Lottery n) :
    rdu w (U ∘ x) p ≤ U (eu x p) := by
  first
  | exact @Econ.RankDependent.rdu_le_u_mean ..
  | (apply @Econ.RankDependent.rdu_le_u_mean <;> assumption)

theorem frozen_pessimism_of_riskAverse {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) {U : ℝ → ℝ}
    {x₀ d : ℝ} (hd : HasDerivAt U d x₀) (hdpos : 0 < d)
    (hRA : ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1), ∃ ε > 0, ∀ h, 0 < h → h < ε →
      rdu w (fun k : ℕ => U (x₀ + k * h)) (binLot t ht0 ht1) ≤
        U (eu (fun k : ℕ => x₀ + k * h) (binLot t ht0 ht1))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≤ t := by
  first
  | exact @Econ.RankDependent.pessimism_of_riskAverse ..
  | (apply @Econ.RankDependent.pessimism_of_riskAverse <;> assumption)

theorem frozen_sq_pessimistic : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ^ 2 ≤ t := by
  first
  | exact @Econ.RankDependent.sq_pessimistic ..
  | (apply @Econ.RankDependent.sq_pessimistic <;> assumption)

theorem frozen_rdu_sq_le_eu {n : ℕ} {u : ℕ → ℝ} (hu : MonotoneOnGrid n u) (p : Lottery n) :
    rdu (fun t => t ^ 2) u p ≤ eu u p := by
  first
  | exact @Econ.RankDependent.rdu_sq_le_eu ..
  | (apply @Econ.RankDependent.rdu_sq_le_eu <;> assumption)

theorem frozen_yaari_riskSeeking {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hover : t < w t) :
    eu (fun k : ℕ => (k : ℝ)) (binLot t ht0 ht1) < rdu w (fun k : ℕ => (k : ℝ)) (binLot t ht0 ht1) := by
  first
  | exact @Econ.RankDependent.yaari_riskSeeking ..
  | (apply @Econ.RankDependent.yaari_riskSeeking <;> assumption)

end RDURiskAttitude

end Econ.Audit.BehavioralXXIII
