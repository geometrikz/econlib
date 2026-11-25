/-
# Frozen statements: behavioral round 27

Headline statements of `Behavioral/RDUNecessity.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-27.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.RDUNecessity

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXVII

section RDUNecessity
open Econ.RankDependent Finset Filter Topology


variable {n : ℕ}

theorem frozen_tendsto_slope_ray {U : ℝ → ℝ} {d x₀ : ℝ} (hd : HasDerivAt U d x₀) (c : ℝ) :
    Tendsto (fun h => h⁻¹ * (U (x₀ + h * c) - U x₀)) (𝓝[>] 0) (𝓝 (c * d)) := by
  first
  | exact @Econ.RankDependent.tendsto_slope_ray ..
  | (apply @Econ.RankDependent.tendsto_slope_ray <;> assumption)

theorem frozen_isMPS_affine {y : ℕ → ℝ} {p q : Lottery n} (h : IsMPS y q p) (c : ℝ) {a : ℝ}
    (ha : 0 ≤ a) : IsMPS (fun k => c + a * y k) q p := by
  first
  | exact @Econ.RankDependent.isMPS_affine ..
  | (apply @Econ.RankDependent.isMPS_affine <;> assumption)

theorem frozen_convex_of_stronglyRiskAverse {w U : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hS : StronglyRiskAverse w U) {x₀ d : ℝ} (hd : HasDerivAt U d x₀) (hdpos : 0 < d) :
    ConvexOn ℝ (Set.Icc 0 1) w := by
  first
  | exact @Econ.RankDependent.convex_of_stronglyRiskAverse ..
  | (apply @Econ.RankDependent.convex_of_stronglyRiskAverse <;> assumption)

theorem frozen_G_baseLot (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) :
    G (baseLot s δ hs hδ h) 1 = s + δ ∧ G (baseLot s δ hs hδ h) 2 = s ∧
      G (baseLot s δ hs hδ h) 3 = s := by
  first
  | exact @Econ.RankDependent.G_baseLot ..
  | (apply @Econ.RankDependent.G_baseLot <;> assumption)

theorem frozen_G_spreadLot (s δ l : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    G (spreadLot s δ l hs hδ h hl0 hl1) 1 = s + δ * l ∧
      G (spreadLot s δ l hs hδ h hl0 hl1) 2 = s + δ * l ∧
      G (spreadLot s δ l hs hδ h hl0 hl1) 3 = s := by
  first
  | exact @Econ.RankDependent.G_spreadLot ..
  | (apply @Econ.RankDependent.G_spreadLot <;> assumption)

theorem frozen_isMPS_spread (s δ l : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    IsMPS (fun k : ℕ => if k = 0 then a else if k = 1 then (1 - l) * a + l * b else
        if k = 2 then b else b + 1)
      (spreadLot s δ l hs hδ h hl0 hl1) (baseLot s δ hs hδ h) := by
  first
  | exact @Econ.RankDependent.isMPS_spread ..
  | (apply @Econ.RankDependent.isMPS_spread <;> assumption)

theorem frozen_concave_of_stronglyRiskAverse {w U : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hS : StronglyRiskAverse w U) {s e : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (he : HasDerivAt w e s)
    (hepos : 0 < e) : ConcaveOn ℝ Set.univ U := by
  first
  | exact Econ.RankDependent.concave_of_stronglyRiskAverse hw0 hw1 hS hs0 hs1 he hepos
  | (apply @Econ.RankDependent.concave_of_stronglyRiskAverse <;> assumption)

theorem frozen_cks_iff {w U : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hwm : MonotoneOn w (Set.Icc 0 1)) {s e : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (he : HasDerivAt w e s) (hepos : 0 < e) (hUm : Monotone U) {x₀ d : ℝ}
    (hd : HasDerivAt U d x₀) (hdpos : 0 < d) :
    StronglyRiskAverse w U ↔ ConvexOn ℝ (Set.Icc 0 1) w ∧ ConcaveOn ℝ Set.univ U := by
  first
  | exact Econ.RankDependent.cks_iff hw0 hw1 hwm hs0 hs1 he hepos hUm hd hdpos
  | (apply @Econ.RankDependent.cks_iff <;> assumption)

theorem frozen_hasDerivAt_sq_half : HasDerivAt (fun t : ℝ => t ^ 2) 1 (1 / 2) := by
  first
  | exact @Econ.RankDependent.hasDerivAt_sq_half ..
  | (apply @Econ.RankDependent.hasDerivAt_sq_half <;> assumption)

theorem frozen_exp_not_stronglyRiskAverse : ¬ StronglyRiskAverse (fun t : ℝ => t ^ 2) Real.exp := by
  first
  | exact @Econ.RankDependent.exp_not_stronglyRiskAverse ..
  | (apply @Econ.RankDependent.exp_not_stronglyRiskAverse <;> assumption)

theorem frozen_concaveW_not_stronglyRiskAverse :
    ¬ StronglyRiskAverse (fun t : ℝ => 2 * t - t ^ 2) id := by
  first
  | exact @Econ.RankDependent.concaveW_not_stronglyRiskAverse ..
  | (apply @Econ.RankDependent.concaveW_not_stronglyRiskAverse <;> assumption)

theorem frozen_sq_id_stronglyRiskAverse : StronglyRiskAverse (fun t : ℝ => t ^ 2) id := by
  first
  | exact @Econ.RankDependent.sq_id_stronglyRiskAverse ..
  | (apply @Econ.RankDependent.sq_id_stronglyRiskAverse <;> assumption)

end RDUNecessity

end Econ.Audit.BehavioralXXVII
