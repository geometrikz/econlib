/-
# Frozen statements: behavioral round 24

Headline statements of `Behavioral/RDUStrongRiskAversion.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-24.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.RDUStrongRiskAversion

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXIV

section RDUStrongRiskAversion
open Econ.RankDependent Finset Filter Topology


variable {n : ℕ}

theorem frozen_abel_support (a s : ℕ → ℝ) :
    ∀ (n : ℕ) (σ : ℝ), (∀ m ≤ n, 0 ≤ ∑ k ∈ range m, a k) →
      (∀ j k, j < k → k < n → a j ≠ 0 → a k ≠ 0 → s k ≤ s j) →
      (∀ k < n, a k ≠ 0 → σ ≤ s k) →
      σ * ∑ k ∈ range n, a k ≤ ∑ k ∈ range n, s k * a k := by
  first
  | exact @Econ.RankDependent.abel_support ..
  | (apply @Econ.RankDependent.abel_support <;> assumption)

theorem frozen_slope_le_slope {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) {a b a' b' : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (ha' : a' ∈ I) (hb' : b' ∈ I) (haa : a' ≤ a) (hbb : b' ≤ b)
    (hab : a ≠ b) (hab' : a' ≠ b') : slope f b' a' ≤ slope f b a := by
  first
  | exact @Econ.RankDependent.slope_le_slope ..
  | (apply @Econ.RankDependent.slope_le_slope <;> assumption)

theorem frozen_fuchs {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) (n : ℕ) {c x y : ℕ → ℝ}
    (hxI : ∀ k < n, x k ∈ I) (hyI : ∀ k < n, y k ∈ I)
    (hx : ∀ j k, j < k → k < n → x k ≤ x j) (hy : ∀ j k, j < k → k < n → y k ≤ y j)
    (hP : ∀ m ≤ n, 0 ≤ ∑ k ∈ range m, c k * (x k - y k))
    (htot : ∑ k ∈ range n, c k * (x k - y k) = 0) :
    0 ≤ ∑ k ∈ range n, c k * (f (x k) - f (y k)) := by
  first
  | exact @Econ.RankDependent.fuchs ..
  | (apply @Econ.RankDependent.fuchs <;> assumption)

theorem frozen_G_antitone (p : Lottery n) {j k : ℕ} (h : j ≤ k) : G p k ≤ G p j := by
  first
  | exact @Econ.RankDependent.G_antitone ..
  | (apply @Econ.RankDependent.G_antitone <;> assumption)

theorem frozen_yaari_mps {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw : ConvexOn ℝ (Set.Icc 0 1) w) {x : ℕ → ℝ} {p q : Lottery n} (h : IsMPS x q p) :
    rdu w x q ≤ rdu w x p := by
  first
  | exact @Econ.RankDependent.yaari_mps ..
  | (apply @Econ.RankDependent.yaari_mps <;> assumption)

theorem frozen_G_triLot_one (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    G (triLot t s hs hst ht) 1 = t := by
  first
  | exact @Econ.RankDependent.G_triLot_one ..
  | (apply @Econ.RankDependent.G_triLot_one <;> assumption)

theorem frozen_G_triLot_two (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    G (triLot t s hs hst ht) 2 = s := by
  first
  | exact @Econ.RankDependent.G_triLot_two ..
  | (apply @Econ.RankDependent.G_triLot_two <;> assumption)

theorem frozen_isMPS_tri {t s l : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    let r := l * t + (1 - l) * s
    ∀ (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
    IsMPS (fun k : ℕ => if k = 0 then 0 else if k = 1 then l else 1)
      (triLot r r hr0 le_rfl hr1) (triLot t s hs hst ht) := by
  first
  | exact @Econ.RankDependent.isMPS_tri ..
  | (apply @Econ.RankDependent.isMPS_tri <;> assumption)

theorem frozen_yaari_strongRiskAverse_iff {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    ConvexOn ℝ (Set.Icc 0 1) w ↔
      ∀ (n : ℕ) (x : ℕ → ℝ), MonotoneOnGrid n x → ∀ p q : Lottery n, IsMPS x q p →
        rdu w x q ≤ rdu w x p := by
  first
  | exact @Econ.RankDependent.yaari_strongRiskAverse_iff ..
  | (apply @Econ.RankDependent.yaari_strongRiskAverse_iff <;> assumption)

theorem frozen_sq_convex : ConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => t ^ 2) := by
  first
  | exact @Econ.RankDependent.sq_convex ..
  | (apply @Econ.RankDependent.sq_convex <;> assumption)

end RDUStrongRiskAversion

end Econ.Audit.BehavioralXXIV
