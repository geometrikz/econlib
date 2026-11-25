/-
# Frozen statements: behavioral round 25

Headline statements of `Behavioral/RDUConcaveConvex.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-25.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.RDUConcaveConvex

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXV

section RDUConcaveConvex
open Econ.RankDependent Finset Filter Topology


variable {n : ℕ}

theorem frozen_slope_nonneg_of_monotoneOn {f : ℝ → ℝ} {I : Set ℝ} (hf : MonotoneOn f I) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) : 0 ≤ slope f a b := by
  first
  | exact @Econ.RankDependent.slope_nonneg_of_monotoneOn ..
  | (apply @Econ.RankDependent.slope_nonneg_of_monotoneOn <;> assumption)

theorem frozen_slope_mul_sub (f : ℝ → ℝ) (a b : ℝ) : slope f a b * (b - a) = f b - f a := by
  first
  | exact @Econ.RankDependent.slope_mul_sub ..
  | (apply @Econ.RankDependent.slope_mul_sub <;> assumption)

theorem frozen_fuchs_mono {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) (hfm : MonotoneOn f I)
    (n : ℕ) {c x y : ℕ → ℝ}
    (hxI : ∀ k < n, x k ∈ I) (hyI : ∀ k < n, y k ∈ I)
    (hx : ∀ j k, j < k → k < n → x k ≤ x j) (hy : ∀ j k, j < k → k < n → y k ≤ y j)
    (hP : ∀ m ≤ n, 0 ≤ ∑ k ∈ range m, c k * (x k - y k)) :
    0 ≤ ∑ k ∈ range n, c k * (f (x k) - f (y k)) := by
  first
  | exact @Econ.RankDependent.fuchs_mono ..
  | (apply @Econ.RankDependent.fuchs_mono <;> assumption)

theorem frozen_isMPS_ssd {x : ℕ → ℝ} {p q : Lottery n} (h : IsMPS x q p) : SSD x q p := by
  first
  | exact @Econ.RankDependent.isMPS_ssd ..
  | (apply @Econ.RankDependent.isMPS_ssd <;> assumption)

theorem frozen_ssd_weighted {w : ℝ → ℝ} (hw : ConvexOn ℝ (Set.Icc 0 1) w)
    (hwm : MonotoneOn w (Set.Icc 0 1)) {x : ℕ → ℝ} {p q : Lottery n} (h : SSD x q p) :
    ∀ m ≤ n, ∑ k ∈ range m, w (G q (k + 1)) * (x (k + 1) - x k) ≤
      ∑ k ∈ range m, w (G p (k + 1)) * (x (k + 1) - x k) := by
  first
  | exact @Econ.RankDependent.ssd_weighted ..
  | (apply @Econ.RankDependent.ssd_weighted <;> assumption)

theorem frozen_monotoneOnGrid_le {x : ℕ → ℝ} (hx : MonotoneOnGrid n x) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) : x i ≤ x j := by
  first
  | exact @Econ.RankDependent.monotoneOnGrid_le ..
  | (apply @Econ.RankDependent.monotoneOnGrid_le <;> assumption)

theorem frozen_cks_ssd {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw : ConvexOn ℝ (Set.Icc 0 1) w) (hwm : MonotoneOn w (Set.Icc 0 1))
    {U : ℝ → ℝ} {I : Set ℝ} (hU : ConcaveOn ℝ I U) (hUm : MonotoneOn U I)
    {x : ℕ → ℝ} (hxI : ∀ k ≤ n, x k ∈ I) (hx : MonotoneOnGrid n x)
    {p q : Lottery n} (h : SSD x q p) :
    rdu w (fun k => U (x k)) q ≤ rdu w (fun k => U (x k)) p := by
  first
  | exact @Econ.RankDependent.cks_ssd ..
  | (apply @Econ.RankDependent.cks_ssd <;> assumption)

theorem frozen_cks_mps {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw : ConvexOn ℝ (Set.Icc 0 1) w) (hwm : MonotoneOn w (Set.Icc 0 1))
    {U : ℝ → ℝ} {I : Set ℝ} (hU : ConcaveOn ℝ I U) (hUm : MonotoneOn U I)
    {x : ℕ → ℝ} (hxI : ∀ k ≤ n, x k ∈ I) (hx : MonotoneOnGrid n x)
    {p q : Lottery n} (h : IsMPS x q p) :
    rdu w (fun k => U (x k)) q ≤ rdu w (fun k => U (x k)) p := by
  first
  | exact @Econ.RankDependent.cks_mps ..
  | (apply @Econ.RankDependent.cks_mps <;> assumption)

theorem frozen_sq_monotoneOn : MonotoneOn (fun t : ℝ => t ^ 2) (Set.Icc 0 1) := by
  first
  | exact @Econ.RankDependent.sq_monotoneOn ..
  | (apply @Econ.RankDependent.sq_monotoneOn <;> assumption)

theorem frozen_sqrt_sq_mps {x : ℕ → ℝ} (hx0 : ∀ k ≤ n, 0 ≤ x k) (hx : MonotoneOnGrid n x)
    {p q : Lottery n} (h : IsMPS x q p) :
    rdu (fun t => t ^ 2) (fun k => Real.sqrt (x k)) q ≤
      rdu (fun t => t ^ 2) (fun k => Real.sqrt (x k)) p := by
  first
  | exact @Econ.RankDependent.sqrt_sq_mps ..
  | (apply @Econ.RankDependent.sqrt_sq_mps <;> assumption)

theorem frozen_sqrt_sq_tri :
    rdu (fun t => t ^ 2) (fun k => Real.sqrt ((fun k : ℕ => if k = 0 then 0 else if k = 1 then
        (1 / 2 : ℝ) else 1) k))
        (triLot (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)) ≤
      rdu (fun t => t ^ 2) (fun k => Real.sqrt ((fun k : ℕ => if k = 0 then 0 else if k = 1 then
        (1 / 2 : ℝ) else 1) k))
        (triLot 1 0 le_rfl (by norm_num) le_rfl) := by
  first
  | exact @Econ.RankDependent.sqrt_sq_tri ..
  | (apply @Econ.RankDependent.sqrt_sq_tri <;> assumption)

theorem frozen_sq_tri_strict :
    let x : ℕ → ℝ := fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else 1
    eu x (triLot (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)) =
        eu x (triLot 1 0 le_rfl (by norm_num) le_rfl) ∧
      rdu (fun t => t ^ 2) x (triLot (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)) = 1 / 4 ∧
      rdu (fun t => t ^ 2) x (triLot 1 0 le_rfl (by norm_num) le_rfl) = 1 / 2 := by
  first
  | exact @Econ.RankDependent.sq_tri_strict ..
  | (apply @Econ.RankDependent.sq_tri_strict <;> assumption)

end RDUConcaveConvex

end Econ.Audit.BehavioralXXV
