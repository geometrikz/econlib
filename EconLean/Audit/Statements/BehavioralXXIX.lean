/-
# Frozen statements: behavioral round 29

Headline statements of `Behavioral/LevelKForwardGuidance.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-29.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.LevelKForwardGuidance

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXIX

section LevelKForwardGuidance
open Econ.LevelKFG Finset Filter Topology


theorem frozen_plan_path {σ : ℝ} {T : ℕ} {c : ℕ → ℝ} (h : ∀ s, c (s + 1) = c s + σ * rcut T s) (s : ℕ) :
    c s = c 0 - σ * (if T < s then 1 else 0) := by
  first
  | exact @Econ.LevelKFG.plan_path ..
  | (apply @Econ.LevelKFG.plan_path <;> assumption)

theorem frozen_plan_eq {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {T : ℕ} {y c : ℕ → ℝ}
    (hy : ∀ s, T < s → y s = 0) (hc : IsPlan β σ T y c) :
    c 0 = (1 - β) * ∑ s ∈ range (T + 1), β ^ s * y s + σ * β ^ (T + 1) ∧
      ∀ s ≤ T, c s = c 0 := by
  first
  | exact @Econ.LevelKFG.plan_eq ..
  | (apply @Econ.LevelKFG.plan_eq <;> assumption)

theorem frozen_exists_plan {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) {y : ℕ → ℝ}
    (hy : ∀ s, T < s → y s = 0) : ∃ c, IsPlan β σ T y c := by
  first
  | exact @Econ.LevelKFG.exists_plan ..
  | (apply @Econ.LevelKFG.exists_plan <;> assumption)

theorem frozen_rational_eq {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {T : ℕ} {y : ℕ → ℝ}
    (h : IsRational β σ T y) : ∀ s ≤ T, y s = σ := by
  first
  | exact @Econ.LevelKFG.rational_eq ..
  | (apply @Econ.LevelKFG.rational_eq <;> assumption)

theorem frozen_rational_clears_after {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {T : ℕ} {y c : ℕ → ℝ}
    (hy : ∀ s, T < s → y s = 0) (hc : IsPlan β σ T y c) (hyc : ∀ s ≤ T, y s = c s) :
    ∀ s, T < s → c s = 0 := by
  first
  | exact @Econ.LevelKFG.rational_clears_after ..
  | (apply @Econ.LevelKFG.rational_clears_after <;> assumption)

theorem frozen_exists_rational {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    IsRational β σ T fun s => if s ≤ T then σ else 0 := by
  first
  | exact @Econ.LevelKFG.exists_rational ..
  | (apply @Econ.LevelKFG.exists_rational <;> assumption)

theorem frozen_levelK_eq {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {T : ℕ} {Y : ℕ → ℕ → ℝ}
    (h : IsLevelK β σ T Y) : ∀ k, ∀ s ≤ T, Y k s = levelK β σ T k := by
  first
  | exact @Econ.LevelKFG.levelK_eq ..
  | (apply @Econ.LevelKFG.levelK_eq <;> assumption)

theorem frozen_exists_levelK {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) :
    ∃ Y, IsLevelK β σ T Y := by
  first
  | exact @Econ.LevelKFG.exists_levelK ..
  | (apply @Econ.LevelKFG.exists_levelK <;> assumption)

theorem frozen_gap_mem {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    0 ≤ 1 - β ^ (T + 1) ∧ 1 - β ^ (T + 1) < 1 := by
  first
  | exact @Econ.LevelKFG.gap_mem ..
  | (apply @Econ.LevelKFG.gap_mem <;> assumption)

theorem frozen_levelK_lt_rational {β σ : ℝ} (hσ : 0 < σ) (T k : ℕ)
    (hT : 0 < 1 - β ^ (T + 1)) : levelK β σ T k < σ := by
  first
  | exact @Econ.LevelKFG.levelK_lt_rational ..
  | (apply @Econ.LevelKFG.levelK_lt_rational <;> assumption)

theorem frozen_levelK_strictMono {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (T : ℕ)
    (hT : 0 < 1 - β ^ (T + 1)) : StrictMono (levelK β σ T) := by
  first
  | exact @Econ.LevelKFG.levelK_strictMono ..
  | (apply @Econ.LevelKFG.levelK_strictMono <;> assumption)

theorem frozen_tendsto_levelK {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    Tendsto (levelK β σ T) atTop (𝓝 σ) := by
  first
  | exact @Econ.LevelKFG.tendsto_levelK ..
  | (apply @Econ.LevelKFG.tendsto_levelK <;> assumption)

theorem frozen_levelK_strictAnti_horizon {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) {k : ℕ}
    (hk : 1 ≤ k) : StrictAnti fun T => levelK β σ T k := by
  first
  | exact @Econ.LevelKFG.levelK_strictAnti_horizon ..
  | (apply @Econ.LevelKFG.levelK_strictAnti_horizon <;> assumption)

theorem frozen_tendsto_levelK_horizon {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (k : ℕ) :
    Tendsto (fun T => levelK β σ T k) atTop (𝓝 0) := by
  first
  | exact @Econ.LevelKFG.tendsto_levelK_horizon ..
  | (apply @Econ.LevelKFG.tendsto_levelK_horizon <;> assumption)

end LevelKForwardGuidance

end Econ.Audit.BehavioralXXIX
