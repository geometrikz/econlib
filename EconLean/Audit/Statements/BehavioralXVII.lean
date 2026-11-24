/-
# Frozen statements: behavioral round 17

Headline statements of `Behavioral/RabinWeizsacker.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-17.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.RabinWeizsacker

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXVII

section RabinWeizsacker
open Econ.Bracketing Finset Filter Topology
variable {n : ℕ}

theorem frozen_broad_prefers {v : ℝ → ℝ} (hv : StrictMono v) {p : Fin n → ℝ} (hp : IsProb p)
    (y : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) : EU v p y < EU v p (fun i => y i + δ) := by
  first
  | exact @Econ.Bracketing.broad_prefers ..
  | (apply @Econ.Bracketing.broad_prefers <;> assumption)

theorem frozen_narrowDominated_of_wealthEffect {u : ℝ → ℝ} (hc : Continuous u) {p : Fin n → ℝ}
    (hp : IsProb p) (hw : WealthEffect u p) : NarrowDominated u p := by
  first
  | exact @Econ.Bracketing.narrowDominated_of_wealthEffect ..
  | (apply @Econ.Bracketing.narrowDominated_of_wealthEffect <;> assumption)

theorem frozen_cara_not_narrowDominated {α : ℝ} (hα : 0 < α) (p : Fin n → ℝ) :
    ¬ NarrowDominated (cara α) p := by
  first
  | exact @Econ.Bracketing.cara_not_narrowDominated ..
  | (apply @Econ.Bracketing.cara_not_narrowDominated <;> assumption)

theorem frozen_caraLove_not_narrowDominated {β : ℝ} (hβ : 0 < β) (p : Fin n → ℝ) :
    ¬ NarrowDominated (caraLove β) p := by
  first
  | exact @Econ.Bracketing.caraLove_not_narrowDominated ..
  | (apply @Econ.Bracketing.caraLove_not_narrowDominated <;> assumption)

theorem frozen_linear_not_narrowDominated {a b : ℝ} (ha : 0 < a) {p : Fin n → ℝ} (hp : IsProb p) :
    ¬ NarrowDominated (fun x => a * x + b) p := by
  first
  | exact @Econ.Bracketing.linear_not_narrowDominated ..
  | (apply @Econ.Bracketing.linear_not_narrowDominated <;> assumption)

theorem frozen_kink_wealthEffect : WealthEffect kink coin := by
  first
  | exact @Econ.Bracketing.kink_wealthEffect ..
  | (apply @Econ.Bracketing.kink_wealthEffect <;> assumption)

theorem frozen_kink_narrowDominated : NarrowDominated kink coin := by
  first
  | exact @Econ.Bracketing.kink_narrowDominated ..
  | (apply @Econ.Bracketing.kink_narrowDominated <;> assumption)

end RabinWeizsacker

end Econ.Audit.BehavioralXVII
