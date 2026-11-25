/-
# Frozen statements: behavioral round 22

Headline statements of `Behavioral/ChoiceFromLists.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-22.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.ChoiceFromLists

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXII

section ChoiceFromLists
open Econ.ChoiceLists
variable {X : Type*} [DecidableEq X] {R : X → X → Bool} {δ : X → Bool} {D : List X → X}

theorem frozen_liia_pi {D : List X → X} (hD : IsChoice D) (h : LIIA D) : PI D := by
  first
  | exact @Econ.ChoiceLists.liia_pi ..
  | (apply @Econ.ChoiceLists.liia_pi <;> assumption)

theorem frozen_pi_liia {D : List X → X} (hD : IsChoice D) (h : PI D) : LIIA D := by
  first
  | exact @Econ.ChoiceLists.pi_liia ..
  | (apply @Econ.ChoiceLists.pi_liia <;> assumption)

theorem frozen_liia_iff_pi {D : List X → X} (hD : IsChoice D) : LIIA D ↔ PI D := by
  first
  | exact @Econ.ChoiceLists.liia_iff_pi ..
  | (apply @Econ.ChoiceLists.liia_iff_pi <;> assumption)

theorem frozen_rule_mem [Inhabited X] : IsChoice (rule R δ) := by
  first
  | exact @Econ.ChoiceLists.rule_mem ..
  | (apply @Econ.ChoiceLists.rule_mem <;> assumption)

theorem frozen_rule_isMax [Inhabited X] (hR : IsWeakOrder R) {L : List X} (hL : L ≠ []) :
    ∀ y ∈ L, R (rule R δ L) y := by
  first
  | exact @Econ.ChoiceLists.rule_isMax ..
  | (apply @Econ.ChoiceLists.rule_isMax <;> assumption)

theorem frozen_pi_rule [Inhabited X] (hR : IsWeakOrder R) (hδ : ClassConst R δ) : PI (rule R δ) := by
  first
  | exact @Econ.ChoiceLists.pi_rule ..
  | (apply @Econ.ChoiceLists.pi_rule <;> assumption)

theorem frozen_exists_rule_of_pi [Inhabited X] (hD : IsChoice D) (h : PI D) :
    ∃ (R : X → X → Bool) (δ : X → Bool), IsWeakOrder R ∧ ClassConst R δ ∧
      ∀ L, IsList L → D L = rule R δ L := by
  first
  | exact @Econ.ChoiceLists.exists_rule_of_pi ..
  | (apply @Econ.ChoiceLists.exists_rule_of_pi <;> assumption)

theorem frozen_pi_iff_rule [Inhabited X] (hD : IsChoice D) :
    PI D ↔ ∃ (R : X → X → Bool) (δ : X → Bool), IsWeakOrder R ∧ ClassConst R δ ∧
      ∀ L, IsList L → D L = rule R δ L := by
  first
  | exact @Econ.ChoiceLists.pi_iff_rule ..
  | (apply @Econ.ChoiceLists.pi_iff_rule <;> assumption)

theorem frozen_pi_first [Inhabited X] : PI (first (X := X)) := by
  first
  | exact @Econ.ChoiceLists.pi_first ..
  | (apply @Econ.ChoiceLists.pi_first <;> assumption)

theorem frozen_first_eq_rule [Inhabited X] {L : List X} (hL : L ≠ []) :
    first L = rule (fun _ _ => true) (fun _ => false) L := by
  first
  | exact @Econ.ChoiceLists.first_eq_rule ..
  | (apply @Econ.ChoiceLists.first_eq_rule <;> assumption)

theorem frozen_first_not_rational [Inhabited X] {a b : X} (hab : a ≠ b) :
    ¬ ∃ P : X → X → Prop, (∀ x y, P x y → ¬ P y x) ∧
      ∀ L, IsList L → ∀ y ∈ L, y ≠ first L → P (first L) y := by
  first
  | exact @Econ.ChoiceLists.first_not_rational ..
  | (apply @Econ.ChoiceLists.first_not_rational <;> assumption)

theorem frozen_pi_satisficing [Inhabited X] (S : X → Bool) : PI (satisficing S) := by
  first
  | exact @Econ.ChoiceLists.pi_satisficing ..
  | (apply @Econ.ChoiceLists.pi_satisficing <;> assumption)

theorem frozen_satisficing_satisfactory [Inhabited X] (S : X → Bool) {L : List X} (hL : L ≠ [])
    {y : X} (hy : y ∈ L) (hSy : S y) : S (satisficing S L) := by
  first
  | exact @Econ.ChoiceLists.satisficing_satisfactory ..
  | (apply @Econ.ChoiceLists.satisficing_satisfactory <;> assumption)

end ChoiceFromLists

end Econ.Audit.BehavioralXXII
