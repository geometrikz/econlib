/-
# Frozen statements: behavioral round 19

Headline statements of `Behavioral/TemptationAxioms.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-19.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.TemptationAxioms

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXIX

section TemptationAxioms
open Econ.Temptation Finset
variable {X : Type*} [DecidableEq X]

theorem frozen_union_between {W : Finset X → ℝ} (hW : SetBetweenness W) {A B : Finset X}
    (hA : A.Nonempty) (hB : B.Nonempty) : min (W A) (W B) ≤ W (A ∪ B) ∧ W (A ∪ B) ≤ max (W A) (W B) := by
  first
  | exact @Econ.Temptation.union_between ..
  | (apply @Econ.Temptation.union_between <;> assumption)

theorem frozen_between_biUnion {ι : Type*} [DecidableEq ι] {W : Finset X → ℝ} (hW : SetBetweenness W)
    {s : Finset ι} (hs : s.Nonempty) {F : ι → Finset X} (hF : ∀ i ∈ s, (F i).Nonempty) :
    s.inf' hs (fun i => W (F i)) ≤ W (s.biUnion F) ∧ W (s.biUnion F) ≤ s.sup' hs (fun i => W (F i)) := by
  first
  | exact @Econ.Temptation.between_biUnion ..
  | (apply @Econ.Temptation.between_biUnion <;> assumption)

theorem frozen_eq_maxmin_pairs {W : Finset X → ℝ} (hW : SetBetweenness W) {A : Finset X}
    (hA : A.Nonempty) : W A = A.sup' hA (fun x => A.inf' hA (fun y => W {x, y})) := by
  first
  | exact @Econ.Temptation.eq_maxmin_pairs ..
  | (apply @Econ.Temptation.eq_maxmin_pairs <;> assumption)

theorem frozen_eq_of_pairs {W W' : Finset X → ℝ} (hW : SetBetweenness W) (hW' : SetBetweenness W')
    (h : ∀ x y : X, W {x, y} = W' {x, y}) {A : Finset X} (hA : A.Nonempty) : W A = W' A := by
  first
  | exact @Econ.Temptation.eq_of_pairs ..
  | (apply @Econ.Temptation.eq_of_pairs <;> assumption)

theorem frozen_GP_setBetweenness (u v : X → ℝ) : SetBetweenness (GP u v) := by
  first
  | exact @Econ.Temptation.GP_setBetweenness ..
  | (apply @Econ.Temptation.GP_setBetweenness <;> assumption)

theorem frozen_W_eq_maxmin_pairs (u v : X → ℝ) {A : Finset X} (hA : A.Nonempty) :
    W u v A hA = A.sup' hA (fun x => A.inf' hA (fun y => W u v {x, y} (insert_nonempty x {y}))) := by
  first
  | exact @Econ.Temptation.W_eq_maxmin_pairs ..
  | (apply @Econ.Temptation.W_eq_maxmin_pairs <;> assumption)

theorem frozen_eq_GP_of_pairs {W' : Finset X → ℝ} (hW : SetBetweenness W') (u v : X → ℝ)
    (h : ∀ x y : X, W' {x, y} = W u v {x, y} (insert_nonempty x {y})) {A : Finset X}
    (hA : A.Nonempty) : W' A = W u v A hA := by
  first
  | exact @Econ.Temptation.eq_GP_of_pairs ..
  | (apply @Econ.Temptation.eq_GP_of_pairs <;> assumption)

theorem frozen_eq_sup_singleton {W : Finset X → ℝ} (hW : StrategicRational W) {A : Finset X}
    (hA : A.Nonempty) : W A = A.sup' hA (fun x => W {x}) := by
  first
  | exact @Econ.Temptation.eq_sup_singleton ..
  | (apply @Econ.Temptation.eq_sup_singleton <;> assumption)

theorem frozen_strategicRational_sup (f : X → ℝ) :
    StrategicRational (fun A => if h : A.Nonempty then A.sup' h f else 0) := by
  first
  | exact @Econ.Temptation.strategicRational_sup ..
  | (apply @Econ.Temptation.strategicRational_sup <;> assumption)

theorem frozen_sbExample_setBetweenness : SetBetweenness sbExample := by
  first
  | exact @Econ.Temptation.sbExample_setBetweenness ..
  | (apply @Econ.Temptation.sbExample_setBetweenness <;> assumption)

theorem frozen_sbExample_not_GP : ¬ ∃ u v : Fin 3 → ℝ, ∀ x y : Fin 3,
    sbExample {x, y} = W u v {x, y} (insert_nonempty x {y}) := by
  first
  | exact @Econ.Temptation.sbExample_not_GP ..
  | (apply @Econ.Temptation.sbExample_not_GP <;> assumption)

end TemptationAxioms

end Econ.Audit.BehavioralXIX
