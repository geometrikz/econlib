/-
# Frozen statements: behavioral round 18

Headline statements of `Behavioral/CARACharacterization.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-18.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.CARACharacterization

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXVIII

section CARACharacterization
open Econ.Bracketing Finset Filter Topology Set


theorem frozen_ti_of_not_wealthEffect {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u)
    (h : ¬ WealthEffect u coin) : TI u := by
  first
  | exact @Econ.Bracketing.ti_of_not_wealthEffect ..
  | (apply @Econ.Bracketing.ti_of_not_wealthEffect <;> assumption)

theorem frozen_affine_shift_of_ti {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u) (hti : TI u)
    (w : ℝ) : ∃ α β : ℝ, 0 < α ∧ ∀ x, u (x + w) = α * u x + β := by
  first
  | exact @Econ.Bracketing.affine_shift_of_ti ..
  | (apply @Econ.Bracketing.affine_shift_of_ti <;> assumption)

theorem frozen_isCARAorLinear_of_affine_shift {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u)
    (h : ∀ w, ∃ α β : ℝ, ∀ x, u (x + w) = α * u x + β) : IsCARAorLinear u := by
  first
  | exact @Econ.Bracketing.isCARAorLinear_of_affine_shift ..
  | (apply @Econ.Bracketing.isCARAorLinear_of_affine_shift <;> assumption)

theorem frozen_isCARAorLinear_of_ti {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u)
    (hti : TI u) : IsCARAorLinear u := by
  first
  | exact @Econ.Bracketing.isCARAorLinear_of_ti ..
  | (apply @Econ.Bracketing.isCARAorLinear_of_ti <;> assumption)

theorem frozen_narrowDominated_affine {v : ℝ → ℝ} {c d : ℝ} (hd : 0 < d) {n : ℕ} {p : Fin n → ℝ}
    (h : NarrowDominated (fun x => c + d * v x) p) : NarrowDominated v p := by
  first
  | exact @Econ.Bracketing.narrowDominated_affine ..
  | (apply @Econ.Bracketing.narrowDominated_affine <;> assumption)

theorem frozen_rabinWeizsacker {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u) :
    NarrowDominated u coin ↔ ¬ IsCARAorLinear u := by
  first
  | exact @Econ.Bracketing.rabinWeizsacker ..
  | (apply @Econ.Bracketing.rabinWeizsacker <;> assumption)

theorem frozen_kink_not_isCARAorLinear : ¬ IsCARAorLinear kink := by
  first
  | exact @Econ.Bracketing.kink_not_isCARAorLinear ..
  | (apply @Econ.Bracketing.kink_not_isCARAorLinear <;> assumption)

theorem frozen_cara_isCARAorLinear {α : ℝ} (hα : 0 < α) : IsCARAorLinear (cara α) := by
  first
  | exact @Econ.Bracketing.cara_isCARAorLinear ..
  | (apply @Econ.Bracketing.cara_isCARAorLinear <;> assumption)

theorem frozen_id_isCARAorLinear : IsCARAorLinear (fun x : ℝ => x) := by
  first
  | exact @Econ.Bracketing.id_isCARAorLinear ..
  | (apply @Econ.Bracketing.id_isCARAorLinear <;> assumption)

end CARACharacterization

end Econ.Audit.BehavioralXVIII
