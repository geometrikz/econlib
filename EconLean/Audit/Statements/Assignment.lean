/-
# Frozen statements: the Shapley–Shubik assignment game

Headline statements of `Cooperative/Assignment`, copied after the adversarial review recorded
in `Audit/REVIEW-assignment.md`. Each is closed by the library theorem, so if a library statement
is ever weakened this file stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Cooperative.Assignment

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Finset Econ

section

variable {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]

theorem frozen_assignment_inCore_iff (a : B → S → ℝ) (x : B ⊕ S → ℝ) :
    IsInCore (assignmentGame a) x ↔
      (∀ i, 0 ≤ x i) ∧ (∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) ∧
        ∑ i, x i = assignmentGame a univ :=
  Econ.assignment_inCore_iff (a := a) (x := x)

theorem frozen_assignment_isBalanced (a : B → S → ℝ) : IsBalanced (assignmentGame a) :=
  Econ.assignment_isBalanced (a := a)

theorem frozen_assignment_weak_duality (a : B → S → ℝ) {x : B ⊕ S → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hcov : ∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) :
    assignmentGame a univ ≤ ∑ i, x i :=
  Econ.assignment_weak_duality (a := a) (x := x) (hx := hx) (hcov := hcov)

theorem frozen_assignment_core_nonempty (a : B → S → ℝ) : ∃ x, IsInCore (assignmentGame a) x :=
  Econ.assignment_core_nonempty (a := a)

theorem frozen_shapley_shubik (a : B → S → ℝ) :
    ∃ u : B → ℝ, ∃ p : S → ℝ, (∀ b, 0 ≤ u b) ∧ (∀ s, 0 ≤ p s) ∧ (∀ b s, a b s ≤ u b + p s) ∧
      ∑ b, u b + ∑ s, p s = assignmentGame a univ :=
  Econ.shapley_shubik (a := a)

theorem frozen_assignment_strong_duality (a : B → S → ℝ) :
    (∀ x : B ⊕ S → ℝ, (∀ i, 0 ≤ x i) → (∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) →
      assignmentGame a univ ≤ ∑ i, x i) ∧
    ∃ x : B ⊕ S → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) ∧
      ∑ i, x i = assignmentGame a univ :=
  Econ.assignment_strong_duality (a := a)

end

end Econ.Audit
