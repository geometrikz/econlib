/-
# Frozen statements: modern micro (round 3)

Headline statements of `Behavioral/GilboaSchmeidler.lean`,
`Behavioral/StochasticChoice.lean`, `Networks/KeyPlayer.lean`,
`Information/Persuasion.lean` and `BoundedRationality/Existence.lean`, copied
verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-modern-micro.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.GilboaSchmeidler
public import EconLean.Behavioral.StochasticChoice
public import EconLean.Networks.KeyPlayer
public import EconLean.Information.Persuasion
public import EconLean.BoundedRationality.Existence

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Econ.Audit.ModernMicro

open Finset Matrix

section GilboaSchmeidler
open Econ.Ambiguity
variable {S : Type*} [Fintype S]

theorem frozen_maxmin_of_isMaxminFunctional {I : (S → ℝ) → ℝ} (hI : IsMaxminFunctional I) :
    priorSet I ⊆ priors S ∧ (priorSet I).Nonempty ∧ Convex ℝ (priorSet I) ∧
      IsClosed (priorSet I) ∧ ∀ f, IsLeast ((fun p => eu p f) '' priorSet I) (I f) := by
  first
  | exact @Econ.Ambiguity.maxmin_of_isMaxminFunctional ..
  | (apply @Econ.Ambiguity.maxmin_of_isMaxminFunctional <;> assumption)

theorem frozen_isMaxminFunctional_of_isLeast {I : (S → ℝ) → ℝ} {C : Set (S → ℝ)}
    (hC : C ⊆ priors S) (h : ∀ f, IsLeast ((fun p => eu p f) '' C) (I f)) :
    IsMaxminFunctional I := by
  first
  | exact @Econ.Ambiguity.isMaxminFunctional_of_isLeast ..
  | (apply @Econ.Ambiguity.isMaxminFunctional_of_isLeast <;> assumption)

theorem frozen_eq_priorSet {I : (S → ℝ) → ℝ} {C : Set (S → ℝ)} (hC : C ⊆ priors S)
    (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h : ∀ f, IsLeast ((fun p => eu p f) '' C) (I f)) : C = priorSet I := by
  first
  | exact @Econ.Ambiguity.eq_priorSet ..
  | (apply @Econ.Ambiguity.eq_priorSet <;> assumption)

theorem frozen_gilboa_schmeidler {R : (S → ℝ) → (S → ℝ) → Prop} (hR : GSAxioms R) :
    ∃ C : Set (S → ℝ), C ⊆ priors S ∧ C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧
      ∃ I : (S → ℝ) → ℝ, (∀ f, IsLeast ((fun p => eu p f) '' C) (I f)) ∧
        ∀ f g, R f g ↔ I g ≤ I f := by
  first
  | exact @Econ.Ambiguity.gilboa_schmeidler ..
  | (apply @Econ.Ambiguity.gilboa_schmeidler <;> assumption)

theorem frozen_gilboa_schmeidler_unique {R : (S → ℝ) → (S → ℝ) → Prop} {C₁ C₂ : Set (S → ℝ)}
    {I₁ I₂ : (S → ℝ) → ℝ} (hC₁ : C₁ ⊆ priors S) (hC₂ : C₂ ⊆ priors S)
    (hconv₁ : Convex ℝ C₁) (hconv₂ : Convex ℝ C₂) (hcl₁ : IsClosed C₁) (hcl₂ : IsClosed C₂)
    (h₁ : ∀ f, IsLeast ((fun p => eu p f) '' C₁) (I₁ f))
    (h₂ : ∀ f, IsLeast ((fun p => eu p f) '' C₂) (I₂ f))
    (hR₁ : ∀ f g, R f g ↔ I₁ g ≤ I₁ f) (hR₂ : ∀ f g, R f g ↔ I₂ g ≤ I₂ f) : C₁ = C₂ := by
  first
  | exact @Econ.Ambiguity.gilboa_schmeidler_unique ..
  | (apply @Econ.Ambiguity.gilboa_schmeidler_unique <;> assumption)

theorem frozen_gsAxioms_of_isMaxminFunctional {I : (S → ℝ) → ℝ} (hI : IsMaxminFunctional I) :
    GSAxioms (fun f g => I g ≤ I f) := by
  first
  | exact @Econ.Ambiguity.gsAxioms_of_isMaxminFunctional ..
  | (apply @Econ.Ambiguity.gsAxioms_of_isMaxminFunctional <;> assumption)

theorem frozen_gsAxioms_ellsberg :
    GSAxioms (fun f g => meu ellsbergPriors ellsbergPriors_nonempty g ≤
      meu ellsbergPriors ellsbergPriors_nonempty f) := by
  first
  | exact @Econ.Ambiguity.gsAxioms_ellsberg ..
  | (apply @Econ.Ambiguity.gsAxioms_ellsberg <;> assumption)

end GilboaSchmeidler

section StochasticChoice
open Econ.StochasticChoice
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem frozen_luce_isChoiceRule {w : X → ℝ} (hw : ∀ a, 0 < w a) : IsChoiceRule (luce w) := by
  first
  | exact @Econ.StochasticChoice.luce_isChoiceRule ..
  | (apply @Econ.StochasticChoice.luce_isChoiceRule <;> assumption)

theorem frozen_luce_iia {w : X → ℝ} (hw : ∀ a, 0 < w a) {A : Finset X} {a b : X} (ha : a ∈ A)
    (hb : b ∈ A) : luce w A a / luce w A b = w a / w b := by
  first
  | exact @Econ.StochasticChoice.luce_iia ..
  | (apply @Econ.StochasticChoice.luce_iia <;> assumption)

theorem frozen_luce_choiceAxiom {w : X → ℝ} (hw : ∀ a, 0 < w a) : ChoiceAxiom (luce w) := by
  first
  | exact @Econ.StochasticChoice.luce_choiceAxiom ..
  | (apply @Econ.StochasticChoice.luce_choiceAxiom <;> assumption)

theorem frozen_eq_luce_of_choiceAxiom {P : Finset X → X → ℝ} (hP : IsChoiceRule P)
    (hpos : ∀ A : Finset X, ∀ a ∈ A, 0 < P A a) (hax : ChoiceAxiom P) {A : Finset X}
    (hA : A.Nonempty) (a : X) :
    P A a = luce (fun b => P univ b) A a := by
  first
  | exact @Econ.StochasticChoice.eq_luce_of_choiceAxiom ..
  | (apply @Econ.StochasticChoice.eq_luce_of_choiceAxiom <;> assumption)

theorem frozen_softmax_eq_luce (lam : ℝ) (v : X → ℝ) (a : X) :
    Logit.softmax lam v a = luce (fun b => Real.exp (v b / lam)) univ a := by
  first
  | exact @Econ.StochasticChoice.softmax_eq_luce ..
  | (apply @Econ.StochasticChoice.softmax_eq_luce <;> assumption)

theorem frozen_rumP_isChoiceRule {μ : Ranking X → ℝ} (hμ : IsRUM μ) : IsChoiceRule (rumP μ) := by
  first
  | exact @Econ.StochasticChoice.rumP_isChoiceRule ..
  | (apply @Econ.StochasticChoice.rumP_isChoiceRule <;> assumption)

theorem frozen_rumP_regularity {μ : Ranking X → ℝ} (hμ : IsRUM μ) {A B : Finset X} (hAB : A ⊆ B)
    {a : X} (ha : a ∈ A) : rumP μ B a ≤ rumP μ A a := by
  first
  | exact @Econ.StochasticChoice.rumP_regularity ..
  | (apply @Econ.StochasticChoice.rumP_regularity <;> assumption)

theorem frozen_bm_rumP (μ : Ranking X → ℝ) {A : Finset X} {a : X} (ha : a ∈ A) :
    bm (rumP μ) A a = ∑ r, μ r * if IsTop r A a ∧ ∀ c, c ∉ A → r c < r a then 1 else 0 := by
  first
  | exact @Econ.StochasticChoice.bm_rumP ..
  | (apply @Econ.StochasticChoice.bm_rumP <;> assumption)

theorem frozen_bm_rumP_nonneg {μ : Ranking X → ℝ} (hμ : IsRUM μ) {A : Finset X} {a : X} (ha : a ∈ A) :
    0 ≤ bm (rumP μ) A a := by
  first
  | exact @Econ.StochasticChoice.bm_rumP_nonneg ..
  | (apply @Econ.StochasticChoice.bm_rumP_nonneg <;> assumption)

end StochasticChoice

section Networks
open Econ.Networks
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem frozen_isNash_iff {G : Matrix n n ℝ} (hG0 : ∀ i, G i i = 0) (α φ : ℝ) (x : n → ℝ) :
    IsNash α φ G x ↔ ∀ i, x i = α + φ * ∑ j, G i j * x j := by
  first
  | exact @Econ.Networks.isNash_iff ..
  | (apply @Econ.Networks.isNash_iff <;> assumption)

theorem frozen_isNash_iff_eq_bonacich {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ)
    (hG0 : ∀ i, G i i = 0) (α : ℝ) (x : n → ℝ) :
    IsNash α φ G x ↔ x = α • bonacich G φ := by
  first
  | exact @Econ.Networks.isNash_iff_eq_bonacich ..
  | (apply @Econ.Networks.isNash_iff_eq_bonacich <;> assumption)

theorem frozen_nash_pos {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) {α : ℝ} (hα : 0 < α) (i : n) :
    0 < (α • bonacich G φ) i := by
  first
  | exact @Econ.Networks.nash_pos ..
  | (apply @Econ.Networks.nash_pos <;> assumption)

theorem frozen_inv_remove {G : Matrix n n ℝ} {φ : ℝ} (hU : IsUnit (1 - φ • G)) (i : n)
    (hii : leontief G φ i i ≠ 0) :
    leontief (remove G i) φ = Matrix.of fun j k : {j // j ≠ i} =>
      leontief G φ j k - leontief G φ j i * leontief G φ i k / leontief G φ i i := by
  first
  | exact @Econ.Networks.inv_remove ..
  | (apply @Econ.Networks.inv_remove <;> assumption)

theorem frozen_aggregate_remove {G : Matrix n n ℝ} {φ : ℝ} (hU : IsUnit (1 - φ • G)) (i : n)
    (hii : leontief G φ i i ≠ 0) :
    aggregate (remove G i) φ = aggregate G φ - intercentrality G φ i := by
  first
  | exact @Econ.Networks.aggregate_remove ..
  | (apply @Econ.Networks.aggregate_remove <;> assumption)

theorem frozen_intercentrality_symm {G : Matrix n n ℝ} {φ : ℝ} (hsymm : Gᵀ = G) (i : n) :
    intercentrality G φ i = bonacich G φ i ^ 2 / leontief G φ i i := by
  first
  | exact @Econ.Networks.intercentrality_symm ..
  | (apply @Econ.Networks.intercentrality_symm <;> assumption)

theorem frozen_keyPlayer {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) {α : ℝ} (hα : 0 < α)
    (i j : n) :
    α * aggregate (remove G i) φ ≤ α * aggregate (remove G j) φ ↔
      intercentrality G φ j ≤ intercentrality G φ i := by
  first
  | exact @Econ.Networks.keyPlayer ..
  | (apply @Econ.Networks.keyPlayer <;> assumption)

theorem frozen_isNash_remove {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) (hG0 : ∀ i, G i i = 0)
    (α : ℝ) (i : n) (x : {j // j ≠ i} → ℝ) :
    IsNash α φ (remove G i) x ↔ x = α • bonacich (remove G i) φ := by
  first
  | exact @Econ.Networks.isNash_remove ..
  | (apply @Econ.Networks.isNash_remove <;> assumption)

theorem frozen_pair_numbers :
    bonacich (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) = ![2, 2] ∧
      aggregate (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) = 4 ∧
      intercentrality (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) 0 = 3 ∧
      aggregate (remove (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0) (1 / 2) = 1 := by
  first
  | exact @Econ.Networks.pair_numbers ..
  | (apply @Econ.Networks.pair_numbers <;> assumption)

end Networks

section Persuasion
open Econ.Persuasion
variable {Ω : Type*} [Fintype Ω] {M : Type*} [Fintype M] {v : (Ω → ℝ) → ℝ} {B : ℝ}

theorem frozen_signal_mean {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) (ω : Ω) :
    ∑ m, msgProb μ₀ σ m * post μ₀ σ m ω = μ₀ ω := by
  first
  | exact @Econ.Persuasion.signal_mean ..
  | (apply @Econ.Persuasion.signal_mean <;> assumption)

theorem frozen_Signal_value_toSplitting {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M)
    (v : (Ω → ℝ) → ℝ) : (σ.toSplitting h₀).value v = signalValue v μ₀ σ := by
  first
  | exact @Econ.Persuasion.Signal.value_toSplitting ..
  | (apply @Econ.Persuasion.Signal.value_toSplitting <;> assumption)

theorem frozen_Splitting_value_toSignal {μ₀ : Ω → ℝ} (s : Splitting μ₀) (v : (Ω → ℝ) → ℝ) :
    signalValue v μ₀ s.toSignal = s.value v := by
  first
  | exact @Econ.Persuasion.Splitting.value_toSignal ..
  | (apply @Econ.Persuasion.Splitting.value_toSignal <;> assumption)

theorem frozen_le_V (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    v μ₀ ≤ V v μ₀ := by
  first
  | exact @Econ.Persuasion.le_V ..
  | (apply @Econ.Persuasion.le_V <;> assumption)

theorem frozen_V_le_of_concave {g : (Ω → ℝ) → ℝ} (hg : ConcaveOn ℝ (beliefs Ω) g)
    (hvg : ∀ μ ∈ beliefs Ω, v μ ≤ g μ) {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    V v μ₀ ≤ g μ₀ := by
  first
  | exact @Econ.Persuasion.V_le_of_concave ..
  | (apply @Econ.Persuasion.V_le_of_concave <;> assumption)

theorem frozen_V_concave (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) : ConcaveOn ℝ (beliefs Ω) (V v) := by
  first
  | exact @Econ.Persuasion.V_concave ..
  | (apply @Econ.Persuasion.V_concave <;> assumption)

theorem frozen_benefits_iff (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    (∃ K, ∃ σ : Signal Ω (Fin K), v μ₀ < signalValue v μ₀ σ) ↔ v μ₀ < V v μ₀ := by
  first
  | exact @Econ.Persuasion.benefits_iff ..
  | (apply @Econ.Persuasion.benefits_iff <;> assumption)

theorem frozen_prosecutor_V : V convict prior = 3 / 5 ∧ convict prior = 0 := by
  first
  | exact @Econ.Persuasion.prosecutor_V ..
  | (apply @Econ.Persuasion.prosecutor_V <;> assumption)

theorem frozen_prosecutor_signal : signalValue convict prior prosecutorSplitting.toSignal = 3 / 5 := by
  first
  | exact @Econ.Persuasion.prosecutor_signal ..
  | (apply @Econ.Persuasion.prosecutor_signal <;> assumption)

end Persuasion

section QREExistence
open Econ.BoundedRationality
variable {I : Type*} [Fintype I] [DecidableEq I] (G : FiniteGame I) [∀ i, Nonempty (G.A i)]

theorem frozen_exists_isLogitQRE (lam : ℝ) : ∃ σ, IsLogitQRE G lam σ := by
  first
  | exact @Econ.BoundedRationality.exists_isLogitQRE ..
  | (apply @Econ.BoundedRationality.exists_isLogitQRE <;> assumption)

end QREExistence

section BNExistence
open Econ.BoundedRationality Econ.BoundedRationality.SubjectiveProblem Econ.Logit Econ.RationalInattention
variable {X Y Θ : Type*} [Fintype X] [Fintype Y] [Fintype Θ] (M : SubjectiveProblem X Y Θ)

theorem frozen_exists_isBerkNash [Nonempty X] [Nonempty Θ] : ∃ σ μ, M.IsBerkNash σ μ := by
  first
  | exact @Econ.BoundedRationality.SubjectiveProblem.exists_isBerkNash ..
  | (apply @Econ.BoundedRationality.SubjectiveProblem.exists_isBerkNash <;> assumption)

end BNExistence

end Econ.Audit.ModernMicro
