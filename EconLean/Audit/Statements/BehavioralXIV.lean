/-
# Frozen statements: behavioral round 14

Headline statements of `BoundedRationality/SwapRegret.lean` and
`BoundedRationality/CursedMixed.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-14.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.SwapRegret
public import EconLean.BoundedRationality.CursedMixed

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXIV

section SwapRegret
open Econ.RegretMatching Function Finset Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

theorem frozen_swapGain_eq_sum (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I)
    (φ : S i → S i) : swapGain u μ i φ = ∑ j, obedienceGain u μ i j (φ j) := by
  first
  | exact @Econ.RegretMatching.swapGain_eq_sum ..
  | (apply @Econ.RegretMatching.swapGain_eq_sum <;> assumption)

theorem frozen_isCorrelatedEq_iff_swap (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) :
    IsCorrelatedEq u μ ↔ μ ∈ lotteries (∀ j, S j) ∧ ∀ i φ, swapGain u μ i φ ≤ 0 := by
  first
  | exact @Econ.RegretMatching.isCorrelatedEq_iff_swap ..
  | (apply @Econ.RegretMatching.isCorrelatedEq_iff_swap <;> assumption)

end SwapRegret

section SwapRegret
open Econ.RegretMatching Function Finset Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

theorem frozen_swapRegret_eq (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (φ : S i → S i) :
    swapRegret u T i φ = T * swapGain u (condAvg u T) i φ := by
  first
  | exact @Econ.RegretMatching.swapRegret_eq ..
  | (apply @Econ.RegretMatching.swapRegret_eq <;> assumption)

theorem frozen_swapGain_condAvg_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {T : ℕ} (hT : 0 < T) (i : I) (φ : S i → S i) :
    swapGain u (condAvg u T) i φ ≤ 2 * B * Fintype.card (S i) ^ 2 / Real.sqrt T := by
  first
  | exact @Econ.RegretMatching.swapGain_condAvg_le ..
  | (apply @Econ.RegretMatching.swapGain_condAvg_le <;> assumption)

theorem frozen_eventually_swapGain_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ i (φ : S i → S i), swapGain u (condAvg u T) i φ ≤ ε := by
  first
  | exact @Econ.RegretMatching.eventually_swapGain_le ..
  | (apply @Econ.RegretMatching.eventually_swapGain_le <;> assumption)

end SwapRegret

section CursedMixed
open Econ.Cursed Function Finset
variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] {C : I → Type*} [∀ i, DecidableEq (C i)]

theorem frozen_behavCursedInterim_eq (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    (p : (∀ j, Θ j) → ℝ) (β : ∀ i, Θ i → A i → ℝ) (i : I) (θi : Θ i) (c : A i) :
    behavCursedInterim χ u p β i θi c = behavInterim (cursedPayoff χ u p) p β i θi c := by
  first
  | exact @Econ.Cursed.behavCursedInterim_eq ..
  | (apply @Econ.Cursed.behavCursedInterim_eq <;> assumption)

theorem frozen_isBehavCursedEq_iff {χ : ℝ} {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} {β : ∀ i, Θ i → A i → ℝ} :
    IsBehavCursedEq χ u p β ↔ IsBehavBNE (cursedPayoff χ u p) p β := by
  first
  | exact @Econ.Cursed.isBehavCursedEq_iff ..
  | (apply @Econ.Cursed.isBehavCursedEq_iff <;> assumption)

theorem frozen_isBehavCursedEq_zero_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} {β : ∀ i, Θ i → A i → ℝ} :
    IsBehavCursedEq 0 u p β ↔ IsBehavBNE u p β := by
  first
  | exact @Econ.Cursed.isBehavCursedEq_zero_iff ..
  | (apply @Econ.Cursed.isBehavCursedEq_zero_iff <;> assumption)

theorem frozen_pureDev_agentPay (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    {τ : ∀ k : Σ i, Θ i, A k.1 → ℝ} (hτ : IsMixedProfile τ) (i : I) (θi : Θ i) (c : A i) :
    pureDev (agentPay u p) τ ⟨i, θi⟩ c = behavInterim u p (toBehav τ) i θi c := by
  first
  | exact @Econ.Cursed.pureDev_agentPay ..
  | (apply @Econ.Cursed.pureDev_agentPay <;> assumption)

theorem frozen_exists_isBehavBNE [∀ i, Nonempty (A i)] (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    {p : (∀ j, Θ j) → ℝ} (hp : p ∈ lotteries (∀ j, Θ j)) :
    ∃ β : ∀ i, Θ i → A i → ℝ, IsBehavBNE u p β := by
  first
  | exact @Econ.Cursed.exists_isBehavBNE ..
  | (apply @Econ.Cursed.exists_isBehavBNE <;> assumption)

theorem frozen_exists_isBehavCursedEq [∀ i, Nonempty (A i)] (χ : ℝ)
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) {p : (∀ j, Θ j) → ℝ}
    (hp : p ∈ lotteries (∀ j, Θ j)) :
    ∃ β : ∀ i, Θ i → A i → ℝ, IsBehavCursedEq χ u p β := by
  first
  | exact @Econ.Cursed.exists_isBehavCursedEq ..
  | (apply @Econ.Cursed.exists_isBehavCursedEq <;> assumption)

theorem frozen_behavAnalogyInterim_eq {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) (β : ∀ i, Θ i → A i → ℝ)
    (i : I) (θi : Θ i) (c : A i) :
    behavAnalogyInterim u p cls β i θi c = behavInterim (classPayoff u p cls) p β i θi c := by
  first
  | exact @Econ.Cursed.behavAnalogyInterim_eq ..
  | (apply @Econ.Cursed.behavAnalogyInterim_eq <;> assumption)

theorem frozen_isBehavABEE_iff {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ} {β : ∀ i, Θ i → A i → ℝ} :
    IsBehavABEE u p cls β ↔ IsBehavBNE (classPayoff u p cls) p β := by
  first
  | exact @Econ.Cursed.isBehavABEE_iff ..
  | (apply @Econ.Cursed.isBehavABEE_iff <;> assumption)

theorem frozen_exists_isBehavABEE [∀ i, Nonempty (A i)] {cls : ∀ i, (∀ j, Θ j) → C i}
    (hcls : IsAnalogyPartition cls) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    {p : (∀ j, Θ j) → ℝ} (hp : p ∈ lotteries (∀ j, Θ j)) :
    ∃ β : ∀ i, Θ i → A i → ℝ, IsBehavABEE u p cls β := by
  first
  | exact @Econ.Cursed.exists_isBehavABEE ..
  | (apply @Econ.Cursed.exists_isBehavABEE <;> assumption)

end CursedMixed

end Econ.Audit.BehavioralXIV
