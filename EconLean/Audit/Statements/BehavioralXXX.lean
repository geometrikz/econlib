/-
# Frozen statements: behavioral round 30

Headline statements of `Behavioral/DeGroot.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-30.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.DeGroot

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXX

section DeGroot
open Econ.DeGroot Matrix Finset Filter Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem frozen_spread_mul_le {A : Matrix ι ι ℝ} (hA : IsStochastic A) {δ : ℝ}
    (hδ : ∀ i j, δ ≤ A i j) {p : ι → ℝ} {lo hi : ℝ} (hlo : ∀ j, lo ≤ p j)
    (hhi : ∀ j, p j ≤ hi) (i i' : ι) :
    (A *ᵥ p) i - (A *ᵥ p) i' ≤ (1 - Fintype.card ι * δ) * (hi - lo) := by
  first
  | exact @Econ.DeGroot.spread_mul_le ..
  | (apply @Econ.DeGroot.spread_mul_le <;> assumption)

theorem frozen_consensus {T : Matrix ι ι ℝ} (hT : IsStochastic T) (hP : IsPrimitive T) (p : ι → ℝ) :
    ∃ L : ℝ, ∀ i, Tendsto (fun t => (T ^ t *ᵥ p) i) atTop (𝓝 L) := by
  first
  | exact @Econ.DeGroot.consensus ..
  | (apply @Econ.DeGroot.consensus <;> assumption)

theorem frozen_influence [Nonempty ι] {T : Matrix ι ι ℝ} (hT : IsStochastic T) (hP : IsPrimitive T) :
    ∃ π : ι → ℝ, IsInfluence T π ∧ (∀ j, 0 < π j) ∧
      (∀ i j, Tendsto (fun t => (T ^ t) i j) atTop (𝓝 (π j))) ∧
      ∀ p : ι → ℝ, ∀ i, Tendsto (fun t => (T ^ t *ᵥ p) i) atTop (𝓝 (π ⬝ᵥ p)) := by
  first
  | exact @Econ.DeGroot.influence ..
  | (apply @Econ.DeGroot.influence <;> assumption)

theorem frozen_influence_unique [Nonempty ι] {T : Matrix ι ι ℝ} (hT : IsStochastic T) (hP : IsPrimitive T)
    {π π' : ι → ℝ} (h : IsInfluence T π) (h' : IsInfluence T π') : π = π' := by
  first
  | exact @Econ.DeGroot.influence_unique ..
  | (apply @Econ.DeGroot.influence_unique <;> assumption)

theorem frozen_isStochastic_normalize {g : Matrix ι ι ℝ} (hg : ∀ i j, 0 ≤ g i j)
    (hd : ∀ i, 0 < ∑ l, g i l) : IsStochastic (normalize g) := by
  first
  | exact @Econ.DeGroot.isStochastic_normalize ..
  | (apply @Econ.DeGroot.isStochastic_normalize <;> assumption)

theorem frozen_influence_degree {g : Matrix ι ι ℝ} (hsym : gᵀ = g)
    (hd : ∀ i, 0 < ∑ l, g i l) [Nonempty ι] :
    IsInfluence (normalize g) fun i => (∑ l, g i l) / ∑ m, ∑ l, g m l := by
  first
  | exact @Econ.DeGroot.influence_degree ..
  | (apply @Econ.DeGroot.influence_degree <;> assumption)

theorem frozen_consensus_degree {g : Matrix ι ι ℝ} (hg : ∀ i j, 0 ≤ g i j) (hsym : gᵀ = g)
    (hd : ∀ i, 0 < ∑ l, g i l) (hP : IsPrimitive (normalize g)) (p : ι → ℝ) (i : ι) :
    Tendsto (fun t => (normalize g ^ t *ᵥ p) i) atTop
      (𝓝 ((∑ j, (∑ l, g j l) * p j) / ∑ m, ∑ l, g m l)) := by
  first
  | exact @Econ.DeGroot.consensus_degree ..
  | (apply @Econ.DeGroot.consensus_degree <;> assumption)

theorem frozen_primitive_of_pos {T : Matrix ι ι ℝ} (h : ∀ i j, 0 < T i j) : IsPrimitive T := by
  first
  | exact @Econ.DeGroot.primitive_of_pos ..
  | (apply @Econ.DeGroot.primitive_of_pos <;> assumption)

theorem frozen_half_stochastic : IsStochastic half := by
  first
  | exact @Econ.DeGroot.half_stochastic ..
  | (apply @Econ.DeGroot.half_stochastic <;> assumption)

theorem frozen_half_primitive : IsPrimitive half := by
  first
  | exact @Econ.DeGroot.half_primitive ..
  | (apply @Econ.DeGroot.half_primitive <;> assumption)

theorem frozen_normalize_ones : normalize (fun _ _ : Fin 2 => (1 : ℝ)) = half := by
  first
  | exact @Econ.DeGroot.normalize_ones ..
  | (apply @Econ.DeGroot.normalize_ones <;> assumption)

theorem frozen_swap_stochastic : IsStochastic swap := by
  first
  | exact @Econ.DeGroot.swap_stochastic ..
  | (apply @Econ.DeGroot.swap_stochastic <;> assumption)

theorem frozen_swap_influence : IsInfluence swap ![1 / 2, 1 / 2] := by
  first
  | exact @Econ.DeGroot.swap_influence ..
  | (apply @Econ.DeGroot.swap_influence <;> assumption)

theorem frozen_swap_not_primitive : ¬ IsPrimitive swap := by
  first
  | exact @Econ.DeGroot.swap_not_primitive ..
  | (apply @Econ.DeGroot.swap_not_primitive <;> assumption)

theorem frozen_swap_not_converge :
    ¬ ∃ L : ℝ, Tendsto (fun t => (swap ^ t *ᵥ ![1, 0]) 0) atTop (𝓝 L) := by
  first
  | exact @Econ.DeGroot.swap_not_converge ..
  | (apply @Econ.DeGroot.swap_not_converge <;> assumption)

end DeGroot

end Econ.Audit.BehavioralXXX
