/-
# Frozen statements: behavioral round 13

Headline statements of `BoundedRationality/ESSUniform.lean`,
copied verbatim after the adversarial review (2026-11-24, record in
`Audit/REVIEW-behavioral-13.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.ESSUniform

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXIII

section ESSUniform
open Econ.ESS Finset
variable {n : ℕ} {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}

theorem frozen_post_mem {x y : Fin n → ℝ} (hx : x ∈ lotteries (Fin n)) (hy : y ∈ lotteries (Fin n))
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : post x y ε ∈ lotteries (Fin n) := by
  first
  | exact @Econ.ESS.post_mem ..
  | (apply @Econ.ESS.post_mem <;> assumption)

theorem frozen_exists_ray (hx : x ∈ lotteries (Fin n)) {y : Fin n → ℝ} (hy : y ∈ lotteries (Fin n))
    (hyx : y ≠ x) :
    ∃ z ∈ lotteries (Fin n), ∃ i0, 0 < x i0 ∧ z i0 = 0 ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧
      y = post x z l ∧ l * x i0 = x i0 - y i0 := by
  first
  | exact @Econ.ESS.exists_ray ..
  | (apply @Econ.ESS.exists_ray <;> assumption)

theorem frozen_advantage_ray (A : Fin n → Fin n → ℝ) (x z : Fin n → ℝ) (l ε : ℝ) :
    adv A x (post x z l) ε = l * adv A x z (ε * l) := by
  first
  | exact @Econ.ESS.advantage_ray ..
  | (apply @Econ.ESS.advantage_ray <;> assumption)

theorem frozen_abs_E_le {u v : Fin n → ℝ} (hu : u ∈ lotteries (Fin n)) (hv : v ∈ lotteries (Fin n)) :
    |E A u v| ≤ ∑ i, ∑ j, |A i j| := by
  first
  | exact @Econ.ESS.abs_E_le ..
  | (apply @Econ.ESS.abs_E_le <;> assumption)

theorem frozen_isESS_iff_uniform (A : Fin n → Fin n → ℝ) (hx : x ∈ lotteries (Fin n)) :
    IsESS A x ↔ ∃ εbar > 0, εbar ≤ 1 ∧ ∀ y ∈ lotteries (Fin n), y ≠ x → ∀ ε, 0 < ε → ε < εbar →
      E A y (post x y ε) < E A x (post x y ε) := by
  first
  | exact @Econ.ESS.isESS_iff_uniform ..
  | (apply @Econ.ESS.isESS_iff_uniform <;> assumption)

theorem frozen_isESS_iff_locallySuperior (A : Fin n → Fin n → ℝ) (hx : x ∈ lotteries (Fin n)) :
    IsESS A x ↔ ∃ δ > 0, ∀ y ∈ lotteries (Fin n), y ≠ x → (∀ i, |y i - x i| < δ) →
      E A y y < E A x y := by
  first
  | exact @Econ.ESS.isESS_iff_locallySuperior ..
  | (apply @Econ.ESS.isESS_iff_locallySuperior <;> assumption)

theorem frozen_hawkDove_uniform_locallySuperior {V C : ℝ} (hV : 0 < V) (hVC : V < C) :
    (∃ εbar > 0, εbar ≤ 1 ∧ ∀ y ∈ lotteries (Fin 2), y ≠ hdMix (V / C) → ∀ ε, 0 < ε →
      ε < εbar → E (hawkDove V C) y (post (hdMix (V / C)) y ε) <
        E (hawkDove V C) (hdMix (V / C)) (post (hdMix (V / C)) y ε)) ∧
    ∃ δ > 0, ∀ y ∈ lotteries (Fin 2), y ≠ hdMix (V / C) → (∀ i, |y i - hdMix (V / C) i| < δ) →
      E (hawkDove V C) y y < E (hawkDove V C) (hdMix (V / C)) y := by
  first
  | exact @Econ.ESS.hawkDove_uniform_locallySuperior ..
  | (apply @Econ.ESS.hawkDove_uniform_locallySuperior <;> assumption)

end ESSUniform

end Econ.Audit.BehavioralXIII
