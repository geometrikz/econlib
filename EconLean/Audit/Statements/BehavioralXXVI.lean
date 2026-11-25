/-
# Frozen statements: behavioral round 26

Headline statements of `Behavioral/RISymmetric.lean`,
copied verbatim after the adversarial review (2026-11-25, record in
`Audit/REVIEW-behavioral-26.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.RISymmetric

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralXXVI

section RISymmetric
open Econ.RationalInattention Finset Real Logit
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem frozen_riObjective_le_valueF {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ} (hg : IsPrior g)
    (v : Ω → ι → ℝ) {p : Ω → ι → ℝ} (hp : IsRule p) :
    riObjective lam g v p ≤ valueF lam g v (marginal g p) := by
  first
  | exact @Econ.RationalInattention.riObjective_le_valueF ..
  | (apply @Econ.RationalInattention.riObjective_le_valueF <;> assumption)

theorem frozen_isRule_gl {lam : ℝ} {P : ι → ℝ} (hP : IsProb P) (v : Ω → ι → ℝ) :
    IsRule fun ω => generalizedLogit lam P (v ω) := by
  first
  | exact @Econ.RationalInattention.isRule_gl ..
  | (apply @Econ.RationalInattention.isRule_gl <;> assumption)

theorem frozen_valueF_le_riObjective_gl {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ} (hg : IsPrior g)
    (v : Ω → ι → ℝ) {P : ι → ℝ} (hP : IsProb P) :
    valueF lam g v P ≤ riObjective lam g v fun ω => generalizedLogit lam P (v ω) := by
  first
  | exact @Econ.RationalInattention.valueF_le_riObjective_gl ..
  | (apply @Econ.RationalInattention.valueF_le_riObjective_gl <;> assumption)

theorem frozen_isOptimalRule_gl_of_isMax {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ} (hg : IsPrior g)
    (v : Ω → ι → ℝ) {P : ι → ℝ} (hP : IsProb P)
    (hmax : ∀ P', IsProb P' → valueF lam g v P' ≤ valueF lam g v P) :
    IsOptimalRule lam g v fun ω => generalizedLogit lam P (v ω) := by
  first
  | exact @Econ.RationalInattention.isOptimalRule_gl_of_isMax ..
  | (apply @Econ.RationalInattention.isOptimalRule_gl_of_isMax <;> assumption)

theorem frozen_valueF_avg_ge {κ : Type*} {lam : ℝ} (hlam : 0 ≤ lam) {g : Ω → ℝ} (hg : ∀ ω, 0 ≤ g ω)
    (v : Ω → ι → ℝ) {S : Finset κ} (hS : S.Nonempty) (Pk : κ → ι → ℝ)
    (hPk : ∀ k ∈ S, IsProb (Pk k)) :
    ∑ k ∈ S, (1 / (#S : ℝ)) * valueF lam g v (Pk k) ≤
      valueF lam g v fun i => ∑ k ∈ S, (1 / (#S : ℝ)) * Pk k i := by
  first
  | exact @Econ.RationalInattention.valueF_avg_ge ..
  | (apply @Econ.RationalInattention.valueF_avg_ge <;> assumption)

theorem frozen_valueF_comp {lam : ℝ} {g : Ω → ℝ} {v : Ω → ι → ℝ} {τ : Equiv.Perm ι}
    (hτ : IsSymmetry g v τ) (P : ι → ℝ) :
    valueF lam g v (fun i => P (τ i)) = valueF lam g v P := by
  first
  | exact @Econ.RationalInattention.valueF_comp ..
  | (apply @Econ.RationalInattention.valueF_comp <;> assumption)

theorem frozen_isSymmetry_mul {g : Ω → ℝ} {v : Ω → ι → ℝ} {σ τ : Equiv.Perm ι}
    (hσ : IsSymmetry g v σ) (hτ : IsSymmetry g v τ) : IsSymmetry g v (σ * τ) := by
  first
  | exact @Econ.RationalInattention.isSymmetry_mul ..
  | (apply @Econ.RationalInattention.isSymmetry_mul <;> assumption)

theorem frozen_gl_const {lam c : ℝ} (hc : 0 < c) (v : ι → ℝ) :
    generalizedLogit lam (fun _ => c) v = softmax lam v := by
  first
  | exact @Econ.RationalInattention.gl_const ..
  | (apply @Econ.RationalInattention.gl_const <;> assumption)

theorem frozen_softmax_optimal_of_symmetric [Nonempty ι] {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ}
    (hg : IsPrior g) {v : Ω → ι → ℝ} (S : Finset (Equiv.Perm ι))
    (hS : ∀ τ ∈ S, IsSymmetry g v τ) (hmul : ∀ σ ∈ S, ∀ τ ∈ S, σ * τ ∈ S)
    (htrans : ∀ i j, ∃ σ ∈ S, σ i = j) :
    IsOptimalRule lam g v fun ω => softmax lam (v ω) := by
  first
  | exact @Econ.RationalInattention.softmax_optimal_of_symmetric ..
  | (apply @Econ.RationalInattention.softmax_optimal_of_symmetric <;> assumption)

theorem frozen_softmax_optimal_of_transitive [Nonempty ι] {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ}
    (hg : IsPrior g) {v : Ω → ι → ℝ} (htrans : ∀ i j, ∃ τ, IsSymmetry g v τ ∧ τ i = j) :
    IsOptimalRule lam g v fun ω => softmax lam (v ω) := by
  first
  | exact @Econ.RationalInattention.softmax_optimal_of_transitive ..
  | (apply @Econ.RationalInattention.softmax_optimal_of_transitive <;> assumption)

theorem frozen_guessPrior_isPrior (n : ℕ) : IsPrior (guessPrior n) := by
  first
  | exact @Econ.RationalInattention.guessPrior_isPrior ..
  | (apply @Econ.RationalInattention.guessPrior_isPrior <;> assumption)

theorem frozen_guess_isSymmetric (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) :
    IsSymmetry (guessPrior n) (guessPayoff n) τ := by
  first
  | exact @Econ.RationalInattention.guess_isSymmetric ..
  | (apply @Econ.RationalInattention.guess_isSymmetric <;> assumption)

theorem frozen_guess_softmax_optimal (n : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    IsOptimalRule lam (guessPrior n) (guessPayoff n) fun ω => softmax lam (guessPayoff n ω) := by
  first
  | exact @Econ.RationalInattention.guess_softmax_optimal ..
  | (apply @Econ.RationalInattention.guess_softmax_optimal <;> assumption)

end RISymmetric

end Econ.Audit.BehavioralXXVI
