/-
# Frozen statements: rational inattention, ambiguity, bounded rationality

Headline statements of `Behavioral/RationalInattention.lean`,
`Behavioral/Ambiguity.lean` and `BoundedRationality/{LevelK,QRE,BerkNash}.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-2.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.Ambiguity
public import EconLean.BoundedRationality.BerkNash
public import EconLean.BoundedRationality.QRE

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Econ.Audit.BehavioralII

open Finset Filter Topology

section RationalInattention
open Econ.RationalInattention Econ.Logit
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem frozen_kl_nonneg [Nonempty ι] {p q : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hqpos : ∀ i, 0 < q i) : 0 ≤ kl p q := by
  apply @Econ.RationalInattention.kl_nonneg <;> assumption

theorem frozen_avgKL_eq (g : Ω → ℝ) (p : Ω → ι → ℝ) (Q : ι → ℝ) :
    avgKL g p Q = mutualInfo g p + kl (marginal g p) Q := by
  apply @Econ.RationalInattention.avgKL_eq <;> assumption

theorem frozen_mutualInfo_le_avgKL [Nonempty ι] {g : Ω → ℝ} (hg : IsPrior g) {p : Ω → ι → ℝ}
    (hp : IsRule p) {Q : ι → ℝ} (hQ : IsProb Q) (hQpos : ∀ i, 0 < Q i) :
    mutualInfo g p ≤ avgKL g p Q := by
  apply @Econ.RationalInattention.mutualInfo_le_avgKL <;> assumption

theorem frozen_optimal_is_generalizedLogit [DecidableEq Ω] {lam : ℝ} (hlam : 0 < lam)
    {g : Ω → ℝ} (hg : IsPrior g) {v : Ω → ι → ℝ} {p : Ω → ι → ℝ}
    (hopt : IsOptimalRule lam g v p) (ω₀ : Ω) :
    p ω₀ = generalizedLogit lam (marginal g p) (v ω₀) := by
  apply @Econ.RationalInattention.optimal_is_generalizedLogit <;> assumption

theorem frozen_optimal_is_softmax_of_uniform [Nonempty ι] [DecidableEq Ω] {lam : ℝ} (hlam : 0 < lam)
    {g : Ω → ℝ} (hg : IsPrior g) {v : Ω → ι → ℝ} {p : Ω → ι → ℝ}
    (hopt : IsOptimalRule lam g v p) {c : ℝ} (hunif : ∀ i, marginal g p i = c)
    (ω : Ω) : p ω = softmax lam (v ω) := by
  apply @Econ.RationalInattention.optimal_is_softmax_of_uniform <;> assumption

end RationalInattention

section Ambiguity
open Econ.Ambiguity
variable {S : Type*} [Fintype S]

theorem frozen_meu_le_eu (C : Finset (S → ℝ)) (hC : C.Nonempty) (f : S → ℝ) {π : S → ℝ} (hπ : π ∈ C) :
    meu C hC f ≤ eu π f := by
  apply @Econ.Ambiguity.meu_le_eu <;> assumption

theorem frozen_meu_mono (C : Finset (S → ℝ)) (hC : C.Nonempty) (hnn : ∀ π ∈ C, ∀ s, 0 ≤ π s)
    {f g : S → ℝ} (h : ∀ s, f s ≤ g s) : meu C hC f ≤ meu C hC g := by
  apply @Econ.Ambiguity.meu_mono <;> assumption

theorem frozen_meu_mix_ge (C : Finset (S → ℝ)) (hC : C.Nonempty) (f g : S → ℝ) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    α * meu C hC f + (1 - α) * meu C hC g ≤ meu C hC (fun s => α * f s + (1 - α) * g s) := by
  apply @Econ.Ambiguity.meu_mix_ge <;> assumption

theorem frozen_meu_mix_const (C : Finset (S → ℝ)) (hC : C.Nonempty) (hsum : ∀ π ∈ C, ∑ s, π s = 1)
    (f : S → ℝ) (α c : ℝ) (h0 : 0 ≤ α) :
    meu C hC (fun s => α * f s + (1 - α) * c) = α * meu C hC f + (1 - α) * c := by
  apply @Econ.Ambiguity.meu_mix_const <;> assumption

theorem frozen_ellsberg_not_seu : ¬ ∃ π : Fin 3 → ℝ,
    eu π betB < eu π betR ∧ eu π betRY < eu π betBY := by
  apply @Econ.Ambiguity.ellsberg_not_seu <;> assumption

theorem frozen_ellsberg_meu :
    meu ellsbergPriors ellsbergPriors_nonempty betB <
      meu ellsbergPriors ellsbergPriors_nonempty betR ∧
    meu ellsbergPriors ellsbergPriors_nonempty betRY <
      meu ellsbergPriors ellsbergPriors_nonempty betBY := by
  apply @Econ.Ambiguity.ellsberg_meu <;> assumption

end Ambiguity

section LevelK
open Econ.BoundedRationality
variable {I : Type*} [DecidableEq I] (G : FiniteGame I)

theorem frozen_exists_levelKPath [∀ i, Nonempty (G.A i)] (a₀ : ∀ i, G.A i) :
    ∃ L, L 0 = a₀ ∧ IsLevelKPath G L := by
  apply @Econ.BoundedRationality.exists_levelKPath <;> assumption

theorem frozen_isPureNash_of_levelK_fixed {L : ℕ → ∀ i, G.A i} (hL : IsLevelKPath G L) {k : ℕ}
    (hfix : L (k + 1) = L k) : IsPureNash G (L k) := by
  apply @Econ.BoundedRationality.isPureNash_of_levelK_fixed <;> assumption

theorem frozen_levelK_eq_of_strictNash {L : ℕ → ∀ i, G.A i} (hL : IsLevelKPath G L)
    (hstrict : IsStrictNash G (L 0)) (k : ℕ) : L k = L 0 := by
  apply @Econ.BoundedRationality.levelK_eq_of_strictNash <;> assumption

theorem frozen_levelK_guess (p : ℝ) (k : ℕ) : levelKGuess p k = 50 * p ^ k := by
  apply @Econ.BoundedRationality.levelK_guess <;> assumption

theorem frozen_levelK_guess_tendsto {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    Tendsto (levelKGuess p) atTop (𝓝 0) := by
  apply @Econ.BoundedRationality.levelK_guess_tendsto <;> assumption

theorem frozen_chGuess_pos {p : ℝ} (hp : 0 < p) {f : ℕ → ℝ} (hf : ∀ j, 0 < f j) (k : ℕ) :
    0 < chGuess p f k := by
  apply @Econ.BoundedRationality.chGuess_pos <;> assumption

theorem frozen_chGuess_strictAnti {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {f : ℕ → ℝ}
    (hf : ∀ j, 0 < f j) : StrictAnti (chGuess p f) := by
  apply @Econ.BoundedRationality.chGuess_strictAnti <;> assumption

end LevelK

section QRE
open Econ.BoundedRationality
variable {I : Type*} [Fintype I] [DecidableEq I] (G : FiniteGame I)

theorem frozen_qre_lambda_zero {σ : ∀ i, G.A i → ℝ} (h : IsLogitQRE G 0 σ) (i : I) (b : G.A i) :
    σ i b = 1 / Fintype.card (G.A i) := by
  apply @Econ.BoundedRationality.qre_lambda_zero <;> assumption

theorem frozen_isNash_of_tendsto_qre [∀ i, Nonempty (G.A i)] {lams : ℕ → ℝ} (hlam : Tendsto lams atTop atTop)
    {σs : ℕ → ∀ i, G.A i → ℝ} (hqre : ∀ n, IsLogitQRE G (lams n) (σs n))
    {σ : ∀ i, G.A i → ℝ} (hconv : ∀ i b, Tendsto (fun n => σs n i b) atTop (𝓝 (σ i b))) :
    IsMixedNash G σ := by
  apply @Econ.BoundedRationality.isNash_of_tendsto_qre <;> assumption

theorem frozen_qre2x2_exists (lam : ℝ) (R C : Fin 2 → Fin 2 → ℝ) :
    ∃ p q, p ∈ Set.Ioo (0 : ℝ) 1 ∧ q ∈ Set.Ioo (0 : ℝ) 1 ∧ IsQRE2x2 lam R C p q := by
  apply @Econ.BoundedRationality.qre2x2_exists <;> assumption

theorem frozen_isLogitQRE_of_qre2x2 {lam : ℝ} {R C : Fin 2 → Fin 2 → ℝ} {p q : ℝ}
    (h : IsQRE2x2 lam R C p q) : IsLogitQRE (game2x2 R C) lam (profile2x2 R C p q) := by
  apply @Econ.BoundedRationality.isLogitQRE_of_qre2x2 <;> assumption

theorem frozen_exists_isLogitQRE_2x2 (lam : ℝ) (R C : Fin 2 → Fin 2 → ℝ) :
    ∃ σ, IsLogitQRE (game2x2 R C) lam σ := by
  apply @Econ.BoundedRationality.exists_isLogitQRE_2x2 <;> assumption

theorem frozen_uniform_isLogitQRE_zero :
    IsLogitQRE G 0 (fun i _ => 1 / Fintype.card (G.A i)) := by
  apply @Econ.BoundedRationality.uniform_isLogitQRE_zero <;> assumption

end QRE

section BerkNash
open Econ.BoundedRationality.SubjectiveProblem Econ.BoundedRationality Econ.Logit Econ.RationalInattention
variable {X Y Θ : Type*} [Fintype X] [Fintype Y] [Fintype Θ] (M : SubjectiveProblem X Y Θ)

theorem frozen_K_nonneg [Nonempty Y] {σ : X → ℝ} (hσ : IsProb σ) (θ : Θ) : 0 ≤ M.K σ θ := by
  apply @Econ.BoundedRationality.SubjectiveProblem.K_nonneg <;> assumption

theorem frozen_K_correct [Nonempty Y] {θs : Θ} (h : M.CorrectAt θs) {σ : X → ℝ} (hσ : IsProb σ) :
    M.K σ θs = 0 ∧ ∀ θ, M.K σ θs ≤ M.K σ θ := by
  apply @Econ.BoundedRationality.SubjectiveProblem.K_correct <;> assumption

theorem frozen_isBerkNash_of_correct [Nonempty Y] [DecidableEq Θ] {θs : Θ} (h : M.CorrectAt θs)
    {σ : X → ℝ} (hσ : M.IsOptimal σ) : M.IsBerkNash σ (pointBelief θs) := by
  apply @Econ.BoundedRationality.SubjectiveProblem.isBerkNash_of_correct <;> assumption

theorem frozen_optimal_of_isBerkNash [Nonempty Y] {θs : Θ} (h : M.CorrectAt θs) {σ : X → ℝ}
    {μ : Θ → ℝ} (hBN : M.IsBerkNash σ μ) (hid : M.Identified σ) : M.IsOptimal σ := by
  apply @Econ.BoundedRationality.SubjectiveProblem.optimal_of_isBerkNash <;> assumption

theorem frozen_example1_misspecified (θ : Fin 2) : ¬ example1.CorrectAt θ := by
  apply @Econ.BoundedRationality.SubjectiveProblem.example1_misspecified <;> assumption

theorem frozen_misspecified_example :
    example1.IsBerkNash (fun x => if x = 0 then 1 else 0) (fun θ => if θ = 1 then 1 else 0) ∧
      example1.trueEU 0 < example1.trueEU 1 := by
  apply @Econ.BoundedRationality.SubjectiveProblem.misspecified_example <;> assumption

end BerkNash

end Econ.Audit.BehavioralII
