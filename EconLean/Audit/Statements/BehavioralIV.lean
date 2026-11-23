/-
# Frozen statements: behavioral round 4

Headline statements of `Behavioral/SocialPreferences.lean`,
`Behavioral/Salience.lean`, `Behavioral/ShroudedAttributes.lean`,
`Behavioral/ContractDesign.lean`, `Behavioral/Falmagne.lean`,
`Information/PersuasionExistence.lean` and the existence results added to
`Behavioral/RationalInattention.lean`, copied verbatim after the adversarial
review (2026-11-23, record in `Audit/REVIEW-behavioral-4.md`). Each is closed
by the library theorem, so if a library statement is ever weakened this file
stops compiling (a stand-in for `leanprover/comparator`). Do not edit a
statement here without a new review.
-/
module

public import EconLean.Behavioral.SocialPreferences
public import EconLean.Behavioral.Salience
public import EconLean.Behavioral.ShroudedAttributes
public import EconLean.Behavioral.ContractDesign
public import EconLean.Behavioral.Falmagne
public import EconLean.Information.PersuasionExistence
public import EconLean.Behavioral.RationalInattention

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Econ.Audit.BehavioralIV

open Finset

section SocialPreferences
open Econ.SocialPreferences
variable {ι : Type*} [Fintype ι]

theorem frozen_accepts_iff {α β s : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hs1 : s ≤ 1) :
    fs2 α β 0 0 ≤ fs2 α β s (1 - s) ↔ α / (1 + 2 * α) ≤ s := by
  first
  | exact @Econ.SocialPreferences.accepts_iff ..
  | (apply @Econ.SocialPreferences.accepts_iff <;> assumption)

theorem frozen_ultimatum_offer_unique {αP βP αR βR : ℝ} (hαP : 0 ≤ αP) (hβP : βP < 1 / 2)
    (hαR : 0 ≤ αR) (hβR : βR ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : s ≠ threshold αR) :
    proposerValue αP βP αR βR s < proposerValue αP βP αR βR (threshold αR) := by
  first
  | exact @Econ.SocialPreferences.ultimatum_offer_unique ..
  | (apply @Econ.SocialPreferences.ultimatum_offer_unique <;> assumption)

theorem frozen_ultimatum_offer_half_unique {αP βP αR βR : ℝ} (hαP : 0 ≤ αP) (hβP : 1 / 2 < βP)
    (hαR : 0 ≤ αR) (hβR : βR ≤ 1) {s : ℝ} (hs1 : s ≤ 1) (hs : s ≠ 1 / 2) :
    proposerValue αP βP αR βR s < proposerValue αP βP αR βR (1 / 2) := by
  first
  | exact @Econ.SocialPreferences.ultimatum_offer_half_unique ..
  | (apply @Econ.SocialPreferences.ultimatum_offer_half_unique <;> assumption)

theorem frozen_dictator_selfish {αD βD g : ℝ} (hαD : 0 ≤ αD) (hβD : βD < 1 / 2) (hg0 : 0 < g) : fs2 αD βD (1 - g) g < fs2 αD βD 1 0 := by
  first
  | exact @Econ.SocialPreferences.dictator_selfish ..
  | (apply @Econ.SocialPreferences.dictator_selfish <;> assumption)

theorem frozen_dictator_half {αD βD g : ℝ} (hαD : 0 ≤ αD) (hβD : 1 / 2 < βD) : fs2 αD βD (1 - g) g ≤ fs2 αD βD (1 / 2) (1 / 2) := by
  first
  | exact @Econ.SocialPreferences.dictator_half ..
  | (apply @Econ.SocialPreferences.dictator_half <;> assumption)

theorem frozen_publicGood_freeRide [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) {α β a y d : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : a + β < 1) (hd : 0 < d) (g : ι → ℝ) (i : ι) :
    fs α β (pgPayoff y a (Function.update g i (g i + d))) i < fs α β (pgPayoff y a g) i := by
  first
  | exact @Econ.SocialPreferences.publicGood_freeRide ..
  | (apply @Econ.SocialPreferences.publicGood_freeRide <;> assumption)

theorem frozen_erc_dictator_le_half {v : ℝ → ℝ → ℝ} (hx : ∀ σ, StrictMono fun x => v x σ)
    (hσ : ∀ x σ σ', σ ≤ σ' → σ' ≤ 1 / 2 → v x σ ≤ v x σ') {g : ℝ} (hg : 1 / 2 < g) :
    erc v ![1 - g, g] 0 < erc v ![1 - (1 / 2 : ℝ), 1 / 2] 0 := by
  first
  | exact @Econ.SocialPreferences.erc_dictator_le_half ..
  | (apply @Econ.SocialPreferences.erc_dictator_le_half <;> assumption)

theorem frozen_erc_rejects_small {v : ℝ → ℝ → ℝ}
    (hc : ContinuousAt (fun p : ℝ × ℝ => v p.1 p.2) (0, 0)) (h0 : v 0 0 < v 0 (1 / 2)) :
    ∃ ε > 0, ∀ s, 0 < s → s < ε → erc v ![1 - s, s] 1 < erc v (![0, 0] : Fin 2 → ℝ) 1 := by
  first
  | exact @Econ.SocialPreferences.erc_rejects_small ..
  | (apply @Econ.SocialPreferences.erc_rejects_small <;> assumption)

end SocialPreferences

section Salience
open Econ.Salience
variable {ι : Type*} [Fintype ι]

theorem frozen_sigma_ordering {θ a a' b' b : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (h1 : a ≤ a')
    (h2 : a' ≤ b') (h3 : b' ≤ b) (hne : a ≠ a' ∨ b' ≠ b) :
    sigma θ a' b' < sigma θ a b := by
  first
  | exact @Econ.Salience.sigma_ordering ..
  | (apply @Econ.Salience.sigma_ordering <;> assumption)

theorem frozen_sigma_dimSens {θ a b ε : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε)
    (hab : a ≠ b) : sigma θ (a + ε) (b + ε) < sigma θ a b := by
  first
  | exact @Econ.Salience.sigma_dimSens ..
  | (apply @Econ.Salience.sigma_dimSens <;> assumption)

theorem frozen_prefers_iff_value [Nonempty ι] {θ δ : ℝ} (hδ : 0 < δ) {π : ι → ℝ}
    (hπ : IsFullProb π) (x y : ι → ℝ) :
    Prefers θ δ π x y ↔ value θ δ π y x ≤ value θ δ π x y := by
  first
  | exact @Econ.Salience.prefers_iff_value ..
  | (apply @Econ.Salience.prefers_iff_value <;> assumption)

theorem frozen_value_one {θ : ℝ} {π : ι → ℝ} (hπ : IsFullProb π) (x y : ι → ℝ) :
    value θ 1 π x y = ∑ s, π s * x s := by
  first
  | exact @Econ.Salience.value_one ..
  | (apply @Econ.Salience.value_one <;> assumption)

theorem frozen_prefers_of_dominates {θ δ : ℝ} (hδ : 0 < δ) {π : ι → ℝ} (hπ : IsFullProb π)
    {x y : ι → ℝ} (hle : ∀ s, y s ≤ x s) {s₀ : ι} (hlt : y s₀ < x s₀) :
    0 < ∑ s, π s * factor θ δ x y s * (x s - y s) := by
  first
  | exact @Econ.Salience.prefers_of_dominates ..
  | (apply @Econ.Salience.prefers_of_dominates <;> assumption)

theorem frozen_longShot_iff {θ δ p G : ℝ} (hθ : 0 < θ) (hδ1 : δ < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hG : 0 < G) :
    0 < ∑ s, probs p s * factor θ δ (longShot G) (sure p G) s * (longShot G s - sure p G s) ↔
      2 * p ^ 2 * G < θ * (1 - 2 * p) := by
  first
  | exact @Econ.Salience.longShot_iff ..
  | (apply @Econ.Salience.longShot_iff <;> assumption)

theorem frozen_longShot_small_p {θ δ G : ℝ} (hθ : 0 < θ) (hδ1 : δ < 1) (hG : 0 < G) :
    ∃ p₀ > 0, ∀ p, 0 < p → p < p₀ →
      0 < ∑ s, probs p s * factor θ δ (longShot G) (sure p G) s *
        (longShot G s - sure p G s) := by
  first
  | exact @Econ.Salience.longShot_small_p ..
  | (apply @Econ.Salience.longShot_small_p <;> assumption)

end Salience

section Shrouding
open Econ.Shrouding
variable (M : Market)

theorem frozen_pStar_lt (h : 0 < M.α * (M.vA - M.cA)) : M.pStar < M.c := by
  first
  | exact @Econ.Shrouding.Market.pStar_lt ..
  | (apply @Econ.Shrouding.Market.pStar_lt <;> assumption)

theorem frozen_shrouded_no_deviation (hα0 : 0 ≤ M.α) (hα1 : M.α ≤ 1)
    (hcurse : M.e - M.cA ≤ M.α * (M.vA - M.cA)) {p pa : ℝ} (hpa : pa ≤ M.vA) :
    M.profitShrouded p pa ≤ 0 := by
  first
  | exact @Econ.Shrouding.Market.shrouded_no_deviation ..
  | (apply @Econ.Shrouding.Market.shrouded_no_deviation <;> assumption)

theorem frozen_curse_of_debiasing (hce : M.cA ≤ M.e) (hcurse : M.e - M.cA < M.α * (M.vA - M.cA))
    {p pa : ℝ} (hattract : p + min pa M.e ≤ M.pStar + M.e) :
    M.profitUnshrouded p pa < 0 := by
  first
  | exact @Econ.Shrouding.Market.curse_of_debiasing ..
  | (apply @Econ.Shrouding.Market.curse_of_debiasing <;> assumption)

theorem frozen_unshroud_profitable (h : M.α * (M.vA - M.cA) < M.e - M.cA) :
    M.pStar + min M.e M.e ≤ M.pStar + M.e ∧ 0 < M.profitUnshrouded M.pStar M.e := by
  first
  | exact @Econ.Shrouding.Market.unshroud_profitable ..
  | (apply @Econ.Shrouding.Market.unshroud_profitable <;> assumption)

end Shrouding

section ContractDesign
open Econ.ContractDesign
variable (G : Gym)

theorem frozen_isMaxOn_pOpt (hopt : G.Region G.pOpt) : IsMaxOn G.profit {p | G.Region p} G.pOpt := by
  first
  | exact @Econ.ContractDesign.Gym.isMaxOn_pOpt ..
  | (apply @Econ.ContractDesign.Gym.isMaxOn_pOpt <;> assumption)

theorem frozen_pOpt_unique (hopt : G.Region G.pOpt) {p : ℝ} (hp : G.Region p) (hne : p ≠ G.pOpt) :
    G.profit p < G.profit G.pOpt := by
  first
  | exact @Econ.ContractDesign.Gym.pOpt_unique ..
  | (apply @Econ.ContractDesign.Gym.pOpt_unique <;> assumption)

theorem frozen_pOpt_lt_cost (hβ : G.β < 1) (hB : 0 < G.δ * G.b) : G.pOpt < G.a := by
  first
  | exact @Econ.ContractDesign.Gym.pOpt_lt_cost ..
  | (apply @Econ.ContractDesign.Gym.pOpt_lt_cost <;> assumption)

theorem frozen_overestimate {p : ℝ} (hp : G.Region p) :
    cdf (G.thrh p) - cdf (G.thr p) = (G.βh - G.β) * G.δ * G.b := by
  first
  | exact @Econ.ContractDesign.Gym.overestimate ..
  | (apply @Econ.ContractDesign.Gym.overestimate <;> assumption)

theorem frozen_profit_lt_of_naive (G' : Gym) (hβ : G'.β = G.β) (hδ : G'.δ = G.δ) (hb : G'.b = G.b)
    (ha : G'.a = G.a) (hu : G'.ū = G.ū) (hlt : G.βh < G'.βh) (hle : G'.βh ≤ 1)
    (hB : 0 < G.δ * G.b) (hopt : G.Region G.pOpt) (hopt' : G'.Region G'.pOpt) :
    G.profit G.pOpt < G'.profit G'.pOpt := by
  first
  | exact @Econ.ContractDesign.Gym.profit_lt_of_naive ..
  | (apply @Econ.ContractDesign.Gym.profit_lt_of_naive <;> assumption)

theorem frozen_welfare_lt {p : ℝ} (hp : G.Region p) (hβ : G.β < G.βh) (hβh : G.βh ≤ 1)
    (hB : 0 < G.δ * G.b) : G.welfare p < G.ū := by
  first
  | exact @Econ.ContractDesign.Gym.welfare_lt ..
  | (apply @Econ.ContractDesign.Gym.welfare_lt <;> assumption)

end ContractDesign

section Falmagne
open Econ.StochasticChoice
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem frozen_sum_bm (P : Finset X → X → ℝ) (A : Finset X) (a : X) :
    ∑ C ∈ (univ \ A).powerset, bm P (A ∪ C) a = P A a := by
  first
  | exact @Econ.StochasticChoice.sum_bm ..
  | (apply @Econ.StochasticChoice.sum_bm <;> assumption)

theorem frozen_falmagne {P : Finset X → X → ℝ} (hP : IsChoiceRule P)
    (hbm : ∀ A a, a ∈ A → 0 ≤ bm P A a) :
    ∃ μ : Ranking X → ℝ, IsRUM μ ∧ ∀ A : Finset X, A.Nonempty → ∀ a, rumP μ A a = P A a := by
  first
  | exact @Econ.StochasticChoice.falmagne ..
  | (apply @Econ.StochasticChoice.falmagne <;> assumption)

theorem frozen_isRUM_iff_bm_nonneg {P : Finset X → X → ℝ} (hP : IsChoiceRule P) :
    (∃ μ : Ranking X → ℝ, IsRUM μ ∧ ∀ A : Finset X, A.Nonempty → ∀ a, rumP μ A a = P A a) ↔
      ∀ A a, a ∈ A → 0 ≤ bm P A a := by
  first
  | exact @Econ.StochasticChoice.isRUM_iff_bm_nonneg ..
  | (apply @Econ.StochasticChoice.isRUM_iff_bm_nonneg <;> assumption)

end Falmagne

section PersuasionExistence
open Econ.Persuasion
variable {Ω : Type*} [Fintype Ω]

theorem frozen_exists_optimal_splitting {v : (Ω → ℝ) → ℝ} (hv : UpperSemicontinuousOn v (beliefs Ω))
    {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    ∃ s : Splitting μ₀, s.K = Fintype.card Ω + 2 ∧ s.value v = V v μ₀ ∧
      ∀ s' : Splitting μ₀, s'.value v ≤ s.value v := by
  first
  | exact @Econ.Persuasion.exists_optimal_splitting ..
  | (apply @Econ.Persuasion.exists_optimal_splitting <;> assumption)

theorem frozen_exists_optimal_signal {v : (Ω → ℝ) → ℝ} (hv : UpperSemicontinuousOn v (beliefs Ω))
    {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    ∃ σ : Signal Ω (Fin (Fintype.card Ω + 2)), signalValue v μ₀ σ = V v μ₀ := by
  first
  | exact @Econ.Persuasion.exists_optimal_signal ..
  | (apply @Econ.Persuasion.exists_optimal_signal <;> assumption)

theorem frozen_prosecutor_exists_optimal :
    ∃ σ : Signal (Fin 2) (Fin (Fintype.card (Fin 2) + 2)), signalValue convict prior σ = 3 / 5 := by
  first
  | exact @Econ.Persuasion.prosecutor_exists_optimal ..
  | (apply @Econ.Persuasion.prosecutor_exists_optimal <;> assumption)

end PersuasionExistence

section RationalInattention
open Econ.RationalInattention Econ.Logit
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem frozen_exists_isOptimalRule [Nonempty ι] (lam : ℝ) (g : Ω → ℝ) (v : Ω → ι → ℝ) :
    ∃ p, IsOptimalRule lam g v p := by
  first
  | exact @Econ.RationalInattention.exists_isOptimalRule ..
  | (apply @Econ.RationalInattention.exists_isOptimalRule <;> assumption)

theorem frozen_exists_optimal_generalizedLogit [Nonempty ι] [DecidableEq Ω] {lam : ℝ} (hlam : 0 < lam)
    {g : Ω → ℝ} (hg : IsPrior g) (v : Ω → ι → ℝ) :
    ∃ p, IsOptimalRule lam g v p ∧ ∀ ω, p ω = generalizedLogit lam (marginal g p) (v ω) := by
  first
  | exact @Econ.RationalInattention.exists_optimal_generalizedLogit ..
  | (apply @Econ.RationalInattention.exists_optimal_generalizedLogit <;> assumption)

end RationalInattention

end Econ.Audit.BehavioralIV
