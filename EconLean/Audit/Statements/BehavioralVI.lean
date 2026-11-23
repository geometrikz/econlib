/-
# Frozen statements: behavioral round 6

Headline statements of `Behavioral/ForwardGuidanceGE.lean`,
`Behavioral/CreditCycles.lean`, `Behavioral/Satisficing.lean`,
`Behavioral/ChoiceWelfare.lean`, `Behavioral/SmoothAmbiguity.lean` and
`Behavioral/LimitedAttention.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-6.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.ForwardGuidanceGE
public import EconLean.Behavioral.CreditCycles
public import EconLean.Behavioral.Satisficing
public import EconLean.Behavioral.ChoiceWelfare
public import EconLean.Behavioral.SmoothAmbiguity
public import EconLean.Behavioral.LimitedAttention

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralVI

section ForwardGuidanceGE
open Econ.CognitiveNK Econ.CognitiveNK.Model Filter Topology
variable (E : Econ.CognitiveNK.Model)

theorem frozen_fgGE_response {T : ℕ} {x p : ℕ → ℝ} (h : E.IsRatePath (cut T) x p)
    (hx : x (T + 1) = 0) (hp : p (T + 1) = 0) : (x 0, p 0) = E.response T := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_response ..
  | (apply @Econ.CognitiveNK.Model.fgGE_response <;> assumption)

theorem frozen_fgGE_path_exists (T : ℕ) :
    ∃ x p : ℕ → ℝ, E.IsRatePath (cut T) x p ∧ x (T + 1) = 0 ∧ p (T + 1) = 0 := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_path_exists ..
  | (apply @Econ.CognitiveNK.Model.fgGE_path_exists <;> assumption)

theorem frozen_fgGE_puzzle_bound (hM : E.M = 1) (hMf : E.Mf = 1) (T : ℕ) :
    1 / E.σ + T * (E.κ / E.σ ^ 2) ≤ (E.response T).1 ∧ E.κ / E.σ ≤ (E.response T).2 := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_puzzle_bound ..
  | (apply @Econ.CognitiveNK.Model.fgGE_puzzle_bound <;> assumption)

theorem frozen_fgGE_puzzle (hM : E.M = 1) (hMf : E.Mf = 1) :
    Tendsto (fun T => (E.response T).1) atTop atTop := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_puzzle ..
  | (apply @Econ.CognitiveNK.Model.fgGE_puzzle <;> assumption)

theorem frozen_fgGE_vanishes (h : E.κ < E.σ * (1 - E.M) * (1 - E.β * E.Mf)) :
    Tendsto (fun T => (E.response T).1) atTop (𝓝 0) ∧
      Tendsto (fun T => (E.response T).2) atTop (𝓝 0) := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_vanishes ..
  | (apply @Econ.CognitiveNK.Model.fgGE_vanishes <;> assumption)

theorem frozen_fgGE_not_vanishes (h : E.σ * (1 - E.M) * (1 - E.β * E.Mf) ≤ E.κ) :
    ¬ Tendsto (fun T => (E.response T).1) atTop (𝓝 0) := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_not_vanishes ..
  | (apply @Econ.CognitiveNK.Model.fgGE_not_vanishes <;> assumption)

theorem frozen_fgGE_vanishes_iff : Tendsto (fun T => (E.response T).1) atTop (𝓝 0) ↔
    E.κ < E.σ * (1 - E.M) * (1 - E.β * E.Mf) := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_vanishes_iff ..
  | (apply @Econ.CognitiveNK.Model.fgGE_vanishes_iff <;> assumption)

theorem frozen_fgGE_vanishes_iff_determinate (hπ : E.φπ = 0) (hx : E.φx = 0) :
    Tendsto (fun T => (E.response T).1) atTop (𝓝 0) ↔ E.Determinate := by
  first
  | exact @Econ.CognitiveNK.Model.fgGE_vanishes_iff_determinate ..
  | (apply @Econ.CognitiveNK.Model.fgGE_vanishes_iff_determinate <;> assumption)

end ForwardGuidanceGE

section CreditCycles
open Econ.CreditCycles Econ.Diagnostic Econ.BeliefRule


theorem frozen_spreadIRF_eq (χ θ ρ : ℝ) (k : ℕ) :
    spreadIRF χ θ ρ k = -χ * ((if k = 0 then 1 + θ else 1) * ρ ^ (k + 1)) := by
  first
  | exact @Econ.CreditCycles.spreadIRF_eq ..
  | (apply @Econ.CreditCycles.spreadIRF_eq <;> assumption)

theorem frozen_investIRF_eq (α θ ρ : ℝ) (k : ℕ) :
    investIRF α θ ρ k = (if k = 0 then 1 + θ else 1) * ρ ^ (k + 1) / (1 - α) := by
  first
  | exact @Econ.CreditCycles.investIRF_eq ..
  | (apply @Econ.CreditCycles.investIRF_eq <;> assumption)

theorem frozen_spread_too_low {χ θ ρ : ℝ} (hχ : 0 < χ) (hθ : 0 < θ) (hρ : 0 < ρ) :
    spreadIRF χ θ ρ 0 < spreadIRF χ 0 ρ 0 := by
  first
  | exact @Econ.CreditCycles.spread_too_low ..
  | (apply @Econ.CreditCycles.spread_too_low <;> assumption)

theorem frozen_invest_boom {α θ ρ : ℝ} (hα : α < 1) (hθ : 0 < θ) (hρ : 0 < ρ) :
    investIRF α 0 ρ 0 < investIRF α θ ρ 0 := by
  first
  | exact @Econ.CreditCycles.invest_boom ..
  | (apply @Econ.CreditCycles.invest_boom <;> assumption)

theorem frozen_spread_reversal (χ θ ρ : ℝ) :
    (spreadIRF χ θ ρ 1 - spreadIRF χ θ ρ 0) - (spreadIRF χ 0 ρ 1 - spreadIRF χ 0 ρ 0) =
      χ * θ * ρ := by
  first
  | exact @Econ.CreditCycles.spread_reversal ..
  | (apply @Econ.CreditCycles.spread_reversal <;> assumption)

theorem frozen_invest_bust {α : ℝ} (hα : α < 1) (θ ρ : ℝ) :
    (investIRF α θ ρ 1 - investIRF α θ ρ 0) - (investIRF α 0 ρ 1 - investIRF α 0 ρ 0) =
      -(θ * ρ / (1 - α)) := by
  first
  | exact @Econ.CreditCycles.invest_bust ..
  | (apply @Econ.CreditCycles.invest_bust <;> assumption)

theorem frozen_invest_bust_lt {α θ ρ : ℝ} (hα : α < 1) (hθ : 0 < θ) (hρ : 0 < ρ) :
    investIRF α θ ρ 1 - investIRF α θ ρ 0 < investIRF α 0 ρ 1 - investIRF α 0 ρ 0 := by
  first
  | exact @Econ.CreditCycles.invest_bust_lt ..
  | (apply @Econ.CreditCycles.invest_bust_lt <;> assumption)

theorem frozen_spread_reversal_pos {χ θ ρ : ℝ} (hχ : 0 < χ) (hθ : 0 < θ) (hρ : 0 < ρ) :
    spreadIRF χ 0 ρ 1 - spreadIRF χ 0 ρ 0 < spreadIRF χ θ ρ 1 - spreadIRF χ θ ρ 0 := by
  first
  | exact @Econ.CreditCycles.spread_reversal_pos ..
  | (apply @Econ.CreditCycles.spread_reversal_pos <;> assumption)

theorem frozen_condExp_spreadNext (χ θ ρ : ℝ) :
    condExp (spreadNext χ θ ρ) = ![-χ * ρ ^ 4, -χ * ρ ^ 3, -χ * ρ ^ 2, 0] := by
  first
  | exact @Econ.CreditCycles.condExp_spreadNext ..
  | (apply @Econ.CreditCycles.condExp_spreadNext <;> assumption)

theorem frozen_spread_sentiment (χ θ ρ : ℝ) :
    spread χ θ ρ - spread χ 0 ρ = (-χ * θ * ρ) • εt := by
  first
  | exact @Econ.CreditCycles.spread_sentiment ..
  | (apply @Econ.CreditCycles.spread_sentiment <;> assumption)

theorem frozen_expected_spread_change_eq (χ θ ρ : ℝ) :
    (condExp (spreadNext χ θ ρ) - spread χ θ ρ) - (condExp (spreadNext χ 0 ρ) - spread χ 0 ρ) =
      (χ * θ * ρ) • εt := by
  first
  | exact @Econ.CreditCycles.expected_spread_change_eq ..
  | (apply @Econ.CreditCycles.expected_spread_change_eq <;> assumption)

theorem frozen_cov_expected_change {χ θ ρ v s2 : ℝ} (hχ : 0 < χ) (hθ : 0 < θ) (hρ : 0 < ρ)
    (hs : 0 < s2) :
    0 < cov v s2 ((condExp (spreadNext χ θ ρ) - spread χ θ ρ) -
      (condExp (spreadNext χ 0 ρ) - spread χ 0 ρ)) εt ∧
    cov v s2 ((condExp (spreadNext χ θ ρ) - spread χ θ ρ) -
      (condExp (spreadNext χ 0 ρ) - spread χ 0 ρ)) (spread χ θ ρ - spread χ 0 ρ) < 0 := by
  first
  | exact @Econ.CreditCycles.cov_expected_change ..
  | (apply @Econ.CreditCycles.cov_expected_change <;> assumption)

end CreditCycles

section Satisficing
open Econ.Satisficing
variable {n : ℕ}

theorem frozen_satisfice_mem (u : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    satisfice u v S hS ∈ S := by
  first
  | exact @Econ.Satisficing.satisfice_mem ..
  | (apply @Econ.Satisficing.satisfice_mem <;> assumption)

theorem frozen_rank_injective (u : Fin n → ℝ) (v : ℝ) : Function.Injective (rank u v) := by
  first
  | exact @Econ.Satisficing.rank_injective ..
  | (apply @Econ.Satisficing.rank_injective <;> assumption)

theorem frozen_satisfice_isMax (u : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {y : Fin n} (hy : y ∈ S) (hne : y ≠ satisfice u v S hS) :
    rank u v y < rank u v (satisfice u v S hS) := by
  first
  | exact @Econ.Satisficing.satisfice_isMax ..
  | (apply @Econ.Satisficing.satisfice_isMax <;> assumption)

theorem frozen_satisfice_warp (u : Fin n → ℝ) (v : ℝ) {S T : Finset (Fin n)} (hS : S.Nonempty)
    (hT : T.Nonempty) {x y : Fin n} (hxy : x ≠ y) (hyS : y ∈ S) (hxT : x ∈ T)
    (hx : satisfice u v S hS = x) : satisfice u v T hT ≠ y := by
  first
  | exact @Econ.Satisficing.satisfice_warp ..
  | (apply @Econ.Satisficing.satisfice_warp <;> assumption)

theorem frozen_satisfice_ne_argmax :
    satisfice (n := 2) ![1, 2] 1 Finset.univ Finset.univ_nonempty = 0 ∧
      (![1, 2] : Fin 2 → ℝ) 0 < ![1, 2] 1 := by
  first
  | exact @Econ.Satisficing.satisfice_ne_argmax ..
  | (apply @Econ.Satisficing.satisfice_ne_argmax <;> assumption)

end Satisficing

section ChoiceWelfare
open Econ.ChoiceWelfare Econ.ChoiceWelfare.Data
variable {X G : Type*} [DecidableEq X] (D : Econ.ChoiceWelfare.Data X G)

theorem frozen_chosen_isWeakOptimum {g : G} {x : X} (hx : x ∈ D.C g) :
    D.IsWeakOptimum (D.menu g) x := by
  first
  | exact @Econ.ChoiceWelfare.Data.chosen_isWeakOptimum ..
  | (apply @Econ.ChoiceWelfare.Data.chosen_isWeakOptimum <;> assumption)

theorem frozen_exists_weak_optimum (hR : D.Rich) {S : Finset X} (hS : S.Nonempty) :
    ∃ x, D.IsWeakOptimum S x := by
  first
  | exact @Econ.ChoiceWelfare.Data.exists_weak_optimum ..
  | (apply @Econ.ChoiceWelfare.Data.exists_weak_optimum <;> assumption)

theorem frozen_pstar_acyclic (hR : D.Rich) (l : List X) (hl : l ≠ [])
    (hcyc : ∀ y ∈ l, ∃ z ∈ l, D.Pstar z y) : False := by
  classical
  first
  | exact @Econ.ChoiceWelfare.Data.pstar_acyclic ..
  | (apply @Econ.ChoiceWelfare.Data.pstar_acyclic <;> assumption)
  | exact Econ.ChoiceWelfare.Data.pstar_acyclic D hR l hl hcyc

theorem frozen_pstar_asymm (hR : D.Rich) {x y : X} (h : D.Pstar x y) : ¬ D.Pstar y x := by
  first
  | exact @Econ.ChoiceWelfare.Data.pstar_asymm ..
  | (apply @Econ.ChoiceWelfare.Data.pstar_asymm <;> assumption)

theorem frozen_pstar_iff_of_utility (hR : D.Rich) {u : X → ℝ}
    (hC : ∀ g, D.C g = {x | x ∈ D.menu g ∧ ∀ y ∈ D.menu g, u y ≤ u x}) (x y : X) :
    D.Pstar x y ↔ u y < u x := by
  first
  | exact @Econ.ChoiceWelfare.Data.pstar_iff_of_utility ..
  | (apply @Econ.ChoiceWelfare.Data.pstar_iff_of_utility <;> assumption)

theorem frozen_frame_ambiguity {a b : X} {g₁ g₂ : G} (ha : a ∈ D.C g₁) (hb₁ : b ∈ D.menu g₁)
    (hb : b ∈ D.C g₂) (ha₂ : a ∈ D.menu g₂) : ¬ D.Pstar a b ∧ ¬ D.Pstar b a := by
  first
  | exact @Econ.ChoiceWelfare.Data.frame_ambiguity ..
  | (apply @Econ.ChoiceWelfare.Data.frame_ambiguity <;> assumption)

end ChoiceWelfare

section SmoothAmbiguity
open Econ.SmoothAmbiguity Finset
variable {S ι : Type*} [Fintype S] [Fintype ι]

theorem frozen_V_le_reduced {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {π : ι → ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1) (p : ι → S → ℝ) (f : S → ℝ) :
    V φ π p f ≤ φ (reduced π p f) := by
  first
  | exact @Econ.SmoothAmbiguity.V_le_reduced ..
  | (apply @Econ.SmoothAmbiguity.V_le_reduced <;> assumption)

theorem frozen_concaveOn_of_averse {φ : ℝ → ℝ}
    (h : ∀ (π : Fin 2 → ℝ), (∀ i, 0 ≤ π i) → ∑ i, π i = 1 → ∀ (p : Fin 2 → Fin 2 → ℝ)
      (f : Fin 2 → ℝ), (∀ i s, 0 ≤ p i s) → (∀ i, ∑ s, p i s = 1) →
      V φ π p f ≤ φ (reduced π p f)) :
    ConcaveOn ℝ Set.univ φ := by
  first
  | exact @Econ.SmoothAmbiguity.concaveOn_of_averse ..
  | (apply @Econ.SmoothAmbiguity.concaveOn_of_averse <;> assumption)

theorem frozen_V_mix_ge {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (p : ι → S → ℝ) (f g : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α * V φ π p f + (1 - α) * V φ π p g ≤ V φ π p (fun s => α * f s + (1 - α) * g s) := by
  first
  | exact @Econ.SmoothAmbiguity.V_mix_ge ..
  | (apply @Econ.SmoothAmbiguity.V_mix_ge <;> assumption)

theorem frozen_hedging {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (p : ι → S → ℝ) {f g : S → ℝ} (hfg : V φ π p f = V φ π p g) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : V φ π p f ≤ V φ π p (fun s => α * f s + (1 - α) * g s) := by
  first
  | exact @Econ.SmoothAmbiguity.hedging ..
  | (apply @Econ.SmoothAmbiguity.hedging <;> assumption)

theorem frozen_V_linear {π : ι → ℝ} (hπ1 : ∑ i, π i = 1) (p : ι → S → ℝ) (f : S → ℝ) (a b : ℝ) :
    V (fun x => a + b * x) π p f = a + b * reduced π p f := by
  first
  | exact @Econ.SmoothAmbiguity.V_linear ..
  | (apply @Econ.SmoothAmbiguity.V_linear <;> assumption)

end SmoothAmbiguity

section LimitedAttention
open Econ.LimitedAttention
variable {X : Type*} [DecidableEq X] {c : Finset X → X} {u : X → ℕ} {Γ : Finset X → Finset X}

theorem frozen_mem_attention_of_change (h : IsCLA c u Γ) {T : Finset X} {x : X} (hx : x ∈ T)
    (hT : (T.erase x).Nonempty) (hch : c T ≠ c (T.erase x)) : x ∈ Γ T := by
  first
  | exact @Econ.LimitedAttention.mem_attention_of_change ..
  | (apply @Econ.LimitedAttention.mem_attention_of_change <;> assumption)

theorem frozen_revealed_pref (h : IsCLA c u Γ) {T : Finset X} {x : X} (hx : x ∈ T)
    (hxc : c T ≠ x) (hch : c T ≠ c (T.erase x)) : u x < u (c T) := by
  first
  | exact @Econ.LimitedAttention.revealed_pref ..
  | (apply @Econ.LimitedAttention.revealed_pref <;> assumption)

theorem frozen_warpLA_of_cla (h : IsCLA c u Γ) : WARPLA c := by
  first
  | exact @Econ.LimitedAttention.warpLA_of_cla ..
  | (apply @Econ.LimitedAttention.warpLA_of_cla <;> assumption)

theorem frozen_example_cla : IsCLA cex uex Γex := by
  first
  | exact @Econ.LimitedAttention.example_cla ..
  | (apply @Econ.LimitedAttention.example_cla <;> assumption)

theorem frozen_example_violates_warp : ¬ WARP cex := by
  first
  | exact @Econ.LimitedAttention.example_violates_warp ..
  | (apply @Econ.LimitedAttention.example_violates_warp <;> assumption)

end LimitedAttention

end Econ.Audit.BehavioralVI
