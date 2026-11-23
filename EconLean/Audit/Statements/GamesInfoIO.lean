/-
# Frozen statements: potential and supermodular games, agreement, cascades, cheap talk,
# the second-price auction, Nash implementation, the linear city

Headline statements of `Games/{Potential,Supermodular}`, `Information/{Agreement,Cascades,
CheapTalk}`, `Mechanism/{SecondPrice,Implementation}` and `Partial/Hotelling`, copied after the
adversarial review recorded in `Audit/REVIEW-games-info-io.md`. Each is closed by the library
theorem, so if a library statement is ever weakened this file stops compiling. Do not edit a
statement here without a new review.
-/
module

public import EconLean.Games.Potential
public import EconLean.Games.Supermodular
public import EconLean.Information.Agreement
public import EconLean.Information.Cascades
public import EconLean.Information.CheapTalk
public import EconLean.Mechanism.SecondPrice
public import EconLean.Mechanism.Implementation
public import EconLean.Partial.Hotelling

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Econ.Audit

open Function Finset Econ

section
-- Games/Potential

variable {I : Type*} [DecidableEq I] {S : I → Type*}

theorem frozen_exists_isNash_of_potential [Fintype I] [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {u : I → (∀ j, S j) → ℝ} {Φ : (∀ j, S j) → ℝ} (hΦ : IsOrdinalPotential u Φ) :
    ∃ s, IsNash u s := by
  apply Econ.exists_isNash_of_potential <;> assumption

theorem frozen_not_infinite_improvementPath [Fintype I] [∀ i, Fintype (S i)]
    {u : I → (∀ j, S j) → ℝ} {Φ : (∀ j, S j) → ℝ} (hΦ : IsOrdinalPotential u Φ)
    (f : ℕ → ∀ j, S j) : ¬ IsImprovementPath u f := by
  apply Econ.not_infinite_improvementPath <;> assumption

variable {R : Type*} [Fintype R] [DecidableEq R] [Fintype I]

theorem frozen_congestion_isExactPotential (c : R → ℕ → ℝ) :
    IsExactPotential (S := fun _ : I => Finset R) (congestionPayoff c) (rosenthal c) := by
  apply Econ.congestion_isExactPotential <;> assumption

theorem frozen_congestion_exists_isNash (c : R → ℕ → ℝ) (A : I → Finset (Finset R))
    (hA : ∀ i, (A i).Nonempty) :
    ∃ s : ∀ i, A i, ∀ i (t : A i),
      congestionPayoff c i (update (fun j => (s j : Finset R)) i t) ≤
        congestionPayoff c i (fun j => (s j : Finset R)) := by
  apply Econ.congestion_exists_isNash <;> assumption

end

section
-- Games/Supermodular

variable {I : Type*} [DecidableEq I] {S : I → Type*} [∀ i, LinearOrder (S i)]
  [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]

theorem frozen_greatestBR_mono {u : I → (∀ j, S j) → ℝ} (hu : HasStrategicComplements u) (i : I) :
    Monotone (greatestBR u i) := by
  apply Econ.greatestBR_mono <;> assumption

theorem frozen_supermodular_greatest_nash [Fintype I] {u : I → (∀ j, S j) → ℝ}
    (hu : HasStrategicComplements u) :
    ∃ s, IsNash u s ∧ ∀ s', IsNash u s' → s' ≤ s := by
  apply Econ.supermodular_greatest_nash <;> assumption

theorem frozen_supermodular_least_nash [Fintype I] {u : I → (∀ j, S j) → ℝ}
    (hu : HasStrategicComplements u) :
    ∃ s, IsNash u s ∧ ∀ s', IsNash u s' → s ≤ s' := by
  apply Econ.supermodular_least_nash <;> assumption

end

section
-- Information/Agreement

variable {Ω L : Type*} [Fintype Ω] [DecidableEq L]

theorem frozen_aumann_agreement [DecidableEq Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 < μ ω) {c₁ c₂ : Ω → L}
    {E : Finset Ω} {a b : ℝ} {ω₀ : Ω} {C : Finset Ω} (hω₀ : ω₀ ∈ C)
    (hC₁ : IsSelfEvident c₁ C) (hC₂ : IsSelfEvident c₂ C)
    (ha : ∀ ω ∈ C, posterior μ c₁ E ω = a) (hb : ∀ ω ∈ C, posterior μ c₂ E ω = b) :
    a = b := by
  exact Econ.aumann_agreement hμ hω₀ hC₁ hC₂ ha hb

end

section
-- Information/Cascades

theorem frozen_cascadeAction_eq_bayes {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {h l : ℕ} {d : ℤ}
    {b : Bool} (hd : (h : ℤ) - l = d + signalSign b) :
    cascadeAction d b = true ↔
      (1 / 2 < bayesPost p h l ∨ (bayesPost p h l = 1 / 2 ∧ b = true)) := by
  apply Econ.cascadeAction_eq_bayes <;> assumption

theorem frozen_cascade_absorbing (s : ℕ → Bool) {n : ℕ} (hn : 2 ≤ |cascadeState s n|) :
    ∀ m, n ≤ m → cascadeState s m = cascadeState s n ∧
      cascadePlay s m = decide (0 < cascadeState s n) := by
  apply Econ.cascade_absorbing <;> assumption

theorem frozen_cascade_of_first_two (s : ℕ → Bool) (h : s 0 = s 1) :
    ∀ m, 2 ≤ m → cascadePlay s m = s 0 := by
  apply Econ.cascade_of_first_two <;> assumption

end

section
-- Information/CheapTalk

theorem frozen_midpoint_minimizes {a c : ℝ} (hac : a ≤ c) (y : ℝ) :
    ∫ θ in a..c, ((a + c) / 2 - θ) ^ 2 ≤ ∫ θ in a..c, (y - θ) ^ 2 := by
  apply Econ.midpoint_minimizes <;> assumption

theorem frozen_partitionEq_arbitrage {b : ℝ} {N : ℕ} {a : ℕ → ℝ} (h : IsPartitionEq b N a) {i : ℕ}
    (hi : i + 1 < N) : a (i + 2) - a (i + 1) = a (i + 1) - a i + 4 * b := by
  apply Econ.partitionEq_arbitrage <;> assumption

theorem frozen_partitionEq_closed_form {b : ℝ} {N : ℕ} {a : ℕ → ℝ} (h : IsPartitionEq b N a) :
    ∀ i ≤ N, a i = i * a 1 + 2 * i * (i - 1) * b := by
  apply Econ.partitionEq_closed_form <;> assumption

theorem frozen_partitionEq_exists_iff {b : ℝ} (hb : 0 < b) {N : ℕ} (hN : 0 < N) :
    (∃ a, IsPartitionEq b N a) ↔ 2 * N * (N - 1) * b < 1 := by
  apply Econ.partitionEq_exists_iff <;> assumption

end

section
-- Mechanism/SecondPrice

variable {I : Type*} [Fintype I] [LinearOrder I] [Nontrivial I]

theorem frozen_spa_truthful_dominant (v : I → ℝ) (i : I) :
    IsDominant (fun j => spaPayoff v j) i (v i) := by
  apply Econ.spa_truthful_dominant <;> assumption

theorem frozen_spa_truthful_nash (v : I → ℝ) : IsNash (fun j => spaPayoff v j) v := by
  apply Econ.spa_truthful_nash <;> assumption

end

section
-- Mechanism/Implementation

variable {I Θ X : Type*} [DecidableEq I]

variable [Fintype I] [Nonempty I] {u : I → Θ → X → ℝ} {F : Θ → Set X}

theorem frozen_maskinMonotone_of_nashImplements {M : I → Type*} {u : I → Θ → X → ℝ}
    {F : Θ → Set X} {g : (∀ i, M i) → X} (h : NashImplements u F g) :
    IsMaskinMonotone u F := by
  apply Econ.maskinMonotone_of_nashImplements <;> assumption

theorem frozen_maskin_sufficiency (hn : 3 ≤ Fintype.card I) (hmono : IsMaskinMonotone u F)
    (hnvp : HasNoVetoPower u F) :
    NashImplements (M := fun _ : I => MaskinMsg Θ X) u F (maskinOutcome u F) := by
  apply Econ.maskin_sufficiency <;> assumption

theorem frozen_weakPareto_nashImplements (hn : 3 ≤ Fintype.card I) :
    NashImplements (M := fun _ : I => MaskinMsg Θ X) u (weakPareto u)
      (maskinOutcome u (weakPareto u)) := by
  apply Econ.weakPareto_nashImplements <;> assumption

end

section
-- Partial/Hotelling

theorem frozen_hotelling_nash {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) (ht : 0 < t) :
    (hotellingPrice a b t c - c) *
        hotellingDemand a b t (hotellingPrice a b t c) (hotellingPrice b a t c) =
      hotellingProfit a b t ∧
    (hotellingPrice b a t c - c) *
        (1 - hotellingDemand a b t (hotellingPrice a b t c) (hotellingPrice b a t c)) =
      hotellingProfit b a t ∧
    (∀ p, (p - c) * hotellingDemand a b t p (hotellingPrice b a t c) ≤ hotellingProfit a b t) ∧
    ∀ p, (p - c) * (1 - hotellingDemand a b t (hotellingPrice a b t c) p) ≤
      hotellingProfit b a t := by
  apply Econ.hotelling_nash <;> assumption

theorem frozen_hotelling_max_differentiation {a a' b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haa' : a < a')
    (hab : a' + b < 1) (ht : 0 < t) : hotellingProfit a' b t < hotellingProfit a b t := by
  apply Econ.hotelling_max_differentiation <;> assumption

end

end Econ.Audit
