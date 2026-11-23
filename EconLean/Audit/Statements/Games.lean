/-
# Frozen statements: game theory (MWG Ch. 7–9)

Headline statements of `Games/*.lean`, copied after the adversarial review recorded in
`Audit/REVIEW-games.md`. Each is closed by the library theorem, so if a library
statement is ever weakened this file stops compiling. Do not edit a statement here
without a new review.
-/
module

public import EconLean.Games.Strategic
public import EconLean.Games.Mixed
public import EconLean.Games.ZeroSum
public import EconLean.Games.Correlated
public import EconLean.Games.Rationalizability
public import EconLean.Games.Bayesian
public import EconLean.Games.Extensive

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Function Econ Econ.GameTree

section Strategic
variable {I : Type*} [DecidableEq I] {S : I → Type*}

theorem frozen_isNash_iff_bestResponse (u : I → (∀ j, S j) → ℝ) (s : ∀ j, S j) :
    IsNash u s ↔ ∀ i, IsBestResponse u i s (s i) :=
  isNash_iff_bestResponse u s

theorem frozen_isNash_of_dominant {u : I → (∀ j, S j) → ℝ} {s : ∀ j, S j}
    (h : ∀ i, IsDominant u i (s i)) : IsNash u s :=
  isNash_of_dominant h

theorem frozen_isNash_mem_isd {u : I → (∀ j, S j) → ℝ} {s : ∀ j, S j} (hs : IsNash u s) :
    ∀ n i, s i ∈ isd u n i :=
  isNash_mem_isd hs

theorem frozen_isNash_of_isd_singleton [∀ i, Fintype (S i)] {u : I → (∀ j, S j) → ℝ}
    {s : ∀ j, S j} {n : ℕ} (hn : ∀ i, isd u n i = {s i}) : IsNash u s :=
  isNash_of_isd_singleton hn

end Strategic

section Mixed
variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

theorem frozen_isMixedNash_iff_pure {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (hσ : IsMixedProfile σ) :
    IsMixedNash u σ ↔ ∀ i t, pureDev u σ i t ≤ mixedPayoff u σ i :=
  isMixedNash_iff_pure hσ

theorem frozen_IsMixedNash_eq_of_pos {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) {i : I} {t : S i} (ht : 0 < σ i t) :
    pureDev u σ i t = mixedPayoff u σ i :=
  h.eq_of_pos ht

theorem frozen_isMixedNash_pureProfile_iff (u : I → (∀ j, S j) → ℝ) (s : ∀ i, S i) :
    IsMixedNash u (pureProfile s) ↔ IsNash u s :=
  isMixedNash_pureProfile_iff u s

theorem frozen_exists_isMixedNash [∀ i, Nonempty (S i)] (u : I → (∀ j, S j) → ℝ) :
    ∃ σ, IsMixedNash u σ :=
  exists_isMixedNash u

theorem frozen_isCorrelatedEq_of_isMixedNash {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) : IsCorrelatedEq u (profileProb σ) :=
  isCorrelatedEq_of_isMixedNash h

theorem frozen_convex_correlatedEq (u : I → (∀ j, S j) → ℝ) :
    Convex ℝ {μ | IsCorrelatedEq u μ} :=
  convex_correlatedEq u

theorem frozen_rationalizable_of_isMixedNash {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) {i : I} {t : S i} (ht : 0 < σ i t) : Rationalizable u i t :=
  rationalizable_of_isMixedNash h ht

theorem frozen_Rationalizable_mem_isdMixed {u : I → (∀ j, S j) → ℝ} {i : I} {t : S i}
    (h : Rationalizable u i t) (n : ℕ) : t ∈ isdMixed u n i :=
  h.mem_isdMixed n

theorem frozen_Rationalizable_mem_isd {u : I → (∀ j, S j) → ℝ} {i : I} {t : S i}
    (h : Rationalizable u i t) (n : ℕ) : t ∈ isd u n i :=
  h.mem_isd n

end Mixed

section ZeroSum
variable {m n : Type*} [Fintype m] [Fintype n]

theorem frozen_exists_saddle [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ x y, IsSaddle A x y :=
  exists_saddle A

theorem frozen_exists_unique_value [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃! v, IsValue A v :=
  exists_unique_value A

theorem frozen_IsSaddle_interchange {A : m → n → ℝ} {x x' : m → ℝ} {y y' : n → ℝ}
    (h : IsSaddle A x y) (h' : IsSaddle A x' y') : IsSaddle A x y' :=
  h.interchange h'

end ZeroSum

section Bayesian
variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)] {A : I → Type*}

theorem frozen_isBNE_iff_interim {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} (hp : p ∈ lotteries (∀ j, Θ j)) {s : ∀ i, Θ i → A i} :
    IsBNE u p s ↔ ∀ i θi a, interim u p s i θi a ≤ interim u p s i θi (s i θi) :=
  isBNE_iff_interim hp

theorem frozen_exists_mixed_BNE [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) :
    ∃ σ : ∀ i, (Θ i → A i) → ℝ, IsMixedNash (exAnte u p) σ :=
  exists_mixed_BNE u p

end Bayesian

section Extensive
variable {I : Type*}

theorem frozen_isSPE_iff_noOneShotDeviation (t : GameTree I) (s : Profile t) :
    IsSPE t s ↔ NoOneShotDeviation t s :=
  isSPE_iff_noOneShotDeviation t s

theorem frozen_exists_isSPE (t : GameTree I) : ∃ s, IsSPE t s :=
  exists_isSPE t

theorem frozen_zermelo (t : GameTree Bool)
    (hwl : ∀ p, IsLeafOf p t → (p true = 1 ∧ p false = -1) ∨ (p true = -1 ∧ p false = 1)) :
    ∃ s : Profile t, (∀ s', OnlyDeviates false t s s' → outcome t s' true = 1) ∨
      (∀ s', OnlyDeviates true t s s' → outcome t s' false = 1) :=
  zermelo t hwl

theorem frozen_zermelo_draw (t : GameTree Bool)
    (hl : ∀ p, IsLeafOf p t → p false = -p true ∧ (p true = 1 ∨ p true = 0 ∨ p true = -1)) :
    ∃ s : Profile t, (∀ s', OnlyDeviates false t s s' → outcome t s' true = 1) ∨
      (∀ s', OnlyDeviates true t s s' → outcome t s' false = 1) ∨
      ((∀ s', OnlyDeviates false t s s' → 0 ≤ outcome t s' true) ∧
        (∀ s', OnlyDeviates true t s s' → 0 ≤ outcome t s' false)) :=
  zermelo_draw t hl

end Extensive

end Econ.Audit
