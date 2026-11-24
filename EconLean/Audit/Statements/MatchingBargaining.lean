/-
# Frozen statements: housing market (TTC), matching with contracts, Rubinstein bargaining

Headline statements of `Matching/{HousingMarket,Contracts}` and `Bargaining/Rubinstein`, copied
after the adversarial review recorded in `Audit/REVIEW-batch7.md`. Each is closed by the
library theorem, so if a library statement is ever weakened this file stops compiling. Do not
edit a statement here without a new review.
-/
module

public import EconLean.Matching.HousingMarket
public import EconLean.Matching.Contracts
public import EconLean.Bargaining.Rubinstein
public import EconLean.Bargaining.RubinsteinGame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Function Finset Econ Filter Topology

section
-- Matching/HousingMarket

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem frozen_ttc_exists (u : N → N → ℝ) : ∃ σ : Equiv.Perm N, IsTTC u σ :=
  Econ.ttc_exists (u := u)

theorem frozen_ttc_in_strictCore {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ : Equiv.Perm N} (hσ : IsTTC u σ) : InStrictCore u σ :=
  Econ.ttc_in_strictCore (u := u) (hu := hu) (σ := σ) (hσ := hσ)

theorem frozen_strictCore_eq_ttc {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ π : Equiv.Perm N} (hσ : IsTTC u σ) (hπ : InStrictCore u π) : π = σ :=
  Econ.strictCore_eq_ttc (u := u) (hu := hu) (σ := σ) (π := π) (hσ := hσ) (hπ := hπ)

theorem frozen_ttc_unique {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ σ' : Equiv.Perm N} (hσ : IsTTC u σ) (hσ' : IsTTC u σ') : σ' = σ :=
  Econ.ttc_unique (u := u) (hu := hu) (σ := σ) (σ' := σ') (hσ := hσ) (hσ' := hσ')

theorem frozen_strictCore_nonempty {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i)) :
    ∃ σ : Equiv.Perm N, InStrictCore u σ ∧ ∀ π, InStrictCore u π → π = σ :=
  Econ.strictCore_nonempty (u := u) (hu := hu)

end

section
-- Matching/Contracts

variable {X : Type*}

theorem frozen_hm_fixedPoint_stable {cD cH : ChoiceFn X} (hsD : cD.Substitutes) (hsH : cH.Substitutes)
    (hiD : cD.IRC) (hiH : cH.IRC) {XD XH : Set X} (hfix : hmMap cD cH (XD, XH) = (XD, XH)) :
    IsStableAlloc cD cH (XD ∩ XH) :=
  Econ.hm_fixedPoint_stable (cD := cD) (cH := cH) (hsD := hsD) (hsH := hsH) (hiD := hiD) (hiH := hiH) (XD := XD) (XH := XH) (hfix := hfix)

theorem frozen_stable_exists {cD cH : ChoiceFn X} (hsD : cD.Substitutes) (hsH : cH.Substitutes)
    (hiD : cD.IRC) (hiH : cH.IRC) : ∃ Y, IsStableAlloc cD cH Y :=
  Econ.stable_exists (cD := cD) (cH := cH) (hsD := hsD) (hsH := hsH) (hiD := hiD) (hiH := hiH)

end

section
-- Bargaining/Rubinstein

theorem frozen_rubinstein_stationary {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1)
    (h₂' : δ₂ < 1) (x y : ℝ) :
    (x = 1 - δ₂ * y ∧ y = 1 - δ₁ * x) ↔ (x = rubinsteinShare δ₁ δ₂ ∧ y = rubinsteinShare δ₂ δ₁) :=
  Econ.rubinstein_stationary (δ₁ := δ₁) (δ₂ := δ₂) (h₁ := h₁) (h₁' := h₁') (h₂' := h₂') (x := x) (y := y)

theorem frozen_shaked_sutton_bounds {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
    {M₁ m₁ M₂ m₂ : ℝ} (hlo₁ : 1 - δ₂ * M₂ ≤ m₁) (hhi₁ : M₁ ≤ 1 - δ₂ * m₂)
    (hlo₂ : 1 - δ₁ * M₁ ≤ m₂) (hhi₂ : M₂ ≤ 1 - δ₁ * m₁) (h₁m : m₁ ≤ M₁) (h₂m : m₂ ≤ M₂) :
    M₁ = rubinsteinShare δ₁ δ₂ ∧ m₁ = rubinsteinShare δ₁ δ₂ ∧
      M₂ = rubinsteinShare δ₂ δ₁ ∧ m₂ = rubinsteinShare δ₂ δ₁ :=
  Econ.shaked_sutton_bounds (δ₁ := δ₁) (δ₂ := δ₂) (h₁ := h₁) (h₁' := h₁') (h₂ := h₂) (h₂' := h₂') (M₁ := M₁) (m₁ := m₁) (M₂ := M₂) (m₂ := m₂) (hlo₁ := hlo₁) (hhi₁ := hhi₁) (hlo₂ := hlo₂) (hhi₂ := hhi₂) (h₁m := h₁m) (h₂m := h₂m)

theorem frozen_rubinsteinShare_mem {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂)
    (h₂' : δ₂ < 1) : 0 < rubinsteinShare δ₁ δ₂ ∧ rubinsteinShare δ₁ δ₂ ≤ 1 :=
  Econ.rubinsteinShare_mem (δ₁ := δ₁) (δ₂ := δ₂) (h₁ := h₁) (h₁' := h₁') (h₂ := h₂) (h₂' := h₂')

theorem frozen_rubinstein_first_mover {δ : ℝ} (h : 0 ≤ δ) (h' : δ < 1) :
    rubinsteinShare δ δ = 1 / (1 + δ) ∧ 1 / 2 < rubinsteinShare δ δ :=
  Econ.rubinstein_first_mover (δ := δ) (h := h) (h' := h')

theorem frozen_rubinstein_patience {δ₁ δ₁' δ₂ δ₂' : ℝ} (h₁ : 0 ≤ δ₁) (h₁₁ : δ₁ ≤ δ₁') (h₁' : δ₁' < 1)
    (h₂ : 0 ≤ δ₂) (h₂₂ : δ₂ ≤ δ₂') (h₂' : δ₂' < 1) :
    rubinsteinShare δ₁ δ₂ ≤ rubinsteinShare δ₁' δ₂ ∧ rubinsteinShare δ₁ δ₂' ≤ rubinsteinShare δ₁ δ₂ :=
  Econ.rubinstein_patience (δ₁ := δ₁) (δ₁' := δ₁') (δ₂ := δ₂) (δ₂' := δ₂') (h₁ := h₁) (h₁₁ := h₁₁) (h₁' := h₁') (h₂ := h₂) (h₂₂ := h₂₂) (h₂' := h₂')

theorem frozen_rubinstein_limit {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    Tendsto (fun Δ : ℝ => rubinsteinShare (Real.exp (-(r₁ * Δ))) (Real.exp (-(r₂ * Δ))))
      (𝓝[>] 0) (𝓝 (r₂ / (r₁ + r₂))) :=
  Econ.rubinstein_limit (r₁ := r₁) (r₂ := r₂) (hr₁ := hr₁) (hr₂ := hr₂)

theorem frozen_rubinstein_symmetric_limit {r : ℝ} (hr : 0 < r) :
    Tendsto (fun Δ : ℝ => rubinsteinShare (Real.exp (-(r * Δ))) (Real.exp (-(r * Δ))))
      (𝓝[>] 0) (𝓝 (1 / 2)) :=
  Econ.rubinstein_symmetric_limit (r := r) (hr := hr)

end

section
-- Matching/HousingMarket (batch 8 additions)

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem frozen_strictCore_agree_below {u u' : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ π : Equiv.Perm N} {r : N → ℕ} (hr : ∀ i, r (σ i) = r i)
    (htop : ∀ i j, r i ≤ r j → u i j ≤ u i (σ i)) (hπ : InStrictCore u' π) {K : ℕ}
    (hagree : ∀ j, r j < K → u' j = u j) : ∀ j, r j < K → π j = σ j :=
  Econ.strictCore_agree_below (u := u) (u' := u') (hu := hu) (σ := σ) (π := π) (r := r) (hr := hr) (htop := htop) (hπ := hπ) (K := K) (hagree := hagree)

theorem frozen_ttc_strategyproof {u u' : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {i : N} (hu' : Function.Injective (u' i)) (hother : ∀ j, j ≠ i → u' j = u j)
    {σ σ' : Equiv.Perm N} (hσ : IsTTC u σ) (hσ' : IsTTC u' σ') : u i (σ' i) ≤ u i (σ i) :=
  Econ.ttc_strategyproof (u := u) (u' := u') (hu := hu) (i := i) (hu' := hu') (hother := hother) (σ := σ) (σ' := σ') (hσ := hσ) (hσ' := hσ')

theorem frozen_ttc_pareto {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i)) {σ : Equiv.Perm N}
    (hσ : IsTTC u σ) (π : Equiv.Perm N) :
    ¬ ((∀ j, u j (σ j) ≤ u j (π j)) ∧ ∃ j, u j (σ j) < u j (π j)) :=
  Econ.ttc_pareto (u := u) (hu := hu) (σ := σ) (hσ := hσ) (π := π)

end

section
-- Bargaining/RubinsteinGame (batch 10)

variable {δ₁ δ₂ : ℝ}

theorem frozen_stationary_isBargSPE (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1) :
    IsBargSPE δ₁ δ₂ (stationaryProfile h₁ h₁' h₂ h₂') :=
  Econ.stationary_isBargSPE h₁ h₁' h₂ h₂'

theorem frozen_stationary_pay₁ (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
    (h : List ℝ) :
    pay₁ (stationaryProfile h₁ h₁' h₂ h₂') δ₁ h =
      if Even h.length then rubinsteinShare δ₁ δ₂ else δ₁ * rubinsteinShare δ₁ δ₂ :=
  Econ.stationary_pay₁ h₁ h₁' h₂ h₂' h

theorem frozen_stationary_pay₂ (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
    (h : List ℝ) :
    pay₂ (stationaryProfile h₁ h₁' h₂ h₂') δ₂ h =
      if Even h.length then δ₂ * rubinsteinShare δ₂ δ₁ else rubinsteinShare δ₂ δ₁ :=
  Econ.stationary_pay₂ h₁ h₁' h₂ h₂' h

theorem frozen_spePay_eq (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1) :
    (∀ v ∈ spePay₁ δ₁ δ₂, v = rubinsteinShare δ₁ δ₂) ∧
      ∀ v ∈ spePay₂ δ₁ δ₂, v = rubinsteinShare δ₂ δ₁ :=
  Econ.spePay_eq h₁ h₁' h₂ h₂'

theorem frozen_bargSPE_eq_stationary (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
    {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) (h : List ℝ) :
    σ.prop h = (stationaryProfile h₁ h₁' h₂ h₂').prop h ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, (σ.acc h x ↔ (stationaryProfile h₁ h₁' h₂ h₂').acc h x) :=
  Econ.bargSPE_eq_stationary h₁ h₁' h₂ h₂' hσ h

theorem frozen_bargSPE_unique (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
    {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) :
    σ.prop [] = rubinsteinShare δ₁ δ₂ ∧ σ.acc [] (rubinsteinShare δ₁ δ₂) ∧
      pay₁ σ δ₁ [] = rubinsteinShare δ₁ δ₂ ∧ pay₂ σ δ₂ [] = 1 - rubinsteinShare δ₁ δ₂ :=
  Econ.bargSPE_unique h₁ h₁' h₂ h₂' hσ

end

end Econ.Audit
