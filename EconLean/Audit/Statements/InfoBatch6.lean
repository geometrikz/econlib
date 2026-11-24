/-
# Frozen statements: informativeness principle, Bayes correlated equilibrium, property
# rights, the Boston mechanism

Headline statements of `Information/{Informativeness,BayesCorrelated,PropertyRights}` and
`Matching/Boston`, copied after the adversarial review recorded in
`Audit/REVIEW-info-batch6.md`. Each is closed by the library theorem, so if a library statement
is ever weakened this file stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Information.Informativeness
public import EconLean.Information.BayesCorrelated
public import EconLean.Information.PropertyRights
public import EconLean.Matching.Boston

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Function Finset Econ

section
-- Information/Informativeness

variable {A X Y : Type*} [Fintype X] [Fintype Y]

theorem frozen_informativeness_principle {f : A → X → Y → ℝ} {g : A → X → ℝ} {h : X → Y → ℝ}
    (hsuff : ∀ a x y, f a x y = g a x * h x y) (hg : ∀ a x, 0 ≤ g a x)
    (hh0 : ∀ x y, 0 ≤ h x y) (hh1 : ∀ x, ∑ y, h x y = 1) {U : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ U φ) {ν : X → Y → ℝ} (hν : ∀ x y, ν x y ∈ U) (c : A → ℝ) :
    (∀ x y, condContract h ν x y ∈ U) ∧
      (∀ a, agentValue f c (condContract h ν) a = agentValue f c ν a) ∧
      (∀ ū a, Implements f c ū ν a → Implements f c ū (condContract h ν) a) ∧
      ∀ a, principalCost f φ (condContract h ν) a ≤ principalCost f φ ν a :=
  Econ.informativeness_principle (f := f) (g := g) (h := h) (hsuff := hsuff) (hg := hg) (hh0 := hh0) (hh1 := hh1) (U := U) (φ := φ) (hφ := hφ) (ν := ν) (hν := hν) (c := c)

theorem frozen_informativeness_strict {f : A → X → Y → ℝ} {g : A → X → ℝ} {h : X → Y → ℝ}
    (hsuff : ∀ a x y, f a x y = g a x * h x y) (hg : ∀ a x, 0 ≤ g a x)
    (hh0 : ∀ x y, 0 ≤ h x y) (hh1 : ∀ x, ∑ y, h x y = 1) {U : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConvexOn ℝ U φ) {ν : X → Y → ℝ} (hν : ∀ x y, ν x y ∈ U) (a : A) {x₀ : X}
    (hx₀ : 0 < g a x₀) {y₁ y₂ : Y} (hy₁ : 0 < h x₀ y₁) (hy₂ : 0 < h x₀ y₂)
    (hne : ν x₀ y₁ ≠ ν x₀ y₂) :
    principalCost f φ (condContract h ν) a < principalCost f φ ν a :=
  Econ.informativeness_strict (f := f) (g := g) (h := h) (hsuff := hsuff) (hg := hg) (hh0 := hh0) (hh1 := hh1) (U := U) (φ := φ) (hφ := hφ) (ν := ν) (hν := hν) (a := a) (x₀ := x₀) (hx₀ := hx₀) (y₁ := y₁) (y₂ := y₂) (hy₁ := hy₁) (hy₂ := hy₂) (hne := hne)

end

section
-- Information/BayesCorrelated

universe uA

variable {Θ I : Type*} [Fintype Θ] [Fintype I] [DecidableEq I]
  {A : I → Type uA} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

variable {R : I → Type*} [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]

theorem frozen_bneOutcome_isBCE {ψ : Θ → ℝ} (hψ : ∀ θ, 0 ≤ ψ θ) {π : Θ → (∀ i, T i) → ℝ}
    {π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ} (hexp : IsExpansion π π')
    {u : I → Θ → (∀ i, A i) → ℝ} {β : ∀ i, T i → R i → A i} (hβ : IsExpansionBNE ψ u π' β) :
    IsBCE ψ π u (bneOutcome ψ π' β) :=
  Econ.bneOutcome_isBCE (ψ := ψ) (hψ := hψ) (π := π) (π' := π') (hexp := hexp) (u := u) (β := β) (hβ := hβ)

theorem frozen_isBCE_bneOutcome [∀ i, Nonempty (A i)] {ψ : Θ → ℝ} (hψ : ∀ θ, 0 ≤ ψ θ)
    {π : Θ → (∀ i, T i) → ℝ} (hπ : ∀ θ t, 0 ≤ π θ t)
    {u : I → Θ → (∀ i, A i) → ℝ} {ν : Θ → (∀ i, T i) → (∀ i, A i) → ℝ}
    (hν : IsBCE ψ π u ν) :
    IsExpansion (R := A) π (obedientExpansion ψ π ν) ∧
      IsExpansionBNE (R := A) ψ u (obedientExpansion ψ π ν) (fun _ _ a => a) ∧
      bneOutcome (R := A) ψ (obedientExpansion ψ π ν) (fun _ _ a => a) = ν :=
  Econ.isBCE_bneOutcome (ψ := ψ) (hψ := hψ) (π := π) (hπ := hπ) (u := u) (ν := ν) (hν := hν)

theorem frozen_isBCE_iff [∀ i, Nonempty (A i)] {ψ : Θ → ℝ} (hψ : ∀ θ, 0 ≤ ψ θ)
    {π : Θ → (∀ i, T i) → ℝ} (hπ : ∀ θ t, 0 ≤ π θ t)
    {u : I → Θ → (∀ i, A i) → ℝ} (ν : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) :
    IsBCE ψ π u ν ↔ ∃ (R : I → Type uA) (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i))
      (π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ) (β : ∀ i, T i → R i → A i),
      IsExpansion π π' ∧ IsExpansionBNE ψ u π' β ∧ bneOutcome ψ π' β = ν :=
  Econ.isBCE_iff (ψ := ψ) (hψ := hψ) (π := π) (hπ := hπ) (u := u) (ν := ν)

end

section
-- Information/PropertyRights

theorem frozen_monotone_argmax {F G : ℝ → ℝ} (hFG : MonotoneOn (fun i => F i - G i) (Set.Ici 0))
    {x y : ℝ}
    (hx : IsInvestmentMax G x) (hy : IsInvestmentMax F y) :
    IsInvestmentMax F (max x y) ∧ IsInvestmentMax G (min x y) :=
  Econ.monotone_argmax (F := F) (G := G) (hFG := hFG) (x := x) (y := y) (hx := hx) (hy := hy)

theorem frozen_underinvestment {V v : ℝ → ℝ} {w : ℝ} (hspec : MonotoneOn (fun i => V i - v i) (Set.Ici 0)) {x y : ℝ}
    (hx : IsInvestmentMax (managerPayoff V v w) x) (hy : IsInvestmentMax (netSurplus V) y)
    (huniq : ∀ z, IsInvestmentMax (netSurplus V) z → z = y) : x ≤ y :=
  Econ.underinvestment (V := V) (v := v) (w := w) (hspec := hspec) (x := x) (y := y) (hx := hx) (hy := hy) (huniq := huniq)

theorem frozen_ownership_raises_investment {V v v' : ℝ → ℝ} {w w' : ℝ}
    (hmore : MonotoneOn (fun i => v' i - v i) (Set.Ici 0)) {x x' : ℝ}
    (hx : IsInvestmentMax (managerPayoff V v w) x) (hx' : IsInvestmentMax (managerPayoff V v' w') x')
    (huniq : ∀ z, IsInvestmentMax (managerPayoff V v' w') z → z = x') : x ≤ x' :=
  Econ.ownership_raises_investment (V := V) (v := v) (v' := v') (w := w) (w' := w') (hmore := hmore) (x := x) (x' := x') (hx := hx) (hx' := hx') (huniq := huniq)

theorem frozen_more_ownership_raises_surplus {V v v' : ℝ → ℝ} {w w' : ℝ}
    (hspec' : MonotoneOn (fun i => V i - v' i) (Set.Ici 0))
    (hmore : MonotoneOn (fun i => v' i - v i) (Set.Ici 0)) {x x' y : ℝ}
    (hx : IsInvestmentMax (managerPayoff V v w) x) (hx' : IsInvestmentMax (managerPayoff V v' w') x')
    (huniq' : ∀ z, IsInvestmentMax (managerPayoff V v' w') z → z = x')
    (hy : IsInvestmentMax (netSurplus V) y) (huniq : ∀ z, IsInvestmentMax (netSurplus V) z → z = y)
    (hmono : MonotoneOn (netSurplus V) (Set.Icc 0 y)) :
    netSurplus V x ≤ netSurplus V x' :=
  Econ.more_ownership_raises_surplus (V := V) (v := v) (v' := v') (w := w) (w' := w') (hspec' := hspec') (hmore := hmore) (x := x) (x' := x') (y := y) (hx := hx) (hx' := hx') (huniq' := huniq') (hy := hy) (huniq := huniq) (hmono := hmono)

end

section
-- Matching/Boston

variable {n m : ℕ}

theorem frozen_boston_manipulable :
    boston exTruePref exPrio 0 = some 2 ∧ boston exManipPref exPrio 0 = some 1 ∧
      (∀ s, exManipPref s ≠ exTruePref s → s = 0) ∧
      (exTruePref 0).idxOf 1 < (exTruePref 0).idxOf 2 :=
  Econ.boston_manipulable 

theorem frozen_boston_not_stable :
    boston exTruePref exPrio 0 = some 2 ∧ boston exTruePref exPrio 2 = some 1 ∧
      (exTruePref 0).idxOf 1 < (exTruePref 0).idxOf 2 ∧ (exPrio 1).idxOf 0 < (exPrio 1).idxOf 2 :=
  Econ.boston_not_stable 

end

end Econ.Audit
