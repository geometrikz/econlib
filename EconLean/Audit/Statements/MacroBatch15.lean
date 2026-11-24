/-
# Frozen statements: Atkinson–Stiglitz and Diamond–Mirrlees

Headline statements copied verbatim after two rounds of context-isolated
adversarial review (2026-11-24; see `Audit/REVIEW-macro-batch15.md`). Each is
closed by the library theorem, so if a library statement is weakened this file
stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.PublicFinance.AtkinsonStiglitz
public import EconLean.Macro.PublicFinance.DiamondMirrlees

@[expose] public section

namespace Econ.Audit

open Matrix Filter Topology

theorem frozen_as_V_e {ι : Type*} [Fintype ι] {v : (ι → ℝ) → ℝ} {p : ι → ℝ}
    (hv : Continuous v) (hp : ∀ i, 0 < p i) {u : ℝ} (h0 : v 0 ≤ u)
    (hatt : ∃ z, (∀ i, 0 ≤ z i) ∧ u ≤ v z ∧ p ⬝ᵥ z = Econ.AtkinsonStiglitz.e v p u) :
    Econ.AtkinsonStiglitz.V v p (Econ.AtkinsonStiglitz.e v p u) = u :=
  Econ.AtkinsonStiglitz.V_e hv hp h0 hatt

theorem frozen_as_income_tax_dominates {ι κ Θ : Type*} [Fintype ι] {v : (ι → ℝ) → ℝ}
    {p t : ι → ℝ} {c : κ → ℝ} {x : κ → ι → ℝ}
    (hR : Econ.AtkinsonStiglitz.Regime v p t c x) (U : Θ → ℝ → ℝ → ℝ) (y : κ → ℝ) :
    (∀ θ j, U θ (Econ.AtkinsonStiglitz.V v p (Econ.AtkinsonStiglitz.c' v p x j)) (y j) =
        U θ (Econ.AtkinsonStiglitz.V v (p + t) (c j)) (y j)) ∧
      (∀ θ i j, U θ (Econ.AtkinsonStiglitz.V v p (Econ.AtkinsonStiglitz.c' v p x j)) (y j) ≤
          U θ (Econ.AtkinsonStiglitz.V v p (Econ.AtkinsonStiglitz.c' v p x i)) (y i) ↔
        U θ (Econ.AtkinsonStiglitz.V v (p + t) (c j)) (y j) ≤
          U θ (Econ.AtkinsonStiglitz.V v (p + t) (c i)) (y i)) ∧
      (∀ j, (y j - c j) + t ⬝ᵥ x j ≤ y j - Econ.AtkinsonStiglitz.c' v p x j) :=
  Econ.AtkinsonStiglitz.income_tax_dominates hR U y

theorem frozen_as_c'_schedule {ι κ : Type*} [Fintype ι] {v : (ι → ℝ) → ℝ}
    {p t : ι → ℝ} {c : κ → ℝ} {x : κ → ι → ℝ}
    (hR : Econ.AtkinsonStiglitz.Regime v p t c x) (y : κ → ℝ)
    (hc : ∀ i j, y i = y j → c i = c j) {i j : κ} (h : y i = y j) :
    Econ.AtkinsonStiglitz.c' v p x i = Econ.AtkinsonStiglitz.c' v p x j :=
  Econ.AtkinsonStiglitz.c'_schedule hR y hc h

theorem frozen_dm_weakly_efficient {ι : Type*} [Finite ι] {Q : Set (ι → ℝ)}
    {W : (ι → ℝ) → ℝ} {x : (ι → ℝ) → ι → ℝ} {g : ι → ℝ} {Z : Set (ι → ℝ)} {q : ι → ℝ}
    (hfd : ∀ z ∈ Z, ∀ z', z' ≤ z → z' ∈ Z)
    (hopt : Econ.DiamondMirrlees.IsOptimum Q W x g Z q)
    (hQ : q ∈ interior Q) (hx : ContinuousAt x q) (hns : ∀ U ∈ 𝓝 q, ∃ q' ∈ U, W q < W q') :
    ¬ ∃ z ∈ Z, ∀ i, x q i + g i < z i :=
  Econ.DiamondMirrlees.weakly_efficient hfd hopt hQ hx hns

theorem frozen_dm_weakly_efficient_of_price_decrease {ι : Type*} [Finite ι] [DecidableEq ι]
    {Q : Set (ι → ℝ)} {W : (ι → ℝ) → ℝ} {x : (ι → ℝ) → ι → ℝ} {g : ι → ℝ}
    {Z : Set (ι → ℝ)} {q : ι → ℝ}
    (hfd : ∀ z ∈ Z, ∀ z', z' ≤ z → z' ∈ Z)
    (hopt : Econ.DiamondMirrlees.IsOptimum Q W x g Z q)
    (hQ : q ∈ interior Q) (hx : ContinuousAt x q) (k : ι)
    (hdec : ∀ᶠ ε in 𝓝[>] (0 : ℝ), W q < W (q - Pi.single k ε)) :
    ¬ ∃ z ∈ Z, ∀ i, x q i + g i < z i :=
  Econ.DiamondMirrlees.weakly_efficient_of_price_decrease hfd hopt hQ hx k hdec

end Econ.Audit
