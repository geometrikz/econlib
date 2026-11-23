/-
# Frozen statements: Brouwer, Kakutani, and unconditional existence

Headline statements of `Foundations/FixedPoint.lean` and
`GE/ExistenceGeneral.lean`, frozen after the context-isolated adversarial review
of 2026-11-23 (see `Audit/REVIEW-fixedpoint.md`). Each theorem is closed by the
library theorem, so changing a library statement breaks this file. Do not edit
a statement here without a new review.
-/
module

public import EconLean.GE.ExistenceGeneral
public import EconLean.GE.ExistenceInterior
public import EconLean.GE.ExistencePreferences

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Econ Set

theorem frozen_brouwer {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x :=
  brouwer_fixedPoint hconv hcomp hne hmaps hf

theorem frozen_brouwer_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x :=
  brouwer_fixedPoint_continuousMap hconv hcomp hne f

theorem frozen_kakutani {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x :=
  kakutani_fixedPoint hconv hcomp hne hmaps hφne hφconv hgraph

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem frozen_brouwerSimplex [Nonempty ι] : BrouwerSimplex ι := brouwerSimplex

theorem frozen_gale_nikaido_debreu' [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    (hz : ContinuousOn z (priceSimplex ι))
    (hW : ∀ p ∈ priceSimplex ι, cost p (z p) ≤ 0) :
    ∃ p ∈ priceSimplex ι, z p ≤ 0 :=
  gale_nikaido_debreu' hz hW

theorem frozen_exists_freeDisposalEquilibrium' [Nonempty ι] (E : ExchangeEconomy α ι)
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d : α → (ι → ℝ) → (ι → ℝ)}
    (hd : E.IsDemandSelection d (priceSimplex ι))
    (hc : ∀ a, ContinuousOn (d a) (priceSimplex ι)) :
    ∃ p ∈ priceSimplex ι, E.IsFreeDisposalEquilibrium p (fun a => d a p) :=
  E.exists_freeDisposalEquilibrium' hlns hd hc

section BoundaryCondition

open Filter Topology

theorem frozen_excessBoundedBelow_def (z : (ι → ℝ) → (ι → ℝ)) :
    ExcessBoundedBelow z ↔ ∃ s : ℝ, ∀ p, PositivePrices p → ∀ l, -s < z p l := Iff.rfl

theorem frozen_boundaryCondition_def (z : (ι → ℝ) → (ι → ℝ)) :
    BoundaryCondition z ↔ ∀ (pn : ℕ → ι → ℝ) (pbar : ι → ℝ), (∀ n, PositivePrices (pn n)) →
      Tendsto pn atTop (𝓝 pbar) → pbar ≠ 0 → (∃ l, pbar l = 0) →
        ∀ M : ℝ, ∀ᶠ n in atTop, ∃ l, M < z (pn n) l := Iff.rfl

theorem frozen_positivePrices_def (p : ι → ℝ) : PositivePrices p ↔ ∀ i, 0 < p i := Iff.rfl

theorem frozen_exists_equilibrium_of_boundaryCondition [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    (hc : ContinuousOn z {p | PositivePrices p}) (hW : ∀ p, PositivePrices p → cost p (z p) = 0)
    (hb : ExcessBoundedBelow z) (hbd : BoundaryCondition z) :
    ∃ p, PositivePrices p ∧ z p = 0 :=
  exists_equilibrium_of_boundaryCondition hc hW hb hbd

end BoundaryCondition

section FromPreferences

theorem frozen_exists_walrasianEquilibrium_of_boundaryCondition [Nonempty ι]
    (E : ExchangeEconomy α ι) (hlns : ∀ a, LocallyNonsatiated (E.pref a))
    {d : α → (ι → ℝ) → (ι → ℝ)} (hd : E.IsDemandSelection d {p | PositivePrices p})
    (hc : ContinuousOn (E.excessDemand d) {p | PositivePrices p})
    (hb : ExcessBoundedBelow (E.excessDemand d)) (hbd : BoundaryCondition (E.excessDemand d)) :
    ∃ p, PositivePrices p ∧ E.IsWalrasianEquilibrium p (fun a => d a p) :=
  E.exists_walrasianEquilibrium_of_boundaryCondition hlns hd hc hb hbd

theorem frozen_boundaryCondition_excessDemand (E : ExchangeEconomy α ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hmono : ∀ a, StronglyMonotone (E.pref a)) (hω : PositivePrices E.totalEndowment)
    {d : α → (ι → ℝ) → (ι → ℝ)} (hd : E.IsDemandSelection d {p | PositivePrices p}) :
    BoundaryCondition (E.excessDemand d) :=
  E.boundaryCondition_excessDemand hpref hu hmono hω hd

theorem frozen_exists_walrasianEquilibrium_of_preferences [Nonempty ι] (E : ExchangeEconomy α ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hsq : ∀ a, StrictlyQuasiconcave (u a)) (hmono : ∀ a, StronglyMonotone (E.pref a))
    (hω : PositivePrices E.totalEndowment) (hωa : ∀ a, E.endow a ≠ 0) :
    ∃ p x, PositivePrices p ∧ E.IsWalrasianEquilibrium p x :=
  E.exists_walrasianEquilibrium_of_preferences hpref hu hsq hmono hω hωa

end FromPreferences

end Econ.Audit
