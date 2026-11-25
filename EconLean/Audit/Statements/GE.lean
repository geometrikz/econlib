/-
# Frozen statements: exchange economies, welfare theorems, core, existence

Headline statements of `GE/Exchange.lean`, `GE/SecondWelfare.lean`,
`GE/Existence.lean` and `Foundations/SupportingHyperplane.lean`, copied after
the context-isolated adversarial review of 2026-11-23 (no statement rated
wrong; deviations documented in the files and in `Audit/REVIEW-ge.md`).

Each theorem is closed by the library theorem, and each definition is pinned
by an `Iff.rfl` unfolding to its textbook form, so if a library statement or
definition is ever changed, this file stops compiling. Stand-in for
`leanprover/comparator` until the audit pipeline (PLAN.md §8.4) is set up. Do
not edit a statement here without a new review.
-/
module

public import EconLean.GE.SecondWelfare
public import EconLean.GE.Existence
public import EconLean.GE.Replica
public import EconLean.GE.DebreuScarf
public import EconLean.GE.ExistenceProduction
public import EconLean.GE.ExistenceUnbounded
public import EconLean.GE.ExistenceArrowDebreu

@[expose] public section

-- Frozen statements keep one uniform variable block, so some carry unused
-- `Fintype` instances; that is harmless here.
set_option linter.unusedSectionVars false

namespace Econ.Audit

open Econ Econ.ExchangeEconomy

variable {α ι : Type*} [Fintype α] [Fintype ι] {E : ExchangeEconomy α ι}

/-! ### Definitions pinned to their textbook form -/

theorem frozen_feasible_def (x : Allocation α ι) :
    E.Feasible x ↔ (∀ a, 0 ≤ x a) ∧ ∑ a, x a = ∑ a, E.endow a := Iff.rfl

theorem frozen_paretoOptimal_def (x : Allocation α ι) :
    E.ParetoOptimal x ↔ E.Feasible x ∧ ∀ y, E.Feasible y →
      ¬ ((∀ a, E.pref a (y a) (x a)) ∧ ∃ a, P (E.pref a) (y a) (x a)) := Iff.rfl

theorem frozen_weaklyParetoOptimal_def (x : Allocation α ι) :
    E.WeaklyParetoOptimal x ↔
      E.Feasible x ∧ ∀ y, E.Feasible y → ¬ ∀ a, P (E.pref a) (y a) (x a) := Iff.rfl

theorem frozen_walrasianEquilibrium_def (p : ι → ℝ) (x : Allocation α ι) :
    E.IsWalrasianEquilibrium p x ↔
      (∀ a, x a ∈ demand (E.pref a) p (cost p (E.endow a))) ∧
        ∑ a, x a = ∑ a, E.endow a := Iff.rfl

theorem frozen_blocks_def (S : Finset α) (x : Allocation α ι) :
    E.Blocks S x ↔ S.Nonempty ∧ ∃ y : Allocation α ι, (∀ a ∈ S, 0 ≤ y a) ∧
      ∑ a ∈ S, y a = ∑ a ∈ S, E.endow a ∧ ∀ a ∈ S, P (E.pref a) (y a) (x a) := Iff.rfl

theorem frozen_inCore_def (x : Allocation α ι) :
    E.InCore x ↔ E.Feasible x ∧ ∀ S, ¬ E.Blocks S x := Iff.rfl

theorem frozen_priceEqTransfers_def (p : ι → ℝ) (w : α → ℝ) (x : Allocation α ι) :
    E.IsPriceEquilibriumWithTransfers p w x ↔ E.Feasible x ∧
      ∑ a, w a = cost p (∑ a, E.endow a) ∧
      ∀ a y, 0 ≤ y → P (E.pref a) y (x a) → w a < cost p y := Iff.rfl

theorem frozen_priceQuasiEqTransfers_def (p : ι → ℝ) (w : α → ℝ) (x : Allocation α ι) :
    E.IsPriceQuasiEquilibriumWithTransfers p w x ↔ E.Feasible x ∧
      ∑ a, w a = cost p (∑ a, E.endow a) ∧
      ∀ a y, 0 ≤ y → P (E.pref a) y (x a) → w a ≤ cost p y := Iff.rfl

theorem frozen_continuousPref_def (R : (ι → ℝ) → (ι → ℝ) → Prop) :
    ContinuousPref R ↔ ∀ x, 0 ≤ x →
      IsClosed {y : ι → ℝ | 0 ≤ y ∧ R y x} ∧ IsClosed {y : ι → ℝ | 0 ≤ y ∧ R x y} :=
  Iff.rfl

theorem frozen_priceSimplex_def (p : ι → ℝ) :
    p ∈ priceSimplex ι ↔ 0 ≤ p ∧ ∑ i, p i = 1 := Iff.rfl

theorem frozen_brouwerSimplex_def :
    BrouwerSimplex ι ↔ ∀ f : (ι → ℝ) → (ι → ℝ), ContinuousOn f (priceSimplex ι) →
      Set.MapsTo f (priceSimplex ι) (priceSimplex ι) →
        ∃ p ∈ priceSimplex ι, f p = p := Iff.rfl

theorem frozen_freeDisposalEquilibrium_def (p : ι → ℝ) (x : Allocation α ι) :
    E.IsFreeDisposalEquilibrium p x ↔ 0 ≤ p ∧
      (∀ a, x a ∈ demand (E.pref a) p (cost p (E.endow a))) ∧
      ∑ a, x a ≤ ∑ a, E.endow a ∧
      ∀ i, (∑ a, x a) i < (∑ a, E.endow a) i → p i = 0 := Iff.rfl

/-! ### Theorems -/

theorem frozen_first_welfare_theorem (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {x : Allocation α ι}
    (heq : E.IsWalrasianEquilibrium p x) : E.ParetoOptimal x :=
  first_welfare_theorem hR hlns heq

theorem frozen_walrasian_inCore {p : ι → ℝ} {x : Allocation α ι}
    (heq : E.IsWalrasianEquilibrium p x) : E.InCore x :=
  heq.inCore

theorem frozen_inCore_individuallyRational (hR : ∀ a, Rational (E.pref a))
    {x : Allocation α ι} (hx : E.InCore x) : ∀ a, E.pref a (x a) (E.endow a) :=
  hx.individuallyRational hR

theorem frozen_inCore_weaklyParetoOptimal [Nonempty α] {x : Allocation α ι}
    (hx : E.InCore x) : E.WeaklyParetoOptimal x :=
  hx.weaklyParetoOptimal

theorem frozen_exists_price_support [Nonempty ι] {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    {x : ι → ℝ} (hx : x ∉ interior C) :
    ∃ p : ι → ℝ, p ≠ 0 ∧ ∀ c ∈ C, cost p x ≤ cost p c :=
  exists_price_support hC hx

theorem frozen_first_welfare_with_transfers (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceEquilibriumWithTransfers p w x) :
    E.ParetoOptimal x :=
  h.paretoOptimal hR hlns

theorem frozen_priceEqTransfers_cost_eq (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceEquilibriumWithTransfers p w x) (a : α) :
    cost p (x a) = w a :=
  h.cost_eq hR hlns a

theorem frozen_second_welfare_theorem [Nonempty ι] (hR : ∀ a, Rational (E.pref a))
    (hconv : ∀ a, ConvexPref (E.pref a)) (hlns : ∀ a, LocallyNonsatiated (E.pref a))
    {x : Allocation α ι} (hx : E.ParetoOptimal x) :
    ∃ p : ι → ℝ, p ≠ 0 ∧
      E.IsPriceQuasiEquilibriumWithTransfers p (fun a => cost p (x a)) x :=
  second_welfare_theorem hR hconv hlns hx

theorem frozen_quasi_to_equilibrium (hR : ∀ a, Rational (E.pref a))
    (hcont : ∀ a, ContinuousPref (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceQuasiEquilibriumWithTransfers p w x)
    (hcheap : ∀ a, ∃ z, 0 ≤ z ∧ cost p z < w a) :
    E.IsPriceEquilibriumWithTransfers p w x :=
  h.isPriceEquilibriumWithTransfers hR hcont hcheap

theorem frozen_second_welfare_theorem_demand [Nonempty ι] [Nonempty α]
    (hR : ∀ a, Rational (E.pref a)) (hmono : ∀ a, StronglyMonotone (E.pref a))
    (hcont : ∀ a, ContinuousPref (E.pref a)) (hconv : ∀ a, ConvexPref (E.pref a))
    {x : Allocation α ι} (hx : E.ParetoOptimal x) (hpos : ∀ a i, 0 < x a i) :
    ∃ p : ι → ℝ, p ≠ 0 ∧ 0 ≤ p ∧
      E.IsPriceEquilibriumWithTransfers p (fun a => cost p (x a)) x ∧
      ∀ a, x a ∈ demand (E.pref a) p (cost p (x a)) :=
  second_welfare_theorem_demand hR hmono hcont hconv hx hpos

theorem frozen_brouwerSimplex_fin_two : BrouwerSimplex (Fin 2) :=
  brouwerSimplex_fin_two

theorem frozen_gale_nikaido_debreu (hB : BrouwerSimplex ι) {z : (ι → ℝ) → (ι → ℝ)}
    (hz : ContinuousOn z (priceSimplex ι))
    (hW : ∀ p ∈ priceSimplex ι, cost p (z p) ≤ 0) :
    ∃ p ∈ priceSimplex ι, z p ≤ 0 :=
  gale_nikaido_debreu hB hz hW

theorem frozen_exists_freeDisposalEquilibrium (hB : BrouwerSimplex ι)
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d : α → (ι → ℝ) → (ι → ℝ)}
    (hd : ∀ p ∈ priceSimplex ι, ∀ a, d a p ∈ demand (E.pref a) p (cost p (E.endow a)))
    (hc : ∀ a, ContinuousOn (d a) (priceSimplex ι)) :
    ∃ p ∈ priceSimplex ι, E.IsFreeDisposalEquilibrium p (fun a => d a p) :=
  exists_freeDisposalEquilibrium hB hlns hd hc

section Replica

/-! Frozen after the adversarial review of 2026-11-25 (`Audit/REVIEW-replica.md`). -/

theorem frozen_replica_def {I : Type*} (u : I → (ι → ℝ) → ℝ) (ω : I → ι → ℝ)
    (hω : ∀ i, 0 ≤ ω i) (r : ℕ) (a : I × Fin r) :
    (replica u ω hω r).pref a = prefOf (u a.1) ∧ (replica u ω hω r).endow a = ω a.1 :=
  ⟨rfl, rfl⟩

theorem frozen_replica_inCore_equalTreatment {I : Type*} [Fintype I] [DecidableEq I]
    {u : I → (ι → ℝ) → ℝ} {ω : I → ι → ℝ} {hω : ∀ i, 0 ≤ ω i} {r : ℕ}
    (hu : ∀ i, Continuous (u i)) (hsq : ∀ i, StrictlyQuasiconcave (u i))
    (hmono : ∀ i, StronglyMonotone (prefOf (u i))) {x : Allocation (I × Fin r) ι}
    (hx : (replica u ω hω r).InCore x) (i : I) (q q' : Fin r) : x (i, q) = x (i, q') :=
  replica_inCore_equalTreatment hu hsq hmono hx i q q'

theorem frozen_linear_replica_unequal_core :
    (replica (fun (_ : Fin 1) (x : Fin 2 → ℝ) => x 0 + x 1) (fun _ _ => 1)
      (fun _ _ => zero_le_one) 2).InCore
      (fun a => if a.2 = 0 then ![2, 0] else ![0, 2]) ∧
    (fun a : Fin 1 × Fin 2 => if a.2 = 0 then (![2, 0] : Fin 2 → ℝ) else ![0, 2]) (0, 0) ≠
      (fun a : Fin 1 × Fin 2 => if a.2 = 0 then (![2, 0] : Fin 2 → ℝ) else ![0, 2]) (0, 1) :=
  GEExamples.linear_replica_unequal_core

end Replica

section DebreuScarf

theorem frozen_walrasian_of_mem_core_replicas {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty I] [Nonempty ι] {u : I → (ι → ℝ) → ℝ} {ω : I → ι → ℝ} {hω : ∀ i, 0 ≤ ω i}
    (hu : ∀ i, Continuous (u i)) (hsq : ∀ i, StrictlyQuasiconcave (u i))
    (hmono : ∀ i, StronglyMonotone (prefOf (u i))) (hωpos : ∀ i, PositivePrices (ω i))
    {xs : I → ι → ℝ} (hcore : ∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) :
    ∃ p : ι → ℝ, PositivePrices p ∧ ∀ i, xs i ∈ demand (prefOf (u i)) p (cost p (ω i)) :=
  walrasian_of_mem_core_replicas hu hsq hmono hωpos hcore

theorem frozen_isWalrasianEquilibrium_of_mem_core_replicas {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] [Nonempty ι] {u : I → (ι → ℝ) → ℝ} {ω : I → ι → ℝ}
    {hω : ∀ i, 0 ≤ ω i} (hu : ∀ i, Continuous (u i)) (hsq : ∀ i, StrictlyQuasiconcave (u i))
    (hmono : ∀ i, StronglyMonotone (prefOf (u i))) (hωpos : ∀ i, PositivePrices (ω i))
    {xs : I → ι → ℝ} (hcore : ∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) :
    ∃ p : ι → ℝ, PositivePrices p ∧
      ∀ r, (replica u ω hω r).IsWalrasianEquilibrium p fun a => xs a.1 :=
  isWalrasianEquilibrium_of_mem_core_replicas hu hsq hmono hωpos hcore

theorem frozen_mem_core_replicas_iff_walrasian {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty I] [Nonempty ι] {u : I → (ι → ℝ) → ℝ} {ω : I → ι → ℝ} {hω : ∀ i, 0 ≤ ω i}
    (hu : ∀ i, Continuous (u i)) (hsq : ∀ i, StrictlyQuasiconcave (u i))
    (hmono : ∀ i, StronglyMonotone (prefOf (u i))) (hωpos : ∀ i, PositivePrices (ω i))
    {xs : I → ι → ℝ} :
    (∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) ↔
      ∃ p : ι → ℝ, PositivePrices p ∧
        ∀ r, (replica u ω hω r).IsWalrasianEquilibrium p fun a => xs a.1 :=
  mem_core_replicas_iff_walrasian hu hsq hmono hωpos

end DebreuScarf

section ExistenceProduction

theorem frozen_exists_walrasianEquilibrium_production {β : Type*} [Fintype β] [Nonempty ι]
    (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, RegularUtility (u a))
    (hω : PositivePrices E.totalEndowment) (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j)
    (hYc : ∀ j, IsCompact (E.prod j)) {s : β → (ι → ℝ) → (ι → ℝ)}
    (hs : ∀ j p, PositivePrices p → ProductionEconomy.ProfitMax p (E.prod j) (s j p))
    (hsc : ∀ j, ContinuousOn (s j) {p | PositivePrices p}) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y :=
  E.exists_walrasianEquilibrium_production hpref hreg hω hY0 hYc hs hsc

theorem frozen_exists_walrasianEquilibrium_production_of_unique {β : Type*} [Fintype β]
    [Nonempty ι] (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hreg : ∀ a, RegularUtility (u a))
    (hω : PositivePrices E.totalEndowment)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYc : ∀ j, IsCompact (E.prod j))
    (huniq : ∀ j p, PositivePrices p →
      {y | ProductionEconomy.ProfitMax p (E.prod j) y}.Subsingleton) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y :=
  E.exists_walrasianEquilibrium_production_of_unique hpref hreg hω hY0 hYc huniq

end ExistenceProduction

section ExistenceUnbounded

theorem frozen_aggProd {β : Type*} [Fintype β] (E : ProductionEconomy α β ι) (z : ι → ℝ) :
    z ∈ E.aggProd ↔ ∃ y : β → ι → ℝ, (∀ j, y j ∈ E.prod j) ∧ ∑ j, y j = z := Iff.rfl

theorem frozen_noFreeLunch (Y : Set (ι → ℝ)) :
    NoFreeLunch Y ↔ ∀ y ∈ Y, 0 ≤ y → y = 0 := Iff.rfl

theorem frozen_irreversible (Y : Set (ι → ℝ)) :
    Irreversible Y ↔ ∀ y ∈ Y, -y ∈ Y → y = 0 := Iff.rfl

theorem frozen_exists_bound_attainable {β : Type*} [Fintype β] (E : ProductionEconomy α β ι)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) (c : ι → ℝ) :
    ∃ R, ∀ y : β → ι → ℝ, (∀ j, y j ∈ E.prod j) → c ≤ ∑ j, y j → ‖y‖ ≤ R :=
  E.exists_bound_attainable hY0 hYcl hYcv hnfl hirr c

theorem frozen_exists_walrasianEquilibrium_unbounded {β : Type*} [Fintype β] [Nonempty ι]
    (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, RegularUtility (u a)) (hω : PositivePrices E.totalEndowment)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYsc : ∀ j, StrictConvex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y :=
  E.exists_walrasianEquilibrium_unbounded hpref hreg hω hY0 hYcl hYsc hnfl hirr

end ExistenceUnbounded

section ExistenceArrowDebreu

theorem frozen_exists_walrasianEquilibrium_arrowDebreu {β : Type*} [Fintype β] [Nonempty ι]
    [Nonempty α] (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hsq : ∀ a, StrictlyQuasiconcave (u a)) (hmono : ∀ a, StronglyMonotone (prefOf (u a)))
    (hωa : ∀ a, PositivePrices (E.endow a))
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y :=
  E.exists_walrasianEquilibrium_arrowDebreu hpref hu hsq hmono hωa hY0 hYcl hYcv hnfl hirr

theorem frozen_exists_walrasianEquilibrium_arrowDebreu_convex {β : Type*} [Fintype β]
    [Nonempty ι] [Nonempty α] (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hqc : ∀ a, QuasiconcaveOn ℝ (Set.Ici 0) (u a))
    (hmono : ∀ a, StronglyMonotone (prefOf (u a)))
    (hωa : ∀ a, PositivePrices (E.endow a))
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y :=
  E.exists_walrasianEquilibrium_arrowDebreu_convex hpref hu hqc hmono hωa hY0 hYcl hYcv hnfl hirr

theorem frozen_quasiconcaveOn (s : Set (ι → ℝ)) (u : (ι → ℝ) → ℝ) :
    QuasiconcaveOn ℝ s u ↔ ∀ r, Convex ℝ {x | x ∈ s ∧ r ≤ u x} := Iff.rfl

end ExistenceArrowDebreu

end Econ.Audit
