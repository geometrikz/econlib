/-
# Frozen statements: production economies and bridge B0 aggregation results

Headline statements of `GE/Production.lean` and `Bridges/Aggregation/*.lean`,
copied after the context-isolated adversarial review of 2026-11-23 (no
statement rated wrong; findings fixed or documented, see
`Audit/REVIEW-production-aggregation.md`). Each is closed by the library
theorem, so a weakened library statement stops this file compiling. Do not
edit a statement here without a new review.
-/
module

public import EconLean.GE.Production
public import EconLean.Bridges.Aggregation.GrossSubstitutes
public import EconLean.Bridges.Aggregation.LawOfDemand
public import EconLean.Bridges.Aggregation.Gorman
public import EconLean.Bridges.Aggregation.Tatonnement
public import EconLean.Bridges.Aggregation.SMD
public import EconLean.Bridges.Aggregation.SMDConsumer

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Econ

section Production

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] {E : ProductionEconomy α β ι}

theorem frozen_production_walrasian_def (p : ι → ℝ) (x : Allocation α ι) (y : β → ι → ℝ) :
    E.IsWalrasianEquilibrium p x y ↔
      (∀ j, y j ∈ E.prod j ∧ ∀ y' ∈ E.prod j, cost p y' ≤ cost p (y j)) ∧
      (∀ a, x a ∈ demand (E.pref a) p
        (cost p (E.endow a) + ∑ j, E.share a j * cost p (y j))) ∧
      ∑ a, x a = ∑ a, E.endow a + ∑ j, y j := Iff.rfl

theorem frozen_production_paretoOptimal_def (x : Allocation α ι) (y : β → ι → ℝ) :
    E.ParetoOptimal x y ↔
      ((∀ a, 0 ≤ x a) ∧ (∀ j, y j ∈ E.prod j) ∧ ∑ a, x a = ∑ a, E.endow a + ∑ j, y j) ∧
      ∀ x' y', E.Feasible x' y' →
        ¬ ((∀ a, E.pref a (x' a) (x a)) ∧ ∃ a, P (E.pref a) (x' a) (x a)) := Iff.rfl

theorem frozen_production_first_welfare (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {x : Allocation α ι}
    {y : β → ι → ℝ} (heq : E.IsWalrasianEquilibrium p x y) : E.ParetoOptimal x y :=
  ProductionEconomy.first_welfare_theorem hR hlns heq

theorem frozen_production_second_welfare [Nonempty ι] [Nonempty α]
    (hR : ∀ a, Rational (E.pref a)) (hconv : ∀ a, ConvexPref (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) (hY : ∀ j, Convex ℝ (E.prod j))
    {x : Allocation α ι} {y : β → ι → ℝ} (hxy : E.ParetoOptimal x y) :
    ∃ p : ι → ℝ, p ≠ 0 ∧
      E.IsPriceQuasiEquilibriumWithTransfers p (fun a => cost p (x a)) x y :=
  ProductionEconomy.second_welfare_theorem hR hconv hlns hY hxy

theorem frozen_production_quasi_to_eq (hR : ∀ a, Rational (E.pref a))
    (hcont : ∀ a, ContinuousPref (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} {y : β → ι → ℝ}
    (h : E.IsPriceQuasiEquilibriumWithTransfers p w x y)
    (hcheap : ∀ a, ∃ z, 0 ≤ z ∧ cost p z < w a) :
    E.IsPriceEquilibriumWithTransfers p w x y :=
  h.isPriceEquilibriumWithTransfers hR hcont hcheap

end Production

section Aggregation

variable {ι : Type*} [Fintype ι]

theorem frozen_grossSubstitutes_def [DecidableEq ι] (z : (ι → ℝ) → (ι → ℝ)) :
    GrossSubstitutes z ↔ ∀ p l (t : ℝ), (∀ i, 0 < p i) → p l < t →
      ∀ k, k ≠ l → z p k < z (Function.update p l t) k := Iff.rfl

theorem frozen_grossSubstitutes_sum [DecidableEq ι] {α : Type*} (s : Finset α)
    (hs : s.Nonempty) {z : α → (ι → ℝ) → (ι → ℝ)} (h : ∀ a ∈ s, GrossSubstitutes (z a)) :
    GrossSubstitutes (fun p => ∑ a ∈ s, z a p) :=
  GrossSubstitutes.sum s hs h

theorem frozen_grossSubstitutes_unique [DecidableEq ι] [Nonempty ι]
    {z : (ι → ℝ) → (ι → ℝ)} (hGS : GrossSubstitutes z)
    (hhom : ∀ p, (∀ i, 0 < p i) → ∀ t : ℝ, 0 < t → z (t • p) = z p) {p p' : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hp' : ∀ i, 0 < p' i) (hz : z p = 0) (hz' : z p' = 0) :
    ∃ t : ℝ, 0 < t ∧ p' = t • p :=
  hGS.unique_equilibrium hhom hp hp' hz hz'

theorem frozen_lawOfDemand_sum {α : Type*} (s : Finset α) {z : α → (ι → ℝ) → (ι → ℝ)}
    {D : Set (ι → ℝ)} (h : ∀ a ∈ s, LawOfDemand (z a) D) :
    LawOfDemand (fun p => ∑ a ∈ s, z a p) D :=
  LawOfDemand.sum s h

theorem frozen_warp_convex_equilibria {z : (ι → ℝ) → (ι → ℝ)} {D : Set (ι → ℝ)}
    (hD : Convex ℝ D) (hW : ∀ p ∈ D, cost p (z p) = 0)
    (hWARP : ∀ p ∈ D, ∀ p' ∈ D, z p ≠ z p' → cost p (z p') ≤ 0 → 0 < cost p' (z p)) :
    Convex ℝ {p | p ∈ D ∧ z p = 0} :=
  ExcessWARP.convex_equilibria hD hW hWARP

theorem frozen_gorman_iff_direction {α : Type*} [Fintype α] {x : α → ℝ → ι → ℝ}
    (h : ∃ β : ι → ℝ, ∀ a w, x a w = x a 0 + w • β) :
    ∃ X : ℝ → ι → ℝ, ∀ w : α → ℝ, ∑ a, x a (w a) = X (∑ a, w a) :=
  aggregatesThroughWealth_of_gorman h

theorem frozen_gorman_nonneg {α : Type*} [Fintype α] [Nontrivial α] {x : α → ℝ → ι → ℝ}
    (hagg : ∃ X : ℝ → ι → ℝ, ∀ w : α → ℝ, (∀ a, 0 ≤ w a) → ∑ a, x a (w a) = X (∑ a, w a))
    (hc : ∀ a, ContinuousOn (x a) (Set.Ici 0)) :
    ∃ β : ι → ℝ, ∀ a, ∀ w, 0 ≤ w → x a w = x a 0 + w • β :=
  gorman_of_aggregatesThroughWealthNonneg hagg hc

end Aggregation

section Tatonnement

theorem frozen_tatonnementPath_def {ι : Type*} [Fintype ι] (z : (ι → ℝ) → (ι → ℝ))
    (p : ℝ → ι → ℝ) :
    IsTatonnementPath z p ↔ ∀ t, 0 ≤ t → HasDerivWithinAt p (z (p t)) (Set.Ici 0) t := Iff.rfl

theorem frozen_priceDistSq_def {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    priceDistSq p q = ∑ i, (p i - q i) ^ 2 := rfl

theorem frozen_tatonnement_antitone {ι : Type*} [Fintype ι] {z : (ι → ℝ) → (ι → ℝ)}
    {p : ℝ → ι → ℝ} {pstar : ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0)
    (hWA : ∀ t, 0 ≤ t → z (p t) ≠ 0 → 0 < cost pstar (z (p t))) :
    AntitoneOn (fun t => priceDistSq (p t) pstar) (Set.Ici 0) :=
  tatonnement_antitone hpath hW hWA

theorem frozen_tatonnement_strictAnti {ι : Type*} [Fintype ι] {z : (ι → ℝ) → (ι → ℝ)}
    {p : ℝ → ι → ℝ} {pstar : ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0)
    (hWA : ∀ t, 0 ≤ t → z (p t) ≠ 0 → 0 < cost pstar (z (p t)))
    (hne : ∀ t, 0 < t → z (p t) ≠ 0) :
    StrictAntiOn (fun t => priceDistSq (p t) pstar) (Set.Ici 0) :=
  tatonnement_strictAnti hpath hW hWA hne

theorem frozen_grossSubstitutes_cost_pos_two_goods {z : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z)
    (hW : ∀ q, PositivePrices q → cost q (z q) = 0) {pstar q : Fin 2 → ℝ}
    (hps : PositivePrices pstar) (hq : PositivePrices q) (hzs : z pstar = 0) (hzq : z q ≠ 0) :
    0 < cost pstar (z q) :=
  hGS.cost_pos_two_goods hhom hW hps hq hzs hzq

end Tatonnement

section SMD

theorem frozen_openPriceSimplex_def {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    p ∈ openPriceSimplex ι ↔ (∀ i, 0 < p i) ∧ ∑ i, p i = 1 := Iff.rfl

theorem frozen_excessWARP_def {ι : Type*} [Fintype ι] (z : (ι → ℝ) → (ι → ℝ))
    (D : Set (ι → ℝ)) :
    ExcessWARP z D ↔
      ∀ p ∈ D, ∀ p' ∈ D, z p ≠ z p' → cost p (z p') ≤ 0 → 0 < cost p' (z p) := Iff.rfl

theorem frozen_debreu_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {z : (ι → ℝ) → (ι → ℝ)} {c : ℝ} {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι)
    (hW : WalrasLaw z D) (hα : ∀ p ∈ D, ∀ l, 0 < z p l + c * p l) :
    ∃ zs : ι → (ι → ℝ) → (ι → ℝ), (∀ p ∈ D, ∑ l, zs l p = z p) ∧
      ∀ l, WalrasLaw (zs l) D ∧ ExcessWARP (zs l) D :=
  debreu_decomposition hD hW hα

theorem frozen_debreu_decomposition_of_boundedBelow {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι)
    (hW : WalrasLaw z D) {ε s : ℝ} (hε : 0 < ε) (hεD : ∀ p ∈ D, ∀ i, ε ≤ p i)
    (hb : ∀ p ∈ D, ∀ l, -s < z p l) :
    ∃ zs : ι → (ι → ℝ) → (ι → ℝ), (∀ p ∈ D, ∑ l, zs l p = z p) ∧
      ∀ l, WalrasLaw (zs l) D ∧ ExcessWARP (zs l) D :=
  debreu_decomposition_of_boundedBelow hD hW hε hεD hb

theorem frozen_debreuPiece_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : (ι → ℝ) → (ι → ℝ)) (c : ℝ) (l : ι) (p : ι → ℝ) :
    debreuPiece z c l p = (z p l + c * p l) • (Pi.single l 1 - (p l / cost p p) • p) := rfl

theorem frozen_debreu_pieces {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {z : (ι → ℝ) → (ι → ℝ)} {c : ℝ} {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι)
    (hW : WalrasLaw z D) (hα : ∀ p ∈ D, ∀ l, 0 < z p l + c * p l) :
    (∀ p ∈ D, ∑ l, debreuPiece z c l p = z p) ∧
      ∀ l, WalrasLaw (debreuPiece z c l) D ∧ ExcessWARP (debreuPiece z c l) D :=
  ⟨fun p hp => sum_debreuPiece c (hD hp).1 (hW p hp),
    fun l => ⟨walrasLaw_debreuPiece z c l hD, excessWARP_debreuPiece hD fun p hp => hα p hp l⟩⟩

theorem frozen_continuousOn_debreuPiece {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {z : (ι → ℝ) → (ι → ℝ)} (c : ℝ) (l : ι) {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι)
    (hz : ContinuousOn z D) : ContinuousOn (debreuPiece z c l) D :=
  continuousOn_debreuPiece c l hD hz

theorem frozen_zBad_def (p : Fin 2 → ℝ) :
    SMDExamples.zBad p = ![(p 0 - 1 / 4) * (p 0 - 3 / 4),
      -(p 0 * ((p 0 - 1 / 4) * (p 0 - 3 / 4))) / p 1] := rfl

theorem frozen_DBad_def (p : Fin 2 → ℝ) :
    p ∈ SMDExamples.DBad ↔ p ∈ openPriceSimplex (Fin 2) ∧ ∀ i, 1 / 8 ≤ p i := Iff.rfl

theorem frozen_zBad_smd : ¬ ExcessWARP SMDExamples.zBad SMDExamples.DBad ∧
    ∃ zs : Fin 2 → (Fin 2 → ℝ) → (Fin 2 → ℝ), (∀ p ∈ SMDExamples.DBad, ∑ l, zs l p = SMDExamples.zBad p) ∧
      ∀ l, WalrasLaw (zs l) SMDExamples.DBad ∧ ExcessWARP (zs l) SMDExamples.DBad :=
  SMDExamples.zBad_smd

end SMD

section SMDConsumer
/-! Debreu's step 2 (`SMDConsumer.lean`), frozen after the isolated review of
2026-11-24 (`Audit/REVIEW-smd-consumers.md`). -/

open Set

theorem frozen_weightedPiece_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ℝ) → ℝ) (l : ι) (q : ι → ℝ) :
    weightedPiece a l q = a q • (Pi.single l 1 - (q l / cost q q) • q) := rfl

theorem frozen_demand_def {ι : Type*} [Fintype ι] (U : (ι → ℝ) → ℝ) (p : ι → ℝ) (w : ℝ) (x : ι → ℝ) :
    x ∈ demand (prefOf U) p w ↔
      (0 ≤ x ∧ cost p x ≤ w) ∧ ∀ y, (0 ≤ y ∧ cost p y ≤ w) → U y ≤ U x := Iff.rfl

theorem frozen_exists_consumer_weightedPiece {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} (l : ι) (hK : IsCompact K)
    (hKS : K ⊆ openPriceSimplex ι) (ha : ContinuousOn a K) (hapos : ∀ q ∈ K, 0 < a q) :
    ∃ (U : (ι → ℝ) → ℝ) (ω : ι → ℝ), QuasiconcaveOn ℝ univ U ∧ (∀ i, 0 < ω i) ∧
      ∀ p ∈ K, demand (prefOf U) p (cost p ω) = {ω + weightedPiece a l p} :=
  exists_consumer_weightedPiece l hK hKS ha hapos

theorem frozen_sonnenschein_mantel_debreu_quasiconcave {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} {K : Set (ι → ℝ)}
    (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι) (hz : ContinuousOn z K)
    (hW : WalrasLaw z K) :
    ∃ (U : ι → (ι → ℝ) → ℝ) (ω : ι → ι → ℝ),
      (∀ l, QuasiconcaveOn ℝ univ (U l) ∧ ∀ i, 0 < ω l i) ∧
      ∀ p ∈ K, ∃ x : ι → ι → ℝ,
        (∀ l, demand (prefOf (U l)) p (cost p (ω l)) = {x l}) ∧ ∑ l, (x l - ω l) = z p :=
  sonnenschein_mantel_debreu_quasiconcave hK hKS hz hW

theorem frozen_zBad_rational_consumers : ¬ ExcessWARP SMDExamples.zBad SMDExamples.DBad ∧
    ∃ (U : Fin 2 → (Fin 2 → ℝ) → ℝ) (ω : Fin 2 → Fin 2 → ℝ),
      (∀ l, QuasiconcaveOn ℝ univ (U l) ∧ ∀ i, 0 < ω l i) ∧
      ∀ p ∈ SMDExamples.DBad, ∃ x : Fin 2 → Fin 2 → ℝ,
        (∀ l, demand (prefOf (U l)) p (cost p (ω l)) = {x l}) ∧
          ∑ l, (x l - ω l) = SMDExamples.zBad p :=
  SMDExamples.zBad_rational_consumers

end SMDConsumer

end Econ.Audit
