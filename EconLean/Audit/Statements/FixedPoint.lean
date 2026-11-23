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

end Econ.Audit
