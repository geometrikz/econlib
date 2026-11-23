/-
# Existence of Walrasian equilibrium for any finite number of goods

PLAN.md §1 (M4). `GE/Existence.lean` proves the Gale–Nikaido–Debreu lemma and
existence of a free-disposal equilibrium from the hypothesis
`BrouwerSimplex ι`. Here that hypothesis is **discharged** for every nonempty
finite set of goods, using Brouwer's theorem (`Foundations/FixedPoint.lean`),
so both results become unconditional.

The price simplex is nonempty (uniform prices), convex, and compact (closed
and inside the unit cube), and `ι → ℝ` is a finite-dimensional normed space.

The scope caveat of `GE/Existence.lean` still applies: demand must be defined
and continuous on the whole simplex, including boundary prices, so this does
not yet cover strongly monotone economies (MWG Prop. 17.C.1).
-/
module

public import EconLean.GE.Existence
public import EconLean.Foundations.FixedPoint

@[expose] public section

namespace Econ

open Set

variable {α ι : Type*} [Fintype ι]

/-- The price simplex is convex. -/
theorem convex_priceSimplex : Convex ℝ (priceSimplex ι) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.2, hq.2, mul_one, hab]

/-- The price simplex is compact: it is closed and lies in the unit cube. -/
theorem isCompact_priceSimplex : IsCompact (priceSimplex ι) := by
  have hclosed : IsClosed (priceSimplex ι) := by
    have h1 : IsClosed {p : ι → ℝ | 0 ≤ p} := isClosed_le continuous_const continuous_id
    have h2 : IsClosed {p : ι → ℝ | ∑ i, p i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  refine (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).of_isClosed_subset hclosed ?_
  intro p hp
  exact ⟨hp.1, fun i => le_one_of_mem_priceSimplex hp i⟩

/-- The price simplex is nonempty when there is at least one good. -/
theorem priceSimplex_nonempty [Nonempty ι] : (priceSimplex ι).Nonempty := by
  refine ⟨fun _ => (Fintype.card ι : ℝ)⁻¹, fun i => by positivity, ?_⟩
  simp [Finset.card_univ]

/-- **Brouwer's theorem for the price simplex**, for any nonempty finite set of
goods. This discharges the hypothesis of `GE/Existence.lean`. -/
theorem brouwerSimplex [Nonempty ι] : BrouwerSimplex ι := fun _ hf hmaps =>
  brouwer_fixedPoint convex_priceSimplex isCompact_priceSimplex priceSimplex_nonempty hmaps hf

/-- **Gale–Nikaido–Debreu lemma, unconditional.** If `z` is continuous on the
price simplex and `p · z(p) ≤ 0` there, some price vector in the simplex has
`z(p) ≤ 0`. -/
theorem gale_nikaido_debreu' [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    (hz : ContinuousOn z (priceSimplex ι))
    (hW : ∀ p ∈ priceSimplex ι, cost p (z p) ≤ 0) :
    ∃ p ∈ priceSimplex ι, z p ≤ 0 :=
  gale_nikaido_debreu brouwerSimplex hz hW

namespace ExchangeEconomy

variable [Fintype α]

/-- **Existence of a free-disposal equilibrium, unconditional** (Debreu 1959
§5.6), for any nonempty finite set of goods: with locally nonsatiated consumers
and a demand selection defined and continuous on the whole price simplex. -/
theorem exists_freeDisposalEquilibrium' [Nonempty ι] (E : ExchangeEconomy α ι)
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d : α → (ι → ℝ) → (ι → ℝ)}
    (hd : E.IsDemandSelection d (priceSimplex ι))
    (hc : ∀ a, ContinuousOn (d a) (priceSimplex ι)) :
    ∃ p ∈ priceSimplex ι, E.IsFreeDisposalEquilibrium p (fun a => d a p) :=
  E.exists_freeDisposalEquilibrium brouwerSimplex hlns hd hc

end ExchangeEconomy

/-! ### Non-vacuity witnesses -/

/-- Brouwer holds for three goods, a case `brouwerSimplex_fin_two` did not cover. -/
example : BrouwerSimplex (Fin 3) := brouwerSimplex

/-- The Gale–Nikaido–Debreu hypotheses are satisfiable with three goods and a
nonzero excess demand `z(p) = -p` (`p · z(p) = -∑ pᵢ² ≤ 0`). -/
example : ∃ p ∈ priceSimplex (Fin 3), (fun q : Fin 3 → ℝ => -q) p ≤ 0 :=
  gale_nikaido_debreu' (continuous_neg.continuousOn) fun p _ => by
    simp only [cost, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)

end Econ
