/-
# The law of demand and aggregate WARP: preserved by aggregation, and they
# make the equilibrium set convex

PLAN.md §7.2a (bridge B0), row "Law of demand". MWG §4.C (Def. 4.C.1,
Prop. 4.C.1), Def. 17.F.1, Prop. 17.F.1, Prop. 17.F.2.

**The economics.** An excess demand function `z` satisfies

* the **weak axiom** (WARP, MWG Def. 17.F.1) if, whenever `z(p) ≠ z(p')` and
  `p · z(p') ≤ 0`, we have `p' · z(p) > 0`;
* the **(strict) law of demand** if `(p' − p) · (z(p') − z(p)) < 0` whenever
  `z(p) ≠ z(p')`: prices and excess demands move in opposite directions.

Results:
1. **The law of demand survives aggregation** (MWG Prop. 4.C.1 for excess
   demand): if every consumer's excess demand satisfies it, so does the
   aggregate. (Unlike WARP itself, which is *not* preserved by adding up.)
2. Under Walras' law, the **law of demand implies WARP** (MWG Prop. 17.F.2 is
   the analogous statement for the uniqueness argument).
3. **WARP makes the equilibrium price set convex** (MWG Prop. 17.F.1): if `p`
   and `p'` are equilibria, so is every convex combination. Together with
   homogeneity this is the "uniqueness up to a convex set" that SMD otherwise
   rules out.

All statements are about excess-demand functions on a set `D` of price vectors
(e.g. strictly positive prices), so they apply equally to a consumer, a
market, or a macro aggregate.
-/
module

public import EconLean.Consumer.Budget

@[expose] public section

namespace Econ

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Walras' law** for excess demand on a set of prices `D`: `p · z(p) = 0`. -/
def WalrasLaw (z : (ι → ℝ) → (ι → ℝ)) (D : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ D, cost p (z p) = 0

/-- **Weak axiom of revealed preference** for excess demand on `D`
(MWG Def. 17.F.1). -/
def ExcessWARP (z : (ι → ℝ) → (ι → ℝ)) (D : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ D, ∀ p' ∈ D, z p ≠ z p' → cost p (z p') ≤ 0 → 0 < cost p' (z p)

/-- **Strict law of demand** on `D`: `(p' − p) · (z(p') − z(p)) < 0` whenever
excess demand differs. -/
def LawOfDemand (z : (ι → ℝ) → (ι → ℝ)) (D : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ D, ∀ p' ∈ D, z p ≠ z p' → cost (p' - p) (z p' - z p) < 0

/-- The weak (non-strict) law of demand on `D`. -/
def WeakLawOfDemand (z : (ι → ℝ) → (ι → ℝ)) (D : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ D, ∀ p' ∈ D, cost (p' - p) (z p' - z p) ≤ 0

/-- The strict law implies the weak one. -/
theorem LawOfDemand.weak {z : (ι → ℝ) → (ι → ℝ)} {D : Set (ι → ℝ)} (h : LawOfDemand z D) :
    WeakLawOfDemand z D := by
  intro p hp p' hp'
  by_cases hz : z p = z p'
  · simp [hz, cost]
  · exact (h p hp p' hp' hz).le

/-! ### 1. Preservation under aggregation (MWG Prop. 4.C.1) -/

/-- **The law of demand is preserved under aggregation.** If each consumer
`a ∈ s` satisfies the strict law of demand, so does the sum of their excess
demands. (If the aggregate changes, some consumer's excess demand changed, and
that consumer's term is strictly negative.) -/
theorem LawOfDemand.sum {α : Type*} (s : Finset α) {z : α → (ι → ℝ) → (ι → ℝ)}
    {D : Set (ι → ℝ)} (h : ∀ a ∈ s, LawOfDemand (z a) D) :
    LawOfDemand (fun p => ∑ a ∈ s, z a p) D := by
  intro p hp p' hp' hne
  -- Some consumer's excess demand differs.
  obtain ⟨b, hb, hbne⟩ : ∃ b ∈ s, z b p ≠ z b p' := by
    by_contra hall
    push Not at hall
    exact hne (Finset.sum_congr rfl hall)
  have hsplit : cost (p' - p) ((∑ a ∈ s, z a p') - ∑ a ∈ s, z a p)
      = ∑ a ∈ s, cost (p' - p) (z a p' - z a p) := by
    rw [← Finset.sum_sub_distrib]
    simp only [cost, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have hsum : (∑ a ∈ s, cost (p' - p) (z a p' - z a p)) < ∑ a ∈ s, (0 : ℝ) :=
    Finset.sum_lt_sum (fun a ha => (h a ha).weak p hp p' hp')
      ⟨b, hb, h b hb p hp p' hp' hbne⟩
  show cost (p' - p) ((∑ a ∈ s, z a p') - ∑ a ∈ s, z a p) < 0
  rw [hsplit]
  simpa using hsum

/-! ### 2. Law of demand ⇒ WARP, under Walras' law -/

/-- With Walras' law, the strict law of demand implies the weak axiom for
excess demand. Expanding `(p' − p) · (z(p') − z(p)) < 0` with `p · z(p) = 0`
and `p' · z(p') = 0` gives `p' · z(p) + p · z(p') > 0`.

**Caution (review finding).** On a cone of prices with excess demand
homogeneous of degree zero (the endowment-economy setting), Walras' law and the
strict law of demand together force `z ≡ 0`: scaling `p'` up makes the law of
demand fail. The law of demand is meant for demand *at fixed wealth* (MWG 4.C)
or on a normalized price slice; this lemma is the algebraic step only. The
WARP ⇒ convex-equilibria theorem below does not have this problem (see the
`zCD` example, which satisfies WARP on all positive prices). -/
theorem LawOfDemand.excessWARP {z : (ι → ℝ) → (ι → ℝ)} {D : Set (ι → ℝ)}
    (hW : WalrasLaw z D) (hL : LawOfDemand z D) : ExcessWARP z D := by
  intro p hp p' hp' hne hle
  have h := hL p hp p' hp' hne
  rw [cost_sub_left, cost_sub_right, cost_sub_right, hW p hp, hW p' hp'] at h
  linarith

/-! ### 3. WARP ⇒ the equilibrium set is convex (MWG Prop. 17.F.1) -/

/-- **MWG Prop. 17.F.1.** If excess demand satisfies Walras' law and the weak
axiom on a convex set of prices `D`, then the set of equilibrium prices
`{p ∈ D | z(p) = 0}` is convex.

Proof: let `p, p'` be equilibria and `q = a p + b p'`. Walras' law gives
`a p · z(q) + b p' · z(q) = 0`, so one of `p · z(q)`, `p' · z(q)` is `≤ 0`.
If `z(q) ≠ 0`, WARP then forces `q · z(p) > 0` (or `q · z(p') > 0`), which is
impossible since `z(p) = z(p') = 0`. -/
theorem ExcessWARP.convex_equilibria {z : (ι → ℝ) → (ι → ℝ)} {D : Set (ι → ℝ)}
    (hD : Convex ℝ D) (hW : WalrasLaw z D) (hWARP : ExcessWARP z D) :
    Convex ℝ {p | p ∈ D ∧ z p = 0} := by
  rintro p ⟨hp, hzp⟩ p' ⟨hp', hzp'⟩ a b ha hb hab
  set q := a • p + b • p' with hq
  have hqD : q ∈ D := hD hp hp' ha hb hab
  refine ⟨hqD, ?_⟩
  by_contra hzq
  have hWq := hW q hqD
  have hsplit : cost q (z q) = a * cost p (z q) + b * cost p' (z q) := by
    rw [hq, cost_add_left, cost_smul_left, cost_smul_left]
  -- One of the two terms is `≤ 0`.
  rcases le_or_gt (cost p (z q)) 0 with h1 | h1
  · have := hWARP p hp q hqD (by rw [hzp]; exact Ne.symm hzq) h1
    rw [hzp] at this
    simp [cost] at this
  · have h2 : cost p' (z q) ≤ 0 := by
      by_contra h2
      push Not at h2
      have : 0 < a * cost p (z q) + b * cost p' (z q) := by
        rcases ha.lt_or_eq with ha' | ha'
        · nlinarith [mul_pos ha' h1, mul_nonneg hb h2.le]
        · subst ha'
          have hb1 : b = 1 := by linarith
          subst hb1
          linarith
      linarith
    have := hWARP p' hp' q hqD (by rw [hzp']; exact Ne.symm hzq) h2
    rw [hzp'] at this
    simp [cost] at this

end Econ
