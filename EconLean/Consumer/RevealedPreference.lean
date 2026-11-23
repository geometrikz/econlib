/-
# Revealed preference: WARP and the compensated law of demand

MWG §2.F, §3.J.

**The economics.** Revealed preference asks what *observed choices* say
about preferences, without assuming we can see the utility function.

If the consumer bought `x` at `(p, w)` when `x'` was also affordable
(`p · x' ≤ w`), then `x` is *revealed preferred* to `x'`. The
**Weak Axiom of Revealed Preference (WARP)** says this ranking is never
contradicted: if `x` is revealed preferred to a different bundle `x'`, then
whenever `x'` is chosen, `x` must have been *unaffordable*:

    p · x' ≤ w  and  x' ≠ x   ⟹   p' · x > w'        (MWG Def. 2.F.1)

where `x = x(p, w)` and `x' = x(p', w')`.

Results:
1. Utility maximization with a *unique* optimum satisfies WARP (MWG §3.J).
2. **Compensated law of demand** (MWG Prop. 2.F.1): WARP plus Walras' law
   imply that, after a price change compensated so the old bundle is just
   affordable, demand moves *against* the price change:
   `(p' - p) · (x' - x) ≤ 0`, strictly if demand changed.
   This is the discrete form of the negative semidefiniteness of the Slutsky
   matrix.
-/
import EconLean.Consumer.Demand

namespace Econ

variable {ι : Type*} [Fintype ι]

/-! ### 1. Utility maximization satisfies WARP -/

/-- **Rational choice satisfies WARP.** Suppose at `(p, w)` the unique best
bundle is `x`, and at `(p', w')` it is `x' ≠ x`. If `x'` was affordable at
`(p, w)` then `x` was *not* affordable at `(p', w')`.

Proof: `x ≿ x'` since `x'` was affordable when `x` was chosen. If `x` were
affordable at `(p', w')`, then `x` would beat everything there (through `x'`,
by transitivity), so `x` would be a best bundle at `(p', w')`, contradicting
uniqueness. -/
theorem warp_of_unique_demand {R : (ι → ℝ) → (ι → ℝ) → Prop} (hR : Rational R)
    {p p' : ι → ℝ} {w w' : ℝ} {x x' : ι → ℝ}
    (hx : demand R p w = {x}) (hx' : demand R p' w' = {x'})
    (haff : cost p x' ≤ w) (hne : x' ≠ x) : w' < cost p' x := by
  have hxmem : x ∈ demand R p w := hx ▸ rfl
  have hx'mem : x' ∈ demand R p' w' := hx' ▸ rfl
  by_contra hle
  push Not at hle
  -- `x ≿ x'` because `x'` was affordable at `(p, w)`.
  have hxx' : R x x' := hxmem.2 x' ⟨hx'mem.1.1, haff⟩
  -- So `x` is also a best bundle at `(p', w')` ...
  have : x ∈ demand R p' w' :=
    ⟨⟨hxmem.1.1, hle⟩, fun y hy => hR.trans hxx' (hx'mem.2 y hy)⟩
  -- ... but the only best bundle there is `x'`.
  rw [hx'] at this
  exact hne this.symm

/-- WARP for a demand *function* `x(p, w)` on strictly positive prices and
nonnegative wealth (MWG Def. 2.F.1). -/
def WARP (x : (ι → ℝ) → ℝ → (ι → ℝ)) : Prop :=
  ∀ p w p' w', (∀ i, 0 < p i) → 0 ≤ w → (∀ i, 0 < p' i) → 0 ≤ w' →
    cost p (x p' w') ≤ w → x p' w' ≠ x p w → w' < cost p' (x p w)

/-- If a rational preference has a unique optimum everywhere, its demand
function satisfies WARP. -/
theorem warp_of_rational {R : (ι → ℝ) → (ι → ℝ) → Prop} (hR : Rational R)
    {x : (ι → ℝ) → ℝ → (ι → ℝ)}
    (hx : ∀ p w, (∀ i, 0 < p i) → 0 ≤ w → demand R p w = {x p w}) : WARP x :=
  fun p w p' w' hp hw hp' hw' haff hne =>
    warp_of_unique_demand hR (hx p w hp hw) (hx p' w' hp' hw') haff hne

/-! ### 2. The compensated law of demand (MWG Prop. 2.F.1) -/

/-- **Compensated law of demand.** Let `x = x(p, w)` and `x' = x(p', w')`,
where wealth is *compensated*, `w' = p' · x`, so the old bundle is just
affordable at the new prices. If both choices exhaust wealth (Walras' law)
and WARP holds between them, then `(p' - p) · (x' - x) ≤ 0`.

The hypothesis `hwarp` is WARP applied to this pair (with the roles of the
two situations swapped). -/
theorem compensated_law_of_demand {p p' x x' : ι → ℝ} {w w' : ℝ}
    (hwal : cost p x = w) (hwal' : cost p' x' = w') (hcomp : w' = cost p' x)
    (hwarp : cost p' x ≤ w' → x ≠ x' → w < cost p x') :
    cost (p' - p) (x' - x) ≤ 0 := by
  -- Expand the bilinear expression into four costs.
  rw [cost_sub_left, cost_sub_right, cost_sub_right]
  by_cases hxx : x = x'
  · -- No change in demand: the expression is zero.
    subst hxx
    simp
  · -- Demand changed: WARP says `x'` was unaffordable at the old situation.
    have hlt := hwarp hcomp.ge hxx
    -- `p'x' - p'x - (px' - px) = w' - w' - (px' - w) < 0`.
    linarith

/-- The strict version: if demand actually changes, the inequality is strict. -/
theorem compensated_law_of_demand_strict {p p' x x' : ι → ℝ} {w w' : ℝ}
    (hwal : cost p x = w) (hwal' : cost p' x' = w') (hcomp : w' = cost p' x)
    (hwarp : cost p' x ≤ w' → x ≠ x' → w < cost p x') (hne : x ≠ x') :
    cost (p' - p) (x' - x) < 0 := by
  rw [cost_sub_left, cost_sub_right, cost_sub_right]
  have hlt := hwarp hcomp.ge hne
  linarith

end Econ
