/-
# Walrasian demand, Walras' law, and existence of demand

MWG §2.D–2.E, §3.B, §3.D.

**The economics.** The consumer picks a best affordable bundle. Given a
preference `R` on bundles, the **Walrasian demand correspondence** is

    x(p, w) = { x ∈ B(p, w) | x ≿ y for every y ∈ B(p, w) }.

It is a *set* (correspondence), since there may be ties or no best bundle.
Results:
1. **Homogeneity of degree zero**: x(αp, αw) = x(p, w) for α > 0.
2. **Walras' law**: under *local nonsatiation*, every demanded bundle
   exhausts wealth, p · x = w.
3. **Strong monotonicity ⇒ local nonsatiation.**
4. **Existence**: a continuous utility function with strictly positive
   prices and w ≥ 0 has nonempty demand (Weierstrass's extreme value theorem).
5. **Convexity**: convex preferences give a convex demand set.
-/
import EconLean.Preferences.Utility
import EconLean.Consumer.Budget

namespace Econ

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The Walrasian demand correspondence for preference `R`. -/
def demand (R : (ι → ℝ) → (ι → ℝ) → Prop) (p : ι → ℝ) (w : ℝ) : Set (ι → ℝ) :=
  {x | x ∈ budgetSet p w ∧ ∀ y ∈ budgetSet p w, R x y}

variable {R : (ι → ℝ) → (ι → ℝ) → Prop}

/-! ### 1. Homogeneity of degree zero (MWG Prop. 3.D.2(i)) -/

/-- Demand depends only on the budget *set*, which is unchanged by scaling
prices and wealth together. -/
theorem demand_smul {α : ℝ} (hα : 0 < α) (p : ι → ℝ) (w : ℝ) :
    demand R (α • p) (α * w) = demand R p w := by
  -- `simp only [demand, ...]` unfolds and rewrites with `budgetSet_smul`.
  simp only [demand, budgetSet_smul hα]

/-! ### 2. Local nonsatiation and Walras' law (MWG Def. 3.B.3, Prop. 3.D.2(ii))

*Local nonsatiation*: arbitrarily close to any bundle there is a strictly
better one. "Close" uses the distance on `ι → ℝ`. -/

/-- `R` is locally nonsatiated on the consumption set `x ≥ 0`. -/
def LocallyNonsatiated (R : (ι → ℝ) → (ι → ℝ) → Prop) : Prop :=
  ∀ x, 0 ≤ x → ∀ ε > 0, ∃ y, 0 ≤ y ∧ dist y x < ε ∧ P R y x

/-- **Key lemma.** Under local nonsatiation, any bundle that leaves money
unspent (`p · y < w`) can be strictly improved upon *within the budget*.
Proof: cost is continuous, so all bundles near `y` still cost less than `w`;
local nonsatiation finds a better one among them. -/
theorem exists_better_affordable (hlns : LocallyNonsatiated R) {p : ι → ℝ} {w : ℝ}
    {y : ι → ℝ} (hy : 0 ≤ y) (hcost : cost p y < w) :
    ∃ z ∈ budgetSet p w, P R z y := by
  -- Step 1: `cost p z < w` holds for all `z` in some ball around `y`.
  have hev : ∀ᶠ z in 𝓝 y, cost p z < w :=
    (continuous_cost p).continuousAt.eventually (gt_mem_nhds hcost)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  -- Step 2: local nonsatiation gives a strictly better `z` in that ball.
  obtain ⟨z, hz0, hzdist, hzy⟩ := hlns y hy ε hε
  exact ⟨z, ⟨hz0, (hball hzdist).le⟩, hzy⟩

/-- **Walras' law.** With locally nonsatiated preferences, demanded bundles
spend all wealth. -/
theorem walras_law (hlns : LocallyNonsatiated R) {p : ι → ℝ} {w : ℝ} {x : ι → ℝ}
    (hx : x ∈ demand R p w) : cost p x = w := by
  -- We know `p · x ≤ w`; rule out `<` by contradiction.
  refine le_antisymm hx.1.2 (not_lt.1 fun hlt => ?_)
  obtain ⟨z, hzB, hzx⟩ := exists_better_affordable hlns hx.1.1 hlt
  -- `z` is affordable, so `x ≿ z` by optimality; but `z ≻ x`.
  exact hzx.2 (hx.2 z hzB)

/-! ### 3. Monotonicity implies local nonsatiation -/

/-- `R` is *strongly monotone*: more of every good, and strictly more of
some, is strictly better (MWG Def. 3.B.2). -/
def StronglyMonotone (R : (ι → ℝ) → (ι → ℝ) → Prop) : Prop :=
  ∀ x y, 0 ≤ x → x ≤ y → x ≠ y → P R y x

/-- Strong monotonicity implies local nonsatiation (when there is at least one
good). Given `x` and `ε`, add `ε/2` of every good. -/
theorem StronglyMonotone.locallyNonsatiated [Nonempty ι] (hmono : StronglyMonotone R) :
    LocallyNonsatiated R := by
  intro x hx ε hε
  -- The candidate bundle: `y = x + ε/2` in every coordinate.
  set y : ι → ℝ := x + fun _ => ε / 2 with hy
  have hpos : (0 : ℝ) < ε / 2 := half_pos hε
  have hxy : x ≤ y := fun i => by simp [hy, hpos.le]
  refine ⟨y, hx.trans hxy, ?_, hmono x y hx hxy ?_⟩
  · -- Distance in the sup metric is `ε/2 < ε`.
    rw [dist_pi_lt_iff hε]
    intro i
    simp [hy, Real.dist_eq, abs_of_pos hpos, hε]
  · -- `y ≠ x` because they differ in any coordinate `i`.
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h i
    simp [hy] at this
    linarith

/-! ### 4. Existence of demand (MWG Prop. 3.D.1)

We specialize to preferences coming from a utility function `u`
(`prefOf u`, from `Preferences/Utility.lean`). -/

/-- **Existence.** If `u` is continuous, prices are strictly positive and
`w ≥ 0`, then demand is nonempty.

Proof: the budget set is compact and nonempty, and a continuous function on
a nonempty compact set attains its maximum (`IsCompact.exists_isMaxOn`). -/
theorem demand_nonempty {u : (ι → ℝ) → ℝ} (hu : Continuous u) {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) {w : ℝ} (hw : 0 ≤ w) :
    (demand (prefOf u) p w).Nonempty := by
  obtain ⟨x, hxB, hmax⟩ := (isCompact_budgetSet hp w).exists_isMaxOn
    ⟨0, zero_mem_budgetSet hw⟩ hu.continuousOn
  -- `IsMaxOn u B x` says `∀ y ∈ B, u y ≤ u x`, which is `prefOf u x y`.
  exact ⟨x, hxB, fun y hy => hmax hy⟩

/-! ### 5. Convexity of demand (MWG Prop. 3.D.2(iii)) -/

/-- `R` is *convex*: upper contour sets `{y | y ≿ x}` are convex. -/
def ConvexPref (R : (ι → ℝ) → (ι → ℝ) → Prop) : Prop :=
  ∀ x, Convex ℝ {y | R y x}

/-- Convex preferences (and rationality) give a convex demand set. -/
theorem convex_demand (hR : Rational R) (hconv : ConvexPref R) (p : ι → ℝ) (w : ℝ) :
    Convex ℝ (demand R p w) := by
  intro x hx y hy a b ha hb hab
  -- The mix `a x + b y` is affordable (the budget set is convex) ...
  refine ⟨convex_budgetSet p w hx.1 hy.1 ha hb hab, fun z hz => ?_⟩
  -- ... and at least as good as `x`, since both `x, y ≿ x`. Then use
  -- transitivity: `a x + b y ≿ x ≿ z`.
  have hmix : R (a • x + b • y) x :=
    hconv x (hR.refl x) (hy.2 x hx.1) ha hb hab
  exact hR.trans hmix (hx.2 z hz)

end Econ
