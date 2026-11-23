/-
# Commodity space, prices and budget sets

MWG §2.B–2.D.

**The economics.** There are finitely many commodities, indexed by a finite
type `ι` (think `ι = Fin L` for L goods). A *bundle* is a vector `x : ι → ℝ`
assigning a quantity to each good; the consumption set is the nonnegative
orthant `x ≥ 0`. Given prices `p : ι → ℝ` and wealth `w : ℝ`, the cost of a
bundle is `p · x = ∑ᵢ pᵢ xᵢ`, and the **Walrasian budget set** is

    B(p, w) = { x ≥ 0 | p · x ≤ w }.

Facts proved here:
* `B(αp, αw) = B(p, w)` for α > 0: only *relative* prices matter.
* `B(p, w)` is convex.
* `B(p, w)` is closed, and if all prices are strictly positive it is
  *compact*. Compactness is what makes demand exist (`Demand.lean`).

**The Lean.** `ι → ℝ` already carries all the structure we need from
Mathlib: it is an ordered vector space (`x ≤ y` means `∀ i, x i ≤ y i`), and a
metric space with the *sup* distance `dist x y = maxᵢ |xᵢ - yᵢ|`.
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Pi

@[expose] public section

namespace Econ

-- `ι` indexes commodities; `[Fintype ι]` says there are finitely many.
variable {ι : Type*} [Fintype ι]

/-- The cost `p · x = ∑ᵢ pᵢ xᵢ` of bundle `x` at prices `p`. -/
def cost (p x : ι → ℝ) : ℝ := ∑ i, p i * x i

section CostLemmas

/-- Cost is linear in prices: scaling prices scales cost. -/
theorem cost_smul_left (α : ℝ) (p x : ι → ℝ) : cost (α • p) x = α * cost p x := by
  -- `Finset.mul_sum` pulls a constant out of a sum.
  simp [cost, Finset.mul_sum, mul_assoc]

/-- Cost is linear in quantities. -/
theorem cost_smul_right (α : ℝ) (p x : ι → ℝ) : cost p (α • x) = α * cost p x := by
  simp only [cost, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem cost_add_right (p x y : ι → ℝ) : cost p (x + y) = cost p x + cost p y := by
  simp [cost, mul_add, Finset.sum_add_distrib]

theorem cost_add_left (p q x : ι → ℝ) : cost (p + q) x = cost p x + cost q x := by
  simp [cost, add_mul, Finset.sum_add_distrib]

theorem cost_sub_left (p q x : ι → ℝ) : cost (p - q) x = cost p x - cost q x := by
  simp [cost, sub_mul, Finset.sum_sub_distrib]

theorem cost_sub_right (p x y : ι → ℝ) : cost p (x - y) = cost p x - cost p y := by
  simp [cost, mul_sub, Finset.sum_sub_distrib]

/-- Nonnegative prices and quantities give nonnegative cost. -/
theorem cost_nonneg {p x : ι → ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) : 0 ≤ cost p x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hx i))

/-- With strictly positive prices, a nonnegative bundle costs zero only if it
is the zero bundle. -/
theorem eq_zero_of_cost_eq_zero {p x : ι → ℝ} (hp : ∀ i, 0 < p i) (hx : 0 ≤ x)
    (h : cost p x = 0) : x = 0 := by
  -- A sum of nonnegative terms is zero iff every term is zero.
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hp i).le (hx i))).1 h
  funext i
  have := hterms i (Finset.mem_univ i)
  -- `pᵢ xᵢ = 0` and `pᵢ ≠ 0` force `xᵢ = 0`.
  exact (mul_eq_zero.1 this).resolve_left (hp i).ne'

/-- Cost is continuous in the bundle (it is a finite sum of continuous
functions). -/
theorem continuous_cost (p : ι → ℝ) : Continuous (cost p) := by
  unfold cost
  fun_prop

end CostLemmas

/-- The Walrasian budget set `B(p, w) = {x ≥ 0 | p · x ≤ w}`. -/
def budgetSet (p : ι → ℝ) (w : ℝ) : Set (ι → ℝ) := {x | 0 ≤ x ∧ cost p x ≤ w}

theorem mem_budgetSet {p : ι → ℝ} {w : ℝ} {x : ι → ℝ} :
    x ∈ budgetSet p w ↔ 0 ≤ x ∧ cost p x ≤ w := Iff.rfl

/-- **Only relative prices matter.** Scaling all prices and wealth by the same
α > 0 leaves the budget set unchanged (MWG §2.D). -/
theorem budgetSet_smul {α : ℝ} (hα : 0 < α) (p : ι → ℝ) (w : ℝ) :
    budgetSet (α • p) (α * w) = budgetSet p w := by
  ext x
  simp only [mem_budgetSet, cost_smul_left]
  -- `mul_le_mul_iff_right₀`: for α > 0, α a ≤ α b ↔ a ≤ b.
  rw [mul_le_mul_iff_right₀ hα]

/-- If wealth is nonnegative, the zero bundle is affordable, so the budget set
is nonempty. -/
theorem zero_mem_budgetSet {p : ι → ℝ} {w : ℝ} (hw : 0 ≤ w) : (0 : ι → ℝ) ∈ budgetSet p w :=
  ⟨le_rfl, by simpa [cost] using hw⟩

/-- **The budget set is convex** (MWG §2.D). It is the intersection of the
convex cone `x ≥ 0` with a half-space `{x | p · x ≤ w}`. -/
theorem convex_budgetSet (p : ι → ℝ) (w : ℝ) : Convex ℝ (budgetSet p w) := by
  -- The half-space is convex because `cost p` is a linear map.
  have hlin : IsLinearMap ℝ (cost p) :=
    ⟨cost_add_right p, fun c x => by simp [cost_smul_right, smul_eq_mul]⟩
  exact (convex_Ici 0).inter (convex_halfSpace_le hlin w)

/-- The budget set is closed: it is cut out by the non-strict inequalities
`0 ≤ x` and `cost p x ≤ w` between continuous functions. -/
theorem isClosed_budgetSet (p : ι → ℝ) (w : ℝ) : IsClosed (budgetSet p w) :=
  (isClosed_le continuous_const continuous_id).inter
    (isClosed_le (continuous_cost p) continuous_const)

/-- With positive prices, each good is bounded in the budget set:
`xᵢ ≤ w / pᵢ` (you can't buy more of good i than your whole wealth buys). -/
theorem le_div_of_mem_budgetSet {p : ι → ℝ} (hp : ∀ i, 0 < p i) {w : ℝ}
    {x : ι → ℝ} (hx : x ∈ budgetSet p w) (i : ι) : x i ≤ w / p i := by
  rw [le_div_iff₀ (hp i), mul_comm]
  -- `pᵢ xᵢ` is one of the nonnegative terms of the sum `p · x ≤ w`.
  calc p i * x i ≤ cost p x :=
        Finset.single_le_sum (f := fun j => p j * x j)
          (fun j _ => mul_nonneg (hp j).le (hx.1 j)) (Finset.mem_univ i)
    _ ≤ w := hx.2

/-- **The budget set is compact when prices are strictly positive.**
It sits inside the box `[0, w/p]`, which is compact (Mathlib's
`CompactIccSpace` instance for `ι → ℝ`), and it is closed. -/
theorem isCompact_budgetSet {p : ι → ℝ} (hp : ∀ i, 0 < p i) (w : ℝ) :
    IsCompact (budgetSet p w) := by
  refine (isCompact_Icc (a := (0 : ι → ℝ)) (b := fun i => w / p i)).of_isClosed_subset
    (isClosed_budgetSet p w) ?_
  intro x hx
  exact ⟨hx.1, fun i => le_div_of_mem_budgetSet hp hx i⟩

end Econ
