/-
# Aggregation of supply and efficient production

MWG §5.E (Prop. 5.E.1) and §5.F (Props. 5.F.1, 5.F.2).

**Aggregation.** With firms `j ∈ J` and production sets `Yⱼ`, the
aggregate production set is the Minkowski sum `Y = ∑ⱼ Yⱼ`. MWG Prop. 5.E.1:
the aggregate firm behaves exactly like the collection of firms,

    π(p) = ∑ⱼ πⱼ(p)    and    y(p) = ∑ⱼ yⱼ(p).

So for producers (unlike consumers, see SMD) aggregation is exact: there
is a "representative firm" with no restrictions. This is the cleanest
micro-to-macro bridge in the canon (PLAN §7.2, bridge B1), and it is why
aggregate production functions are routine in macro while aggregate
demand needs Gorman-type restrictions.

**Efficiency.** A plan `y ∈ Y` is *efficient* if no other feasible plan
produces weakly more of every good and strictly more of some. Prop 5.F.1
(a "first welfare theorem" for one firm): a profit maximizer at strictly
positive prices is efficient. Prop 5.F.2 (a "second welfare theorem"):
with convex `Y`, every efficient plan maximizes profit at some nonzero
price vector `p ≥ 0`. The proof uses a separating hyperplane, which is the
same tool the Second Welfare Theorem (M4) will need.
-/
module

public import EconLean.Producer.Production
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

namespace Econ

open Filter Topology Set

variable {ι : Type*} [Fintype ι]

/-! ### Aggregation (MWG §5.E) -/

section Aggregation

variable {J : Type*} [Fintype J]

/-- The **aggregate production set** `∑ⱼ Yⱼ`: all sums of individually
feasible plans. -/
def aggregate (Ys : J → Set (ι → ℝ)) : Set (ι → ℝ) :=
  {y | ∃ ys : J → ι → ℝ, (∀ j, ys j ∈ Ys j) ∧ y = ∑ j, ys j}

/-- The value of a sum is the sum of the values. -/
theorem cost_univ_sum (p : ι → ℝ) (ys : J → ι → ℝ) : cost p (∑ j, ys j) = ∑ j, cost p (ys j) := by
  simp only [cost, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

variable {Ys : J → Set (ι → ℝ)} {p : ι → ℝ}

/-- Summing individual supplies gives an aggregate supply (MWG 5.E.1, ⊇). -/
theorem sum_mem_supply_aggregate {ys : J → ι → ℝ} (h : ∀ j, ys j ∈ supply (Ys j) p) :
    ∑ j, ys j ∈ supply (aggregate Ys) p := by
  refine ⟨⟨ys, fun j => (h j).1, rfl⟩, ?_⟩
  rintro _ ⟨ys', hys', rfl⟩
  show cost p (∑ j, ys' j) ≤ cost p (∑ j, ys j)
  rw [cost_univ_sum, cost_univ_sum]
  exact Finset.sum_le_sum fun j _ => (h j).2 _ (hys' j)

/-- Every decomposition of an aggregate supply into feasible individual plans
consists of individual supplies. -/
theorem mem_supply_of_sum_mem_supply_aggregate [DecidableEq J] {ys : J → ι → ℝ} (hys : ∀ j, ys j ∈ Ys j)
    (h : ∑ j, ys j ∈ supply (aggregate Ys) p) (j : J) : ys j ∈ supply (Ys j) p := by
  refine ⟨hys j, fun y' hy' => ?_⟩
  -- Replace firm `j`'s plan by `y'`; the aggregate can't do better.
  show cost p y' ≤ cost p (ys j)
  have hagg : cost p (∑ k, Function.update ys j y' k) ≤ cost p (∑ k, ys k) := h.2 _ ⟨Function.update ys j y', fun k => by
    rcases eq_or_ne k j with rfl | hk
    · simpa using hy'
    · simpa [hk] using hys k, rfl⟩
  rw [cost_univ_sum, cost_univ_sum] at hagg
  have hsplit : ∀ g : J → ι → ℝ, ∑ k, cost p (g k) =
      cost p (g j) + ∑ k ∈ Finset.univ.erase j, cost p (g k) := fun g =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  rw [hsplit, hsplit ys] at hagg
  have hrest : ∑ k ∈ Finset.univ.erase j, cost p (Function.update ys j y' k) =
      ∑ k ∈ Finset.univ.erase j, cost p (ys k) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest, Function.update_self] at hagg
  linarith

/-- **Aggregate supply = sum of individual supplies** (MWG Prop. 5.E.1 (ii)). -/
theorem supply_aggregate [DecidableEq J] (y : ι → ℝ) :
    y ∈ supply (aggregate Ys) p ↔ ∃ ys : J → ι → ℝ, (∀ j, ys j ∈ supply (Ys j) p) ∧ y = ∑ j, ys j := by
  constructor
  · intro h
    obtain ⟨ys, hys, rfl⟩ := h.1
    exact ⟨ys, mem_supply_of_sum_mem_supply_aggregate hys h, rfl⟩
  · rintro ⟨ys, hys, rfl⟩
    exact sum_mem_supply_aggregate hys

/-- **Aggregate profit = sum of individual profits** (MWG Prop. 5.E.1 (i)).
Only finiteness of each firm's profit is needed (no maximizer has to exist):
each `Yⱼ` nonempty with profits bounded above at `p`. -/
theorem profit_aggregate (hne : ∀ j, (Ys j).Nonempty)
    (hb : ∀ j, BddAbove ((fun y => cost p y) '' Ys j)) :
    profit (aggregate Ys) p = ∑ j, profit (Ys j) p := by
  classical
  have hle : ∀ y ∈ aggregate Ys, cost p y ≤ ∑ j, profit (Ys j) p := by
    rintro _ ⟨ys, hys, rfl⟩
    rw [cost_univ_sum]
    exact Finset.sum_le_sum fun j _ => cost_le_profit (hb j) (hys j)
  have hAne : (aggregate Ys).Nonempty := by
    choose ys hys using hne
    exact ⟨_, ys, hys, rfl⟩
  have hbA : BddAbove ((fun y => cost p y) '' aggregate Ys) :=
    ⟨_, by rintro _ ⟨y, hy, rfl⟩; exact hle y hy⟩
  apply le_antisymm
  · rw [profit_def]
    exact csSup_le (hAne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hle y hy)
  · -- Pick `δ/(n+1)`-optimal plans for each firm and add them up.
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set n : ℝ := (Fintype.card J : ℝ)
    have hn : 0 ≤ n := Nat.cast_nonneg _
    set ε := δ / (n + 1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    have hnear : ∀ j, ∃ y ∈ Ys j, profit (Ys j) p - ε < cost p y := fun j => by
      obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ :=
        exists_lt_of_lt_csSup ((hne j).image _) (sub_lt_self (profit (Ys j) p) hε)
      exact ⟨y, hy, h⟩
    choose ys hys hlt using hnear
    have hagg : cost p (∑ j, ys j) ≤ profit (aggregate Ys) p :=
      cost_le_profit hbA ⟨ys, hys, rfl⟩
    rw [cost_univ_sum] at hagg
    have hsum : ∑ j, profit (Ys j) p - n * ε ≤ ∑ j, cost p (ys j) := by
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hlt j).le
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
      exact this
    have hnε : n * ε < δ := by
      calc n * ε < (n + 1) * ε := by nlinarith
        _ = δ := by simp only [ε]; field_simp
    linarith

/-- The same, stated with attained maxima. -/
theorem profit_aggregate_of_supply (h : ∀ j, (supply (Ys j) p).Nonempty) :
    profit (aggregate Ys) p = ∑ j, profit (Ys j) p := by
  choose ys hys using h
  rw [profit_eq (sum_mem_supply_aggregate hys), cost_univ_sum]
  exact Finset.sum_congr rfl fun j _ => (profit_eq (hys j)).symm

/-- **Witness for `profit_aggregate`.** Two free-disposal firms
`Yⱼ = {y ≤ ȳⱼ}` at strictly positive prices satisfy its hypotheses. -/
example {ι : Type*} [Fintype ι] (ybar : Fin 2 → ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    (∀ j, (Iic (ybar j)).Nonempty) ∧ (∀ j, BddAbove ((fun y => cost p y) '' Iic (ybar j))) ∧
      profit (aggregate fun j => Iic (ybar j)) p = ∑ j, profit (Iic (ybar j)) p := by
  have hne : ∀ j, (Iic (ybar j)).Nonempty := fun j => nonempty_Iic
  have hb : ∀ j, BddAbove ((fun y => cost p y) '' Iic (ybar j)) := fun j =>
    ⟨cost p (ybar j), by
      rintro _ ⟨y, hy, rfl⟩
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hp i).le⟩
  exact ⟨hne, hb, profit_aggregate hne hb⟩

end Aggregation

/-! ### Efficient production (MWG §5.F) -/

/-- A plan is **efficient** in `Y` (MWG Def. 5.F.1) if it is feasible and no
feasible plan is weakly larger in every coordinate and different. -/
def Efficient (Y : Set (ι → ℝ)) (y : ι → ℝ) : Prop :=
  y ∈ Y ∧ ∀ y' ∈ Y, y ≤ y' → y' = y

variable {Y : Set (ι → ℝ)}

/-- **Profit maximization at `p ≫ 0` implies efficiency** (MWG Prop. 5.F.1).
A version of the First Welfare Theorem for a single firm. -/
theorem efficient_of_mem_supply {p y : ι → ℝ} (hp : ∀ i, 0 < p i) (hy : y ∈ supply Y p) :
    Efficient Y y := by
  refine ⟨hy.1, fun y' hy' hle => ?_⟩
  by_contra hne
  -- Some coordinate is strictly larger, so `p · y' > p · y`.
  obtain ⟨i, hi⟩ : ∃ i, y i < y' i := by
    by_contra h
    push Not at h
    exact hne (funext fun i => le_antisymm (h i) (hle i))
  have hlt : cost p y < cost p y' :=
    Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hp j).le)
      ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hi (hp i)⟩
  exact absurd (hy.2 y' hy') (not_le.2 hlt)

/-- **Efficient plans are supported by prices** (MWG Prop. 5.F.2). If `Y`
is convex and `y` is efficient, there is a price vector `p ≥ 0`, `p ≠ 0`,
at which `y` maximizes profit.

Proof: the open convex set `{a | a ≫ y}` misses `Y` (efficiency), so a
continuous linear functional `f` separates them (Hahn–Banach). Prices are
`pᵢ = -f(eᵢ)`. -/
theorem exists_price_of_efficient [Nonempty ι] (hY : Convex ℝ Y) {y : ι → ℝ} (hy : Efficient Y y) :
    ∃ p : ι → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ y ∈ supply Y p := by
  classical
  -- The strictly-dominating plans.
  set S : Set (ι → ℝ) := Set.pi univ fun i => Ioi (y i) with hS
  have hSo : IsOpen S := isOpen_set_pi finite_univ fun i _ => isOpen_Ioi
  have hSc : Convex ℝ S := convex_pi fun i _ => convex_Ioi (y i)
  have hdisj : Disjoint S Y := by
    rw [Set.disjoint_left]
    intro a ha haY
    have hle : y ≤ a := fun i => (ha i (mem_univ i)).le
    have := hy.2 a haY hle
    subst this
    exact lt_irrefl _ (ha (Classical.arbitrary ι) (mem_univ _))
  obtain ⟨f, u, hfS, hfY⟩ := geometric_hahn_banach_open hSc hSo hY hdisj
  -- Prices from the functional.
  set p : ι → ℝ := fun i => -f ((fun j => if i = j then (1 : ℝ) else 0)) with hp
  have hcost : ∀ x, cost p x = -f x := by
    intro x
    rw [show f x = f.toLinearMap x from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp [cost, hp, Finset.sum_neg_distrib, mul_comm]
  -- `y + t • 1` (and more) strictly dominate `y`.
  have hmemS : ∀ v : ι → ℝ, (∀ i, 0 < v i) → y + v ∈ S :=
    fun v hv i _ => by simpa using hv i
  refine ⟨p, ?_, ?_, hy.1, ?_⟩
  · -- `p ≥ 0`: otherwise pushing far along `eᵢ` would break `f < u` on `S`.
    intro i
    by_contra hneg
    push Not at hneg
    have hfi : 0 < f ((fun j => if i = j then (1 : ℝ) else 0)) := by simp only [hp, Pi.zero_apply] at hneg; linarith
    set t : ℝ := (|u - f (y + 1)| + 1) / f ((fun j => if i = j then (1 : ℝ) else 0))
    have ht : 0 ≤ t := div_nonneg (by positivity) hfi.le
    have hin := hfS _ (hmemS (1 + t • (fun j => if i = j then (1 : ℝ) else 0)) fun j => by
      have : 0 ≤ t * (if i = j then (1 : ℝ) else 0) := mul_nonneg ht (by split_ifs <;> norm_num)
      simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]; linarith)
    rw [← add_assoc, map_add, map_smul, smul_eq_mul] at hin
    have : t * f ((fun j => if i = j then (1 : ℝ) else 0)) = |u - f (y + 1)| + 1 := div_mul_cancel₀ _ hfi.ne'
    have := le_abs_self (u - f (y + 1))
    linarith
  · -- `p ≠ 0`: otherwise `f = 0`, contradicting `f < u ≤ f` across the sets.
    intro hp0
    have hf0 : ∀ x, f x = 0 := fun x => by
      have := hcost x; rw [hp0] at this; simp [cost] at this; linarith
    have h1 := hfS _ (hmemS 1 fun _ => one_pos)
    have h2 := hfY y hy.1
    rw [hf0] at h1 h2
    linarith
  · -- `y` maximizes `p · ·` on `Y`: `p · b ≤ -u < p · (y + ε 1)` for all `ε > 0`.
    intro b hb
    have hb' : cost p b ≤ -u := by rw [hcost]; linarith [hfY b hb]
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set s : ℝ := ∑ i, p i
    set ε : ℝ := δ / (|s| + 1)
    have hε : 0 < ε := div_pos hδ (by positivity)
    have hin := hfS _ (hmemS (fun _ => ε) fun _ => hε)
    have hval : cost p (y + fun _ => ε) = cost p y + ε * s := by
      rw [cost_add_right]; simp [cost, s, Finset.sum_mul, mul_comm]
    have hlt : -u < cost p (y + fun _ => ε) := by rw [hcost]; linarith
    have hεs : ε * s < δ := by
      calc ε * s ≤ ε * |s| := mul_le_mul_of_nonneg_left (le_abs_self s) hε.le
        _ < ε * (|s| + 1) := mul_lt_mul_of_pos_left (by linarith) hε
        _ = δ := div_mul_cancel₀ _ (by positivity)
    linarith

/-- **Witness for 5.F.2.** In the convex technology `{y | y₀ + y₁ ≤ 0}`
(one unit of good 1 makes one unit of good 0), the plan `(1, -1)` is
efficient, so it is supported by some nonzero `p ≥ 0`. -/
example : Convex ℝ {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} ∧
    Efficient {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} ![1, -1] ∧
    ∃ p : Fin 2 → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ ![1, -1] ∈ supply {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} p := by
  have hconv : Convex ℝ {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} := by
    intro y hy y' hy' a b ha hb _
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hy' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hy ha, mul_le_mul_of_nonneg_left hy' hb]
  have heff : Efficient {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0} ![1, -1] := by
    refine ⟨by simp, fun y' hy' hle => ?_⟩
    have h0 := hle 0
    have h1 := hle 1
    simp only [mem_ofPred_eq] at hy'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    funext i
    fin_cases i <;> simp <;> linarith
  exact ⟨hconv, heff, exists_price_of_efficient hconv heff⟩

end Econ
