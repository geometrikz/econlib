/-
# Existence of Walrasian equilibrium from preferences (MWG Prop. 17.B.2 + 17.C.1)

PLAN.md §1 (M4). MWG Prop. 17.B.2, 17.C.1; Debreu (1959) §5.

**The economics.** `GE/ExistenceInterior.lean` proves existence from properties
of aggregate excess demand. Here those properties are derived from the
primitives of an exchange economy whose consumers have

* continuous utility functions `uₐ` (`E.pref a = prefOf uₐ`),
* strictly quasiconcave utility (so demand is a continuous function),
* strongly monotone preferences,
* nonzero endowments `ωₐ ≥ 0` with strictly positive aggregate endowment `ω̄ ≫ 0`.

Then (MWG 17.B.2):
* excess demand is continuous on `p ≫ 0` (Berge, `Consumer/Continuity.lean`);
* Walras' law holds (local nonsatiation);
* excess demand is bounded below by `−ω̄`;
* the **boundary condition** holds: if `pⁿ → p̄ ≠ 0` with `p̄ₗ = 0`, some
  consumer with positive wealth at `p̄` demands unboundedly much. Otherwise,
  along a subsequence their demand converges to some `x̄` affordable at `p̄`;
  but good `l` is free at `p̄`, so `t x̄ + eₗ` (for `t < 1` near `1`) is strictly
  cheaper than their wealth and strictly better than `x̄` by strong
  monotonicity and continuity, hence affordable and better than their demand
  at `pⁿ` for large `n`, contradicting optimality in the limit.

So a Walrasian equilibrium with strictly positive prices exists
(`exists_walrasianEquilibrium_of_preferences`), e.g. for Cobb–Douglas-like
economies that the closed-simplex theorem cannot handle.
-/
module

public import EconLean.GE.ExistenceInterior
public import EconLean.Consumer.Continuity
public import EconLean.GE.Examples
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

namespace Econ

namespace ExchangeEconomy

open Filter Topology Set

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- **The boundary condition from strong monotonicity** (MWG Prop. 17.B.2(v)).
If utilities are continuous and preferences strongly monotone, and the aggregate
endowment is strictly positive, then for any demand selection on strictly
positive prices, aggregate excess demand satisfies the boundary condition. -/
theorem boundaryCondition_excessDemand (E : ExchangeEconomy α ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hmono : ∀ a, StronglyMonotone (E.pref a)) (hω : PositivePrices E.totalEndowment)
    {d : α → (ι → ℝ) → (ι → ℝ)} (hd : E.IsDemandSelection d {p | PositivePrices p}) :
    BoundaryCondition (E.excessDemand d) := by
  classical
  intro pn pbar hpos hlim hne ⟨l, hl⟩ M
  have hcoord : ∀ i, Tendsto (fun n => pn n i) atTop (𝓝 (pbar i)) := fun i =>
    ((continuous_apply i).tendsto pbar).comp hlim
  have hpbar0 : 0 ≤ pbar := fun i => ge_of_tendsto' (hcoord i) fun n => (hpos n i).le
  -- Demand is nonnegative and affordable.
  have hdmem : ∀ n a, d a (pn n) ∈ demand (E.pref a) (pn n) (E.wealth (pn n) a) :=
    fun n a => hd (pn n) (hpos n) a
  -- Some consumer has positive wealth at `p̄`.
  obtain ⟨a, ha⟩ : ∃ a, 0 < cost pbar (E.endow a) := by
    have htot : 0 < cost pbar E.totalEndowment := by
      obtain ⟨i, hi⟩ : ∃ i, pbar i ≠ 0 := by
        by_contra h; push Not at h; exact hne (funext h)
      have hpi : 0 < pbar i := lt_of_le_of_ne (hpbar0 i) (Ne.symm hi)
      exact Finset.sum_pos' (fun j _ => mul_nonneg (hpbar0 j) (hω j).le)
        ⟨i, Finset.mem_univ i, mul_pos hpi (hω i)⟩
    rw [totalEndowment, cost_sum] at htot
    by_contra h; push Not at h
    exact absurd htot (not_lt.2 (Finset.sum_nonpos fun a _ => h a))
  -- Key claim: consumer `a`'s demand is eventually large in some good.
  have hkey : ∀ M' : ℝ, ∀ᶠ n in atTop, ∃ k, M' < d a (pn n) k := by
    intro M'
    by_contra hcon
    rw [not_eventually] at hcon
    simp only [not_exists, not_lt] at hcon
    obtain ⟨φ, hφ, hφb⟩ := extraction_of_frequently_atTop hcon
    -- The demands along `φ` lie in a compact box.
    have hbox : ∀ n, d a (pn (φ n)) ∈ Icc (0 : ι → ℝ) (fun _ => M') := fun n =>
      ⟨(hdmem (φ n) a).1.1, fun k => hφb n k⟩
    obtain ⟨xbar, -, ψ, hψ, hxlim⟩ := isCompact_Icc.tendsto_subseq hbox
    set x : ℕ → ι → ℝ := fun n => d a (pn (φ (ψ n))) with hx
    set q : ℕ → ι → ℝ := fun n => pn (φ (ψ n)) with hq
    have hqlim : Tendsto q atTop (𝓝 pbar) := hlim.comp (hφ.comp hψ).tendsto_atTop
    have hxlim' : Tendsto x atTop (𝓝 xbar) := hxlim
    have hx0 : ∀ n, 0 ≤ x n := fun n => (hdmem _ a).1.1
    have hxbar0 : 0 ≤ xbar := fun k =>
      ge_of_tendsto' (((continuous_apply k).tendsto xbar).comp hxlim') fun n => hx0 n k
    -- Costs converge.
    have hcostq : ∀ y, Tendsto (fun n => cost (q n) y) atTop (𝓝 (cost pbar y)) := fun y => by
      have : Continuous fun p : ι → ℝ => cost p y := by unfold cost; fun_prop
      exact (this.tendsto pbar).comp hqlim
    have hcostx : Tendsto (fun n => cost (q n) (x n)) atTop (𝓝 (cost pbar xbar)) := by
      have : Continuous fun pq : (ι → ℝ) × (ι → ℝ) => cost pq.1 pq.2 := by unfold cost; fun_prop
      exact (this.tendsto (pbar, xbar)).comp (hqlim.prodMk_nhds hxlim')
    -- `x̄` is affordable at `p̄`.
    have hxbar_aff : cost pbar xbar ≤ cost pbar (E.endow a) :=
      le_of_tendsto_of_tendsto' hcostx (hcostq _) fun n => (hdmem _ a).1.2
    -- A strictly better, strictly cheaper bundle at `p̄`.
    set e : ι → ℝ := Pi.single l 1 with he
    have he0 : 0 ≤ e := fun k => by
      by_cases hk : k = l
      · subst hk; simp [he]
      · simp [he, hk]
    have hcost_e : cost pbar e = 0 := by
      simp [he, cost, Pi.single_apply, hl]
    have hbetter : u a xbar < u a (xbar + e) := by
      have h := hmono a xbar (xbar + e) hxbar0 (le_add_of_nonneg_right he0) (by
        intro h
        have := congrFun h l
        simp [he] at this)
      rw [hpref a] at h
      exact lt_of_not_ge h.2
    -- For `t < 1` close to `1`, `t x̄ + e` is still strictly better.
    have hcontt : ContinuousAt (fun t : ℝ => u a (t • xbar + e)) 1 :=
      ((hu a).comp ((continuous_id.smul continuous_const).add continuous_const)).continuousAt
    have hev : ∀ᶠ t in 𝓝 (1 : ℝ), u a xbar < u a (t • xbar + e) := by
      have := hcontt.eventually (lt_mem_nhds (by simpa using hbetter))
      exact this
    obtain ⟨t, ht, ht1, ht0⟩ : ∃ t : ℝ, u a xbar < u a (t • xbar + e) ∧ t < 1 ∧ 0 ≤ t := by
      obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 hev
      have hm0 : 0 < min δ 1 := lt_min hδ one_pos
      have hm1 : min δ 1 ≤ 1 := min_le_right _ _
      have hmδ : min δ 1 ≤ δ := min_le_left _ _
      refine ⟨1 - min δ 1 / 2, hP ?_, by linarith, by linarith⟩
      rw [Real.dist_eq, show 1 - min δ 1 / 2 - 1 = -(min δ 1 / 2) by ring, abs_neg,
        abs_of_pos (by linarith)]
      linarith
    set y : ι → ℝ := t • xbar + e with hy
    have hy0 : 0 ≤ y := fun k => add_nonneg (mul_nonneg ht0 (hxbar0 k)) (he0 k)
    have hcosty : cost pbar y < cost pbar (E.endow a) := by
      rw [hy, cost_add_right, cost_smul_right, hcost_e, add_zero]
      calc t * cost pbar xbar ≤ t * cost pbar (E.endow a) :=
            mul_le_mul_of_nonneg_left hxbar_aff ht0
        _ < cost pbar (E.endow a) := by nlinarith
    -- So `y` is affordable at `q n` for large `n`, hence `u x_n ≥ u y`.
    have hev_aff : ∀ᶠ n in atTop, cost (q n) y < cost (q n) (E.endow a) :=
      ((hcostq y).sub (hcostq (E.endow a))).eventually
        (gt_mem_nhds (show cost pbar y - cost pbar (E.endow a) < 0 by linarith)) |>.mono
        fun n hn => by linarith
    have hev_le : ∀ᶠ n in atTop, u a y ≤ u a (x n) := hev_aff.mono fun n hn => by
      have h := (hdmem (φ (ψ n)) a).2 y ⟨hy0, hn.le⟩
      rw [hpref a] at h
      exact h
    have hlimu : Tendsto (fun n => u a (x n)) atTop (𝓝 (u a xbar)) :=
      ((hu a).tendsto xbar).comp hxlim'
    have : u a y ≤ u a xbar := ge_of_tendsto hlimu hev_le
    linarith
  -- Aggregate excess demand inherits the blow-up.
  have htotal_nonneg : ∀ k, 0 ≤ E.totalEndowment k := fun k => (hω k).le
  filter_upwards [hkey (M + ∑ k, E.totalEndowment k)] with n ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hsingle : d a (pn n) k ≤ ∑ b, d b (pn n) k :=
    Finset.single_le_sum (f := fun b => d b (pn n) k) (fun b _ => (hdmem n b).1.1 k)
      (Finset.mem_univ a)
  have hωk : E.totalEndowment k ≤ ∑ j, E.totalEndowment j :=
    Finset.single_le_sum (f := fun j => E.totalEndowment j) (fun j _ => htotal_nonneg j)
      (Finset.mem_univ k)
  simp only [excessDemand, Pi.sub_apply, Finset.sum_apply]
  linarith

omit [Fintype α] in
/-- Wealth is strictly positive at strictly positive prices when the endowment
is nonnegative and nonzero. -/
theorem wealth_pos (E : ExchangeEconomy α ι) {a : α} (hωa : E.endow a ≠ 0) {p : ι → ℝ}
    (hp : PositivePrices p) : 0 < E.wealth p a := by
  obtain ⟨i, hi⟩ : ∃ i, E.endow a i ≠ 0 := by
    by_contra h; push Not at h; exact hωa (funext h)
  have hpos : 0 < E.endow a i := lt_of_le_of_ne (E.endow_nonneg a i) (Ne.symm hi)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hp j).le (E.endow_nonneg a j))
    ⟨i, Finset.mem_univ i, mul_pos (hp i) hpos⟩

/-- **Existence of Walrasian equilibrium from preferences** (MWG Prop. 17.C.1
with the hypotheses of Prop. 17.B.2). In an exchange economy where every
consumer has a continuous, strictly quasiconcave utility representing strongly
monotone preferences and a nonzero endowment, and the aggregate endowment is
strictly positive, there is a Walrasian equilibrium with strictly positive
prices.

Deviation: each endowment is assumed nonzero (`hωa`), i.e. every consumer has
positive wealth at `p ≫ 0`, as MWG assumes in the text of 17.B.2. It is not
mathematically necessary (a zero-wealth consumer demands `{0}`). -/
theorem exists_walrasianEquilibrium_of_preferences [Nonempty ι] (E : ExchangeEconomy α ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hsq : ∀ a, StrictlyQuasiconcave (u a)) (hmono : ∀ a, StronglyMonotone (E.pref a))
    (hω : PositivePrices E.totalEndowment) (hωa : ∀ a, E.endow a ≠ 0) :
    ∃ p x, PositivePrices p ∧ E.IsWalrasianEquilibrium p x := by
  classical
  choose xd hxc hxs using fun a => exists_continuous_demand_function (hu a) (hsq a)
  -- The demand selection: the unique demanded bundle at `p ≫ 0`.
  let pw : α → ∀ p : ι → ℝ, PositivePrices p → PriceWealth ι := fun a p hp =>
    ⟨(p, cost p (E.endow a)), hp, E.wealth_pos (hωa a) hp⟩
  let d : α → (ι → ℝ) → (ι → ℝ) := fun a p =>
    if hp : PositivePrices p then xd a (pw a p hp) else 0
  have hd : E.IsDemandSelection d {p | PositivePrices p} := by
    intro p hp a
    have hmem : xd a (pw a p hp) ∈ demand (prefOf (u a)) p (cost p (E.endow a)) := by
      have := hxs a (pw a p hp)
      rw [this]; exact Set.mem_singleton _
    have hda : d a p = xd a (pw a p hp) := dite_eq_left_of_eq_true (eq_true hp)
    rw [hda, hpref a]
    exact hmem
  -- Continuity of each consumer's demand on `p ≫ 0`.
  have hdc : ∀ a, ContinuousOn (d a) {p | PositivePrices p} := by
    intro a
    rw [continuousOn_iff_continuous_domRestrict]
    have hG : Continuous fun q : {p : ι → ℝ // PositivePrices p} => pw a q.1 q.2 := by
      refine Continuous.subtype_mk ?_ _
      have : Continuous fun p : ι → ℝ => cost p (E.endow a) := by unfold cost; fun_prop
      exact continuous_subtype_val.prodMk (this.comp continuous_subtype_val)
    have : Set.domRestrict {p | PositivePrices p} (d a) = fun q => xd a (pw a q.1 q.2) := by
      funext q
      simp only [Set.domRestrict_apply, d]
      exact dite_eq_left_of_eq_true (eq_true q.2)
    rw [this]
    exact (hxc a).comp hG
  have hzc : ContinuousOn (E.excessDemand d) {p | PositivePrices p} := by
    have : E.excessDemand d = (fun p => ∑ a, d a p) - fun _ => E.totalEndowment := by
      funext p; rfl
    rw [this]
    exact (continuousOn_finsetSum _ fun a _ => hdc a).sub continuousOn_const
  -- Bounded below by `−ω̄`.
  have hb : ExcessBoundedBelow (E.excessDemand d) := by
    refine ⟨∑ k, E.totalEndowment k + 1, fun p hp k => ?_⟩
    have hd0 : 0 ≤ ∑ a, d a p k :=
      Finset.sum_nonneg fun a _ => (hd p hp a).1.1 k
    have hωk : E.totalEndowment k ≤ ∑ j, E.totalEndowment j :=
      Finset.single_le_sum (f := fun j => E.totalEndowment j) (fun j _ => (hω j).le)
        (Finset.mem_univ k)
    simp only [excessDemand, Pi.sub_apply, Finset.sum_apply]
    linarith
  have hlns : ∀ a, LocallyNonsatiated (E.pref a) := fun a => (hmono a).locallyNonsatiated
  obtain ⟨p, hp, heq⟩ := E.exists_walrasianEquilibrium_of_boundaryCondition hlns hd hzc hb
    (E.boundaryCondition_excessDemand hpref hu hmono hω hd)
  exact ⟨p, _, hp, heq⟩

end ExchangeEconomy

/-! ### Non-vacuity: a square-root economy

`u(x) = √x₀ + √x₁` is continuous, strictly quasiconcave and strongly monotone
on the orthant, but demand does not exist when a price is zero, so only the
boundary-condition theorem gives existence here. -/

namespace GEExamples

open Real

/-- Square-root utility. -/
noncomputable def uSqrt (x : Fin 2 → ℝ) : ℝ := √(x 0) + √(x 1)

theorem continuous_uSqrt : Continuous uSqrt := by
  unfold uSqrt; fun_prop

theorem strictlyQuasiconcave_uSqrt : StrictlyQuasiconcave uSqrt := by
  intro x y hx hy hne t ht0 ht1
  have hcc := strictConcaveOn_sqrt
  have hle : ∀ i, t * √(x i) + (1 - t) * √(y i) ≤ √(t * x i + (1 - t) * y i) := fun i => by
    have := hcc.concaveOn.2 (Set.mem_Ici.2 (hx i)) (Set.mem_Ici.2 (hy i)) ht0.le
      (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    simpa [smul_eq_mul] using this
  have hlt : ∀ i, x i ≠ y i → t * √(x i) + (1 - t) * √(y i) < √(t * x i + (1 - t) * y i) :=
    fun i hi => by
      have := hcc.2 (Set.mem_Ici.2 (hx i)) (Set.mem_Ici.2 (hy i)) hi ht0
        (by linarith : (0 : ℝ) < 1 - t) (by ring)
      simpa [smul_eq_mul] using this
  have hmin : min (uSqrt x) (uSqrt y) ≤ t * uSqrt x + (1 - t) * uSqrt y := by
    rcases le_total (uSqrt x) (uSqrt y) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hstrict : t * uSqrt x + (1 - t) * uSqrt y < uSqrt (t • x + (1 - t) • y) := by
    simp only [uSqrt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h0 : x 0 = y 0
    · have h1 : x 1 ≠ y 1 := by
        intro h1; apply hne; funext i; fin_cases i
        · exact h0
        · exact h1
      linarith [hle 0, hlt 1 h1]
    · linarith [hlt 0 h0, hle 1]
  exact lt_of_le_of_lt hmin hstrict

theorem stronglyMonotone_uSqrt : StronglyMonotone (prefOf uSqrt) := by
  intro x y hx hxy hne
  have hlt : uSqrt x < uSqrt y := by
    have hle : ∀ i, √(x i) ≤ √(y i) := fun i => Real.sqrt_le_sqrt (hxy i)
    simp only [uSqrt]
    by_cases h0 : x 0 = y 0
    · have h1 : x 1 < y 1 := lt_of_le_of_ne (hxy 1) fun h1 => hne (by
        funext i; fin_cases i
        · exact h0
        · exact h1)
      linarith [hle 0, Real.sqrt_lt_sqrt (hx 1) h1]
    · linarith [Real.sqrt_lt_sqrt (hx 0) (lt_of_le_of_ne (hxy 0) h0), hle 1]
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- Two square-root consumers with endowments `(1, 2)` and `(2, 1)`. -/
noncomputable def sqrtEconomy : ExchangeEconomy (Fin 2) (Fin 2) where
  pref _ := prefOf uSqrt
  endow := endow₂
  endow_nonneg := endow₂_nonneg

/-- **Existence for the square-root economy**, from preferences alone. -/
theorem sqrtEconomy_exists_equilibrium :
    ∃ p x, PositivePrices p ∧ sqrtEconomy.IsWalrasianEquilibrium p x :=
  sqrtEconomy.exists_walrasianEquilibrium_of_preferences (u := fun _ => uSqrt)
    (fun _ => rfl) (fun _ => continuous_uSqrt) (fun _ => strictlyQuasiconcave_uSqrt)
    (fun _ => stronglyMonotone_uSqrt)
    (fun i => by
      simp only [ExchangeEconomy.totalEndowment, sqrtEconomy, Finset.sum_apply]
      exact Finset.sum_pos (fun a _ => endow₂_pos a i) Finset.univ_nonempty)
    (fun a h => by
      have := congrFun h 0
      simp only [sqrtEconomy, Pi.zero_apply] at this
      exact (endow₂_pos a 0).ne' this)

end GEExamples

end Econ
