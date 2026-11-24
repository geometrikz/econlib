/-
# Existence of Walrasian equilibrium: zero endowments and Cobb–Douglas-type preferences

PLAN.md §1 (M4). MWG Prop. 17.B.2, 17.C.1; Debreu (1959) §5.

`GE/ExistencePreferences.lean` proves existence for consumers with continuous,
strictly quasiconcave, strongly monotone utility and **nonzero** endowments.
Two standard cases fall outside it:

* **Consumers with zero endowment.** They have zero wealth at every price and
  demand `{0}` at `p ≫ 0`. The earlier theorem required `ωₐ ≠ 0`; MWG
  17.B.2 itself only asks for `ω̄ ≫ 0`, which is what we assume here.
* **Cobb–Douglas-type preferences**, e.g. `u(x) = x₀ x₁`. These are not
  strongly monotone and not strictly quasiconcave on the whole orthant: every
  boundary bundle has utility `0`. They are, however, strictly monotone and
  strictly quasiconcave on the interior, and every interior bundle beats every
  boundary bundle (the standard Cobb–Douglas case; only `x₀ x₁` is formalized).

Both are handled by one theorem whose per-consumer hypothesis
`RegularUtility u` collects exactly what the proof uses: continuity, unique
demand at positive prices and wealth, local nonsatiation, and an *improvement
property* (a bundle affordable at a boundary price can be strictly improved
while staying strictly cheaper). Under continuity the improvement property says
exactly that demand is empty at boundary prices with positive wealth;
`RegularUtility.demand_eq_empty_of_boundary` proves the direction used. We show that both classical hypothesis sets
imply it (`regularUtility_of_strictlyQuasiconcave`,
`regularUtility_of_interiorRegular`), then prove existence with no assumption
on individual endowments (`exists_walrasianEquilibrium_of_regular`). The
witness `cdEconomy` has a Cobb–Douglas consumer who must trade
(`cdEconomy_trade`) and a consumer with zero endowment.

Caveat: utilities must be continuous on all of `ℝ^ι`; a utility defined only on
the orthant (e.g. `Σ log xᵢ`) has to be composed with the positive part first.
-/
module

public import EconLean.GE.ExistencePreferences

@[expose] public section

namespace Econ

open Filter Topology Set

variable {ι : Type*} [Fintype ι]

/-! ### Regular utilities -/

/-- What the existence proof needs from each consumer's utility. -/
structure RegularUtility (u : (ι → ℝ) → ℝ) : Prop where
  /-- Continuity. -/
  cont : Continuous u
  /-- Demand has at most one element at positive prices and wealth. -/
  unique : ∀ p w, PositivePrices p → 0 < w → (demand (prefOf u) p w).Subsingleton
  /-- Local nonsatiation (gives Walras' law). -/
  lns : LocallyNonsatiated (prefOf u)
  /-- Improvement at boundary prices: if `x̄ ≥ 0` is affordable at `p̄ ≥ 0` with
  positive wealth `W` and some good is free, some `y ≥ 0` is strictly better and
  strictly cheaper. -/
  improve : ∀ (xbar pbar : ι → ℝ) (W : ℝ), 0 ≤ xbar → 0 ≤ pbar → (∃ l, pbar l = 0) →
    cost pbar xbar ≤ W → 0 < W → ∃ y, 0 ≤ y ∧ u xbar < u y ∧ cost pbar y < W

/-- **Cobb–Douglas-type regularity**, a sufficient condition in the spirit of
MWG's boundary discussion (not MWG's exact statement): continuous,
strictly increasing and strictly quasiconcave on the interior of the orthant,
and every interior bundle strictly better than every boundary bundle. -/
structure InteriorRegular (u : (ι → ℝ) → ℝ) : Prop where
  cont : Continuous u
  /-- Strictly increasing from interior bundles (`PositivePrices x` here just
  means the bundle `x` is strictly positive). -/
  mono : ∀ x y : ι → ℝ, PositivePrices x → x ≤ y → x ≠ y → u x < u y
  /-- Strictly quasiconcave on the interior. -/
  sqc : ∀ x y : ι → ℝ, PositivePrices x → PositivePrices y → x ≠ y → ∀ t : ℝ, 0 < t → t < 1 →
    min (u x) (u y) < u (t • x + (1 - t) • y)
  /-- Boundary bundles are worse than interior ones. -/
  boundary : ∀ x y : ι → ℝ, 0 ≤ x → (∃ i, x i = 0) → PositivePrices y → u x < u y

/-- The improvement property rules out demand at boundary prices: if some good
is free and wealth is positive, nothing is utility-maximizing. -/
theorem RegularUtility.demand_eq_empty_of_boundary {u : (ι → ℝ) → ℝ} (hu : RegularUtility u)
    {pbar : ι → ℝ} {W : ℝ} (hp : 0 ≤ pbar) (hl : ∃ l, pbar l = 0) (hW : 0 < W) :
    demand (prefOf u) pbar W = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, hy0, hlt, hcy⟩ := hu.improve x pbar W hx.1.1 hp hl hx.1.2 hW
  have := hx.2 y ⟨hy0, hcy.le⟩
  exact absurd this (not_le.mpr hlt)

omit [Fintype ι] in
/-- If `u x̄ < u (x̄ + e)` and `u` is continuous, then `u x̄ < u (t x̄ + e)` for
some `t ∈ [0, 1)`. -/
theorem exists_lt_one_better {u : (ι → ℝ) → ℝ} (hu : Continuous u) {xbar e : ι → ℝ}
    (h : u xbar < u (xbar + e)) : ∃ t : ℝ, u xbar < u (t • xbar + e) ∧ t < 1 ∧ 0 ≤ t := by
  have hcontt : ContinuousAt (fun t : ℝ => u (t • xbar + e)) 1 :=
    (hu.comp ((continuous_id.smul continuous_const).add continuous_const)).continuousAt
  have hev : ∀ᶠ t in 𝓝 (1 : ℝ), u xbar < u (t • xbar + e) :=
    hcontt.eventually (lt_mem_nhds (by simpa using h))
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 hev
  have hm0 : 0 < min δ 1 := lt_min hδ one_pos
  have hm1 : min δ 1 ≤ 1 := min_le_right _ _
  have hmδ : min δ 1 ≤ δ := min_le_left _ _
  refine ⟨1 - min δ 1 / 2, hP ?_, by linarith, by linarith⟩
  rw [Real.dist_eq, show 1 - min δ 1 / 2 - 1 = -(min δ 1 / 2) by ring, abs_neg,
    abs_of_pos (by linarith)]
  linarith

/-- Moving along a free good: `t x̄ + e_l` with `t < 1` is strictly cheaper. -/
theorem cost_smul_add_single_lt [DecidableEq ι] {xbar pbar : ι → ℝ} {W t : ℝ} {l : ι}
    (hxbar : 0 ≤ xbar) (hpbar : 0 ≤ pbar) (hl : pbar l = 0) (haff : cost pbar xbar ≤ W)
    (hW : 0 < W) (ht1 : t < 1) (ht0 : 0 ≤ t) :
    cost pbar (t • xbar + Pi.single l 1) < W := by
  have hcost_e : cost pbar (Pi.single l 1) = 0 := by
    simp [cost, Pi.single_apply, hl]
  rw [cost_add_right, cost_smul_right, hcost_e, add_zero]
  have h0 : 0 ≤ cost pbar xbar := Finset.sum_nonneg fun i _ => mul_nonneg (hpbar i) (hxbar i)
  nlinarith

omit [Fintype ι] in
theorem single_nonneg' [DecidableEq ι] (l : ι) : (0 : ι → ℝ) ≤ Pi.single l 1 := fun k => by
  by_cases hk : k = l
  · subst hk; simp
  · simp [hk]

/-- **Classical case.** Continuous, strictly quasiconcave, strongly monotone
utilities are regular. -/
theorem regularUtility_of_strictlyQuasiconcave [Nonempty ι] {u : (ι → ℝ) → ℝ} (hu : Continuous u)
    (hsq : StrictlyQuasiconcave u) (hmono : StronglyMonotone (prefOf u)) : RegularUtility u := by
  classical
  refine ⟨hu, fun p w _ _ => demand_subsingleton hsq p w, hmono.locallyNonsatiated, ?_⟩
  intro xbar pbar W hxbar hpbar ⟨l, hl⟩ haff hW
  have hbetter : u xbar < u (xbar + Pi.single l 1) := by
    have h := hmono xbar (xbar + Pi.single l 1) hxbar
      (le_add_of_nonneg_right (single_nonneg' l)) (by
        intro h; have := congrFun h l; simp at this)
    exact lt_of_not_ge h.2
  obtain ⟨t, ht, ht1, ht0⟩ := exists_lt_one_better hu hbetter
  exact ⟨t • xbar + Pi.single l 1, fun k => add_nonneg (mul_nonneg ht0 (hxbar k))
    (single_nonneg' l k), ht, cost_smul_add_single_lt hxbar hpbar hl haff hW ht1 ht0⟩

omit [Fintype ι] in
theorem positive_add_const {x : ι → ℝ} (hx : 0 ≤ x) {δ : ℝ} (hδ : 0 < δ) :
    PositivePrices (x + fun _ => δ) := fun i => by
  have : 0 ≤ x i := hx i
  simp only [Pi.add_apply]; linarith

/-- Interior-regular utilities are locally nonsatiated. -/
theorem InteriorRegular.locallyNonsatiated [Nonempty ι] {u : (ι → ℝ) → ℝ}
    (h : InteriorRegular u) : LocallyNonsatiated (prefOf u) := by
  intro x hx ε hε
  set y : ι → ℝ := x + fun _ => ε / 2
  have hy : PositivePrices y := positive_add_const hx (by positivity)
  have hdist : dist y x < ε := by
    rw [dist_eq_norm, show y - x = fun _ => ε / 2 by funext i; simp [y]]
    rw [pi_norm_const, Real.norm_of_nonneg (by positivity)]
    linarith
  have hlt : u x < u y := by
    by_cases hb : ∃ i, x i = 0
    · exact h.boundary x y hx hb hy
    · push Not at hb
      have hxpos : PositivePrices x := fun i => lt_of_le_of_ne (hx i) (Ne.symm (hb i))
      refine h.mono x y hxpos (fun i => by simp only [y, Pi.add_apply]; linarith) ?_
      intro hxy
      obtain ⟨i⟩ := ‹Nonempty ι›
      have := congrFun hxy i
      simp only [y, Pi.add_apply] at this
      linarith
  exact ⟨y, fun i => (hy i).le, hdist, hlt.le, not_le.2 hlt⟩

/-- **Cobb–Douglas-type case.** Interior-regular utilities are regular. -/
theorem regularUtility_of_interiorRegular [Nonempty ι] {u : (ι → ℝ) → ℝ}
    (h : InteriorRegular u) : RegularUtility u := by
  classical
  -- A cheap interior bundle: `δ 𝟙` with `δ = w / (2 ∑ p + 1)`.
  have hcheap : ∀ (p : ι → ℝ) (w : ℝ), 0 ≤ p → 0 < w →
      PositivePrices (fun _ : ι => w / (2 * ∑ i, p i + 1)) ∧
        cost p (fun _ : ι => w / (2 * ∑ i, p i + 1)) < w := by
    intro p w hp hw
    have hs : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp i
    refine ⟨fun _ => by positivity, ?_⟩
    have : cost p (fun _ : ι => w / (2 * ∑ i, p i + 1))
        = (∑ i, p i) * (w / (2 * ∑ i, p i + 1)) := by
      simp only [cost, Finset.sum_mul]
    rw [this, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨h.cont, ?_, h.locallyNonsatiated, ?_⟩
  · -- Demanded bundles are interior, then strict quasiconcavity on the interior.
    intro p w hp hw
    have hint : ∀ x ∈ demand (prefOf u) p w, PositivePrices x := by
      intro x hx
      by_contra hnot
      have hb : ∃ i, x i = 0 := by
        by_contra hb; push Not at hb
        exact hnot fun i => lt_of_le_of_ne (hx.1.1 i) (Ne.symm (hb i))
      obtain ⟨hyp, hyc⟩ := hcheap p w (fun i => (hp i).le) hw
      have h1 := h.boundary x _ hx.1.1 hb hyp
      have h2 : u (fun _ : ι => w / (2 * ∑ i, p i + 1)) ≤ u x :=
        hx.2 _ ⟨fun i => (hyp i).le, hyc.le⟩
      linarith
    intro x hx y hy
    by_contra hne
    have hmid : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y ∈ budgetSet p w :=
      convex_budgetSet p w hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
    have hlt := h.sqc x y (hint x hx) (hint y hy) hne (1 / 2) (by norm_num) (by norm_num)
    have h1 : u ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) ≤ u x := hx.2 _ hmid
    have h2 : u ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) ≤ u y := hy.2 _ hmid
    exact lt_irrefl _ (lt_of_lt_of_le hlt (le_min h1 h2))
  · intro xbar pbar W hxbar hpbar ⟨l, hl⟩ haff hW
    by_cases hb : ∃ i, xbar i = 0
    · obtain ⟨hyp, hyc⟩ := hcheap pbar W hpbar hW
      exact ⟨_, fun i => (hyp i).le, h.boundary xbar _ hxbar hb hyp, hyc⟩
    · push Not at hb
      have hxpos : PositivePrices xbar := fun i => lt_of_le_of_ne (hxbar i) (Ne.symm (hb i))
      have hbetter : u xbar < u (xbar + Pi.single l 1) :=
        h.mono _ _ hxpos (le_add_of_nonneg_right (single_nonneg' l)) (by
          intro h; have := congrFun h l; simp at this)
      obtain ⟨t, ht, ht1, ht0⟩ := exists_lt_one_better h.cont hbetter
      exact ⟨t • xbar + Pi.single l 1, fun k => add_nonneg (mul_nonneg ht0 (hxbar k))
        (single_nonneg' l k), ht, cost_smul_add_single_lt hxbar hpbar hl haff hW ht1 ht0⟩

/-- A regular utility has a continuous demand function at positive prices and
wealth. -/
theorem RegularUtility.exists_continuous_demand_function {u : (ι → ℝ) → ℝ}
    (h : RegularUtility u) :
    ∃ x : PriceWealth ι → (ι → ℝ), Continuous x ∧
      ∀ pw, demand (prefOf u) pw.1.1 pw.1.2 = {x pw} := by
  have hne : ∀ pw : PriceWealth ι, (demand (prefOf u) pw.1.1 pw.1.2).Nonempty :=
    fun pw => demand_nonempty h.cont pw.2.1 pw.2.2.le
  choose x hx using hne
  have hsing : ∀ pw, demand (prefOf u) pw.1.1 pw.1.2 = {x pw} := fun pw =>
    (h.unique _ _ pw.2.1 pw.2.2 |>.eq_singleton_of_mem (hx pw))
  exact ⟨x, continuous_demand_function h.cont hsing, hsing⟩

namespace ExchangeEconomy

variable {α : Type*} [Fintype α]

/-- With zero endowment, demand at `p ≫ 0` is `{0}`. -/
theorem demand_zero_wealth {R : (ι → ℝ) → (ι → ℝ) → Prop} (hrefl : R 0 0) {p : ι → ℝ}
    (hp : PositivePrices p) : (0 : ι → ℝ) ∈ demand R p (cost p 0) := by
  have hb : ∀ y ∈ budgetSet p (cost p 0), y = 0 := by
    intro y hy
    have hc : cost p y ≤ 0 := by simpa [cost] using hy.2
    funext i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ p j * y j := fun j _ => mul_nonneg (hp j).le (hy.1 j)
    have h0 : ∑ j, p j * y j = 0 := le_antisymm hc (Finset.sum_nonneg hnn)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hp i).ne'
    · simpa using h
  refine ⟨⟨le_rfl, le_rfl⟩, fun y hy => ?_⟩
  rw [hb y hy]; exact hrefl

/-- **The boundary condition from regular utilities.** -/
theorem boundaryCondition_excessDemand_of_regular (E : ExchangeEconomy α ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a)) (hreg : ∀ a, RegularUtility (u a))
    (hω : PositivePrices E.totalEndowment)
    {d : α → (ι → ℝ) → (ι → ℝ)} (hd : E.IsDemandSelection d {p | PositivePrices p}) :
    BoundaryCondition (E.excessDemand d) := by
  classical
  intro pn pbar hpos hlim hne ⟨l, hl⟩ M
  have hcoord : ∀ i, Tendsto (fun n => pn n i) atTop (𝓝 (pbar i)) := fun i =>
    ((continuous_apply i).tendsto pbar).comp hlim
  have hpbar0 : 0 ≤ pbar := fun i => ge_of_tendsto' (hcoord i) fun n => (hpos n i).le
  have hdmem : ∀ n a, d a (pn n) ∈ demand (E.pref a) (pn n) (E.wealth (pn n) a) :=
    fun n a => hd (pn n) (hpos n) a
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
  have hkey : ∀ M' : ℝ, ∀ᶠ n in atTop, ∃ k, M' < d a (pn n) k := by
    intro M'
    by_contra hcon
    rw [not_eventually] at hcon
    simp only [not_exists, not_lt] at hcon
    obtain ⟨φ, hφ, hφb⟩ := extraction_of_frequently_atTop hcon
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
    have hcostq : ∀ y, Tendsto (fun n => cost (q n) y) atTop (𝓝 (cost pbar y)) := fun y => by
      have : Continuous fun p : ι → ℝ => cost p y := by unfold cost; fun_prop
      exact (this.tendsto pbar).comp hqlim
    have hcostx : Tendsto (fun n => cost (q n) (x n)) atTop (𝓝 (cost pbar xbar)) := by
      have : Continuous fun pq : (ι → ℝ) × (ι → ℝ) => cost pq.1 pq.2 := by unfold cost; fun_prop
      exact (this.tendsto (pbar, xbar)).comp (hqlim.prodMk_nhds hxlim')
    have hxbar_aff : cost pbar xbar ≤ cost pbar (E.endow a) :=
      le_of_tendsto_of_tendsto' hcostx (hcostq _) fun n => (hdmem _ a).1.2
    obtain ⟨y, hy0, hybetter, hcosty⟩ :=
      (hreg a).improve xbar pbar _ hxbar0 hpbar0 ⟨l, hl⟩ hxbar_aff ha
    have hev_aff : ∀ᶠ n in atTop, cost (q n) y < cost (q n) (E.endow a) :=
      ((hcostq y).sub (hcostq (E.endow a))).eventually
        (gt_mem_nhds (show cost pbar y - cost pbar (E.endow a) < 0 by linarith)) |>.mono
        fun n hn => by linarith
    have hev_le : ∀ᶠ n in atTop, u a y ≤ u a (x n) := hev_aff.mono fun n hn => by
      have h := (hdmem (φ (ψ n)) a).2 y ⟨hy0, hn.le⟩
      rw [hpref a] at h
      exact h
    have hlimu : Tendsto (fun n => u a (x n)) atTop (𝓝 (u a xbar)) :=
      ((hreg a).cont.tendsto xbar).comp hxlim'
    have : u a y ≤ u a xbar := ge_of_tendsto hlimu hev_le
    linarith
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

/-- **Existence of Walrasian equilibrium for regular consumers** (MWG 17.C.1
with the hypotheses of 17.B.2), with **no assumption on individual
endowments**: some consumers may own nothing. Each consumer has a regular
utility (`RegularUtility`, implied by the classical hypotheses and by
Cobb–Douglas-type interior regularity) and the aggregate endowment is strictly
positive. -/
theorem exists_walrasianEquilibrium_of_regular [Nonempty ι] (E : ExchangeEconomy α ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, RegularUtility (u a)) (hω : PositivePrices E.totalEndowment) :
    ∃ p x, PositivePrices p ∧ E.IsWalrasianEquilibrium p x := by
  classical
  choose xd hxc hxs using fun a => (hreg a).exists_continuous_demand_function
  -- Consumers with zero endowment demand `0`; the others their unique bundle.
  let pw : ∀ a : α, ∀ p : ι → ℝ, PositivePrices p → E.endow a ≠ 0 → PriceWealth ι :=
    fun a p hp ha => ⟨(p, cost p (E.endow a)), hp, E.wealth_pos ha hp⟩
  let d : α → (ι → ℝ) → (ι → ℝ) := fun a p =>
    if ha : E.endow a = 0 then 0 else if hp : PositivePrices p then xd a (pw a p hp ha) else 0
  have hd : E.IsDemandSelection d {p | PositivePrices p} := by
    intro p hp a
    by_cases ha : E.endow a = 0
    · have hda : d a p = 0 := dite_eq_left_of_eq_true (eq_true ha)
      rw [hda, hpref a, wealth, ha]
      exact demand_zero_wealth (le_refl (u a 0)) hp
    · have hmem : xd a (pw a p hp ha) ∈ demand (prefOf (u a)) p (cost p (E.endow a)) := by
        have := hxs a (pw a p hp ha)
        rw [this]; exact Set.mem_singleton _
      have hda : d a p = xd a (pw a p hp ha) := by
        simp only [d, ha, ↓reduceDIte]
        exact dite_eq_left_of_eq_true (eq_true hp)
      rw [hda, hpref a]
      exact hmem
  have hdc : ∀ a, ContinuousOn (d a) {p | PositivePrices p} := by
    intro a
    by_cases ha : E.endow a = 0
    · have : d a = fun _ => 0 := funext fun p => dite_eq_left_of_eq_true (eq_true ha)
      rw [this]; exact continuousOn_const
    rw [continuousOn_iff_continuous_domRestrict]
    have hG : Continuous fun q : {p : ι → ℝ // PositivePrices p} => pw a q.1 q.2 ha := by
      refine Continuous.subtype_mk ?_ _
      have : Continuous fun p : ι → ℝ => cost p (E.endow a) := by unfold cost; fun_prop
      exact continuous_subtype_val.prodMk (this.comp continuous_subtype_val)
    have : Set.domRestrict {p | PositivePrices p} (d a) = fun q => xd a (pw a q.1 q.2 ha) := by
      funext q
      simp only [Set.domRestrict_apply, d, ha, ↓reduceDIte]
      exact dite_eq_left_of_eq_true (eq_true q.2)
    rw [this]
    exact (hxc a).comp hG
  have hzc : ContinuousOn (E.excessDemand d) {p | PositivePrices p} := by
    have : E.excessDemand d = (fun p => ∑ a, d a p) - fun _ => E.totalEndowment := by
      funext p; rfl
    rw [this]
    exact (continuousOn_finsetSum _ fun a _ => hdc a).sub continuousOn_const
  have hb : ExcessBoundedBelow (E.excessDemand d) := by
    refine ⟨∑ k, E.totalEndowment k + 1, fun p hp k => ?_⟩
    have hd0 : 0 ≤ ∑ a, d a p k :=
      Finset.sum_nonneg fun a _ => (hd p hp a).1.1 k
    have hωk : E.totalEndowment k ≤ ∑ j, E.totalEndowment j :=
      Finset.single_le_sum (f := fun j => E.totalEndowment j) (fun j _ => (hω j).le)
        (Finset.mem_univ k)
    simp only [excessDemand, Pi.sub_apply, Finset.sum_apply]
    linarith
  have hlns : ∀ a, LocallyNonsatiated (E.pref a) := fun a => by
    rw [hpref a]; exact (hreg a).lns
  obtain ⟨p, hp, heq⟩ := E.exists_walrasianEquilibrium_of_boundaryCondition hlns hd hzc hb
    (E.boundaryCondition_excessDemand_of_regular hpref hreg hω hd)
  exact ⟨p, _, hp, heq⟩

/-- **MWG 17.B.2/17.C.1 without the nonzero-endowment assumption.** Continuous,
strictly quasiconcave, strongly monotone utilities and `ω̄ ≫ 0` suffice. -/
theorem exists_walrasianEquilibrium_of_preferences_of_totalEndowment [Nonempty ι]
    (E : ExchangeEconomy α ι) {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hu : ∀ a, Continuous (u a)) (hsq : ∀ a, StrictlyQuasiconcave (u a))
    (hmono : ∀ a, StronglyMonotone (E.pref a)) (hω : PositivePrices E.totalEndowment) :
    ∃ p x, PositivePrices p ∧ E.IsWalrasianEquilibrium p x :=
  E.exists_walrasianEquilibrium_of_regular hpref
    (fun a => regularUtility_of_strictlyQuasiconcave (hu a) (hsq a) (by rw [← hpref a]; exact hmono a))
    hω

/-- **Existence with Cobb–Douglas-type consumers** (interior regularity), with
no assumption on individual endowments. -/
theorem exists_walrasianEquilibrium_of_interiorRegular [Nonempty ι] (E : ExchangeEconomy α ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, InteriorRegular (u a)) (hω : PositivePrices E.totalEndowment) :
    ∃ p x, PositivePrices p ∧ E.IsWalrasianEquilibrium p x :=
  E.exists_walrasianEquilibrium_of_regular hpref (fun a => regularUtility_of_interiorRegular (hreg a))
    hω

end ExchangeEconomy

/-! ### Witness: a Cobb–Douglas consumer and a consumer who owns nothing -/

namespace GEExamples

/-- The Cobb–Douglas utility `u(x) = x₀ x₁`. -/
def uCD (x : Fin 2 → ℝ) : ℝ := x 0 * x 1

theorem interiorRegular_uCD : InteriorRegular uCD := by
  refine ⟨by unfold uCD; fun_prop, ?_, ?_, ?_⟩
  · intro x y hx hy hne
    have h0 := hy 0
    have h0' := hx 0
    have h1' := hx 1
    have hy0 : x 0 ≤ y 0 := hy 0 |> fun _ => ‹x ≤ y› 0
    have hy1 : x 1 ≤ y 1 := ‹x ≤ y› 1
    have hlt : x 0 < y 0 ∨ x 1 < y 1 := by
      by_contra h; push Not at h
      exact hne (funext fun i => by fin_cases i <;> simp <;> linarith [h.1, h.2])
    unfold uCD
    rcases hlt with h | h <;> nlinarith
  · intro x y hx hy hne t ht0 ht1
    have hx0 := hx 0; have hx1 := hx 1; have hy0 := hy 0; have hy1 := hy 1
    unfold uCD
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set s := 1 - t with hs
    have hs0 : 0 < s := by linarith
    set A := x 0 * x 1
    set B := y 0 * y 1
    set C := x 0 * y 1 + y 0 * x 1
    have hA : 0 < A := mul_pos hx0 hx1
    have hB : 0 < B := mul_pos hy0 hy1
    have hC : 0 < C := by positivity
    have hCsq : C ^ 2 - 4 * A * B = (x 0 * y 1 - y 0 * x 1) ^ 2 := by
      simp only [A, B, C]; ring
    have hexp : (t * x 0 + s * y 0) * (t * x 1 + s * y 1) = t ^ 2 * A + s ^ 2 * B + t * s * C := by
      simp only [A, B, C]; ring
    rw [hexp]
    have hts : t + s = 1 := by rw [hs]; ring
    -- WLOG on which is smaller.
    have key : ∀ t s A B : ℝ, 0 < t → 0 < s → t + s = 1 → 0 < A → A ≤ B → 0 < C →
        C ^ 2 ≥ 4 * A * B → (B = A → C ^ 2 = 4 * A * B → False) →
        A < t ^ 2 * A + s ^ 2 * B + t * s * C := by
      intro t s A B ht0 hs0 hts A0 hAB hC hC2 heq
      have hA := A0
      have hC2A : 2 * A ≤ C := by nlinarith
      have hA1 : A = (t + s) ^ 2 * A := by rw [hts]; ring
      rcases hAB.lt_or_eq with hlt | heqAB
      · nlinarith [mul_pos hs0 hs0, mul_pos ht0 hs0]
      · have hCgt : 2 * A < C := by
          rcases hC2A.lt_or_eq with h | h
          · exact h
          · exact absurd (by rw [← h, ← heqAB]; ring) (heq heqAB.symm)
        nlinarith [mul_pos ht0 hs0]
    have hnotboth : B = A → C ^ 2 = 4 * A * B → False := by
      intro hBA hC2
      have hsq : (x 0 * y 1 - y 0 * x 1) ^ 2 = 0 := by linarith
      have hcross : x 0 * y 1 = y 0 * x 1 := by nlinarith [sq_nonneg (x 0 * y 1 - y 0 * x 1)]
      -- `x₀ y₁ = y₀ x₁` and `x₀ x₁ = y₀ y₁` force `x = y`.
      have h1 : x 1 ^ 2 = y 1 ^ 2 := by
        have : x 0 * (x 1 * y 1) = x 0 * (y 1 * y 1) := by
          have e1 : x 0 * x 1 = y 0 * y 1 := by simp only [A, B] at hBA; linarith
          nlinarith
        have := mul_left_cancel₀ hx0.ne' this
        nlinarith
      have hx1y1 : x 1 = y 1 := by nlinarith [sq_nonneg (x 1 - y 1), sq_nonneg (x 1 + y 1)]
      have hx0y0 : x 0 = y 0 := by
        rw [hx1y1] at hcross
        exact mul_right_cancel₀ hy1.ne' hcross
      exact hne (funext fun i => by fin_cases i <;> simp [hx0y0, hx1y1])
    have hC2 : C ^ 2 ≥ 4 * A * B := by nlinarith [sq_nonneg (x 0 * y 1 - y 0 * x 1)]
    rcases le_total A B with hAB | hBA
    · rw [min_eq_left hAB]
      exact key t s A B ht0 hs0 hts hA hAB hC hC2 hnotboth
    · rw [min_eq_right hBA]
      have := key s t B A hs0 ht0 (by linarith) hB hBA hC (by linarith)
        (fun h1 h2 => hnotboth h1.symm (by linarith))
      linarith
  · intro x y hx ⟨i, hi⟩ hy
    unfold uCD
    have : x 0 * x 1 = 0 := by fin_cases i <;> simp at hi <;> simp [hi]
    rw [this]
    exact mul_pos (hy 0) (hy 1)

/-- A three-consumer economy: consumer `0` has Cobb–Douglas utility and owns
`(1, 0)`; consumer `1` has square-root utility and owns **nothing**; consumer `2`
has square-root utility and owns `(0, 1)`. -/
noncomputable def cdEconomy : ExchangeEconomy (Fin 3) (Fin 2) where
  pref a := if a = 0 then prefOf uCD else prefOf uSqrt
  endow a := fun i => if a = 0 then (if i = 0 then 1 else 0)
    else if a = 2 then (if i = 1 then 1 else 0) else 0
  endow_nonneg a i := by
    simp only [Pi.zero_apply]
    split_ifs <;> norm_num

theorem cdEconomy_endow_one : cdEconomy.endow 1 = 0 := by
  ext i; simp [cdEconomy]

/-- **Existence for the Cobb–Douglas / zero-endowment economy.** The earlier
preference theorem does not apply: Cobb–Douglas is not strongly monotone, and
consumer `1` owns nothing. -/
theorem cdEconomy_exists_equilibrium :
    ∃ p x, PositivePrices p ∧ cdEconomy.IsWalrasianEquilibrium p x := by
  refine cdEconomy.exists_walrasianEquilibrium_of_regular
    (u := fun a => if a = 0 then uCD else uSqrt) (fun a => ?_) (fun a => ?_) ?_
  · by_cases h : a = 0 <;> simp [cdEconomy, h]
  · by_cases h : a = 0
    · simp only [h, ↓reduceIte]; exact regularUtility_of_interiorRegular interiorRegular_uCD
    · simp only [h, ↓reduceIte]
      exact regularUtility_of_strictlyQuasiconcave continuous_uSqrt strictlyQuasiconcave_uSqrt
        stronglyMonotone_uSqrt
  · intro i
    fin_cases i <;> simp [ExchangeEconomy.totalEndowment, cdEconomy, Fin.sum_univ_three]

/-- **The Cobb–Douglas consumer trades** in every equilibrium at positive prices:
its endowment `(1, 0)` is a boundary bundle with utility `0`, while the
affordable bundle `(1/2, p₀/(2p₁))` has positive utility. -/
theorem cdEconomy_trade {p : Fin 2 → ℝ} {x : Allocation (Fin 3) (Fin 2)}
    (hp : PositivePrices p) (h : cdEconomy.IsWalrasianEquilibrium p x) :
    x 0 ≠ cdEconomy.endow 0 := by
  intro hx
  have hd := h.1 0
  have hpref : cdEconomy.pref 0 = prefOf uCD := by simp [cdEconomy]
  rw [hpref, hx] at hd
  have h0 := hp 0
  have h1 := hp 1
  set y : Fin 2 → ℝ := ![1 / 2, p 0 / (2 * p 1)] with hy
  have hy0 : 0 ≤ y := by
    intro i; fin_cases i <;> simp [hy]; positivity
  have hcost : cost p y ≤ cdEconomy.wealth p 0 := by
    simp only [ExchangeEconomy.wealth, cost, Fin.sum_univ_two, hy, cdEconomy]
    simp
    field_simp
    linarith
  have := hd.2 y ⟨hy0, hcost⟩
  simp only [prefOf, uCD, hy, cdEconomy] at this
  simp at this
  have : 0 < p 0 / (2 * p 1) := by positivity
  nlinarith

end GEExamples

end Econ
