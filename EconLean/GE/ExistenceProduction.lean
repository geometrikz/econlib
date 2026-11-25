/-
# Existence of Walrasian equilibrium in a production economy

PLAN.md §1 (M4). MWG §17.B–17.C (production via the aggregate excess demand
of a private ownership economy);
Arrow & Debreu (1954); Debreu (1959) §5.

A private ownership economy (`GE/Production.lean`) with
* consumers with regular utilities (`RegularUtility`: e.g. continuous, strictly
  quasiconcave, strongly monotone, or Cobb–Douglas type), any nonnegative
  endowments (some consumers may own nothing but shares, or nothing at all; the theorem
  covers both, the witness below exercises the first),
  and a strictly positive aggregate endowment;
* firms with **compact** production sets containing `0` (inaction is possible),
  and a supply function `sⱼ` that is profit-maximizing and continuous on
  strictly positive prices

has a Walrasian equilibrium at strictly positive prices
(`exists_walrasianEquilibrium_production`).

Scope. Compactness of each `Yⱼ` stands in for Arrow–Debreu's closed, convex,
irreversible, free-disposal sets; it excludes free disposal and constant
returns, and the truncation to attainable production that the canonical proofs
use is not formalized. The closest textbook match is MWG §17.B with bounded,
strictly convex production sets. Set-valued supply (Kakutani) is not covered.
No assumption on individual endowments: a consumer whose wealth is `0` demands
`0`, and demand stays continuous as wealth falls to `0` (it is squeezed by
`xᵢ ≤ w / pᵢ`).

Continuity of supply holds when profit maximizers are unique (Berge,
`exists_continuous_supply`), giving `exists_walrasianEquilibrium_production_of_unique`;
the general theorem takes a continuous profit-maximizing selection, which also
covers the witness. The witness
`discEconomy` has one firm whose production set is a Euclidean disc through
`0`, with supply `c + ρ p / ‖p‖₂` (Cauchy–Schwarz); `discEconomy3` adds a consumer
who owns no goods but the whole firm (a pure shareholder).

Proof. Excess demand `z(p) = ∑ₐ xₐ(p, wₐ(p)) − ω̄ − ∑ⱼ sⱼ(p)` with
`wₐ(p) = p · ωₐ + ∑ⱼ θₐⱼ p · sⱼ(p)` is continuous on `p ≫ 0` and satisfies
Walras' law. It is bounded below because production sets are bounded. For
the boundary condition, profits are nonnegative (`0 ∈ Yⱼ`), so a consumer with
`p̄ · ωₐ > 0` keeps wealth bounded away from `0` and, by the improvement
property, demands unboundedly much near a boundary price
(`RegularUtility.demand_unbounded`). Then the interior existence theorem
applies.
-/
module

public import EconLean.GE.ExistenceRegular
public import EconLean.GE.Production

@[expose] public section

namespace Econ

open Filter Topology Set Finset

variable {ι : Type*} [Fintype ι]

/-- **Demand blows up near boundary prices.** If `qₙ → p̄` with some zero
price, wealth stays above some `c > 0`, and `xₙ` is demanded at `(qₙ, wₙ)`,
then `xₙ` eventually has arbitrarily large coordinates. -/
theorem RegularUtility.demand_unbounded {u : (ι → ℝ) → ℝ} (hreg : RegularUtility u)
    {qn : ℕ → ι → ℝ} {pbar : ι → ℝ} (hpos : ∀ n, PositivePrices (qn n))
    (hlim : Tendsto qn atTop (𝓝 pbar)) (hl : ∃ l, pbar l = 0) {wn : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hw : ∀ᶠ n in atTop, c ≤ wn n) {xn : ℕ → ι → ℝ}
    (hx : ∀ n, xn n ∈ demand (prefOf u) (qn n) (wn n)) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∃ k, M < xn n k := by
  intro M
  have hcoord : ∀ i, Tendsto (fun n => qn n i) atTop (𝓝 (pbar i)) := fun i =>
    ((continuous_apply i).tendsto pbar).comp hlim
  have hpbar0 : 0 ≤ pbar := fun i => ge_of_tendsto' (hcoord i) fun n => (hpos n i).le
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_exists, not_lt] at hcon
  obtain ⟨φ, hφ, hφb⟩ := extraction_of_frequently_atTop (hcon.and_eventually hw)
  have hbox : ∀ n, xn (φ n) ∈ Icc (0 : ι → ℝ) (fun _ => M) := fun n =>
    ⟨(hx (φ n)).1.1, fun k => (hφb n).1 k⟩
  obtain ⟨xbar, -, ψ, hψ, hxlim⟩ := isCompact_Icc.tendsto_subseq hbox
  set x : ℕ → ι → ℝ := fun n => xn (φ (ψ n)) with hxdef
  set q : ℕ → ι → ℝ := fun n => qn (φ (ψ n)) with hqdef
  set w : ℕ → ℝ := fun n => wn (φ (ψ n)) with hwdef
  have hqlim : Tendsto q atTop (𝓝 pbar) := hlim.comp (hφ.comp hψ).tendsto_atTop
  have hxlim' : Tendsto x atTop (𝓝 xbar) := hxlim
  have hx0 : ∀ n, 0 ≤ x n := fun n => (hx _).1.1
  have hxbar0 : 0 ≤ xbar := fun k =>
    ge_of_tendsto' (((continuous_apply k).tendsto xbar).comp hxlim') fun n => hx0 n k
  have hcostq : ∀ y, Tendsto (fun n => cost (q n) y) atTop (𝓝 (cost pbar y)) := fun y => by
    have : Continuous fun p : ι → ℝ => cost p y := by unfold cost; fun_prop
    exact (this.tendsto pbar).comp hqlim
  have hcostx : Tendsto (fun n => cost (q n) (x n)) atTop (𝓝 (cost pbar xbar)) := by
    have : Continuous fun pq : (ι → ℝ) × (ι → ℝ) => cost pq.1 pq.2 := by unfold cost; fun_prop
    exact (this.tendsto (pbar, xbar)).comp (hqlim.prodMk_nhds hxlim')
  -- Wealth dominates `W_n = max c (q_n · x_n) → W = max c (p̄ · x̄) > 0`.
  set W := max c (cost pbar xbar) with hW
  have hWpos : 0 < W := lt_of_lt_of_le hc (le_max_left _ _)
  have hWn : ∀ n, max c (cost (q n) (x n)) ≤ w n := fun n =>
    max_le (hφb (ψ n)).2 (hx _).1.2
  have hWlim : Tendsto (fun n => max c (cost (q n) (x n))) atTop (𝓝 W) :=
    tendsto_const_nhds.max hcostx
  obtain ⟨y, hy0, hybetter, hcosty⟩ :=
    hreg.improve xbar pbar W hxbar0 hpbar0 hl (le_max_right _ _) hWpos
  have hev_aff : ∀ᶠ n in atTop, cost (q n) y < max c (cost (q n) (x n)) :=
    ((hcostq y).sub hWlim).eventually
      (gt_mem_nhds (show cost pbar y - W < 0 by linarith)) |>.mono fun n hn => by linarith
  have hev_le : ∀ᶠ n in atTop, u y ≤ u (x n) := hev_aff.mono fun n hn =>
    (hx (φ (ψ n))).2 y ⟨hy0, (hn.trans_le (hWn n)).le⟩
  have hlimu : Tendsto (fun n => u (x n)) atTop (𝓝 (u xbar)) :=
    (hreg.cont.tendsto xbar).comp hxlim'
  have : u y ≤ u xbar := ge_of_tendsto hlimu hev_le
  linarith


omit [Fintype ι] in
/-- A compact set of bundles has uniformly bounded coordinates. -/
theorem exists_coord_bound {Y : Set (ι → ℝ)} [Finite ι] (hY : IsCompact Y) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ Y, ∀ l, |y l| ≤ R := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)).1 hY.isBounded
  refine ⟨max R 0, le_max_right _ _, fun y hy l => ?_⟩
  have h1 : ‖y‖ ≤ R := by simpa using hR hy
  have h2 := (norm_le_pi_norm y l).trans h1
  rw [Real.norm_eq_abs] at h2
  exact h2.trans (le_max_left _ _)

namespace ProductionEconomy

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Existence of Walrasian equilibrium with production** (MWG 17.B–17.C).
Consumers have regular utilities (no assumption on individual endowments), the aggregate
endowment is strictly positive; firms have compact production sets containing
`0` and a profit-maximizing supply function continuous on strictly positive
prices. Then a Walrasian equilibrium with strictly positive prices exists. -/
theorem exists_walrasianEquilibrium_production [Nonempty ι] (E : ProductionEconomy α β ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, RegularUtility (u a))
    (hω : PositivePrices E.totalEndowment) (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j)
    (hYc : ∀ j, IsCompact (E.prod j)) {s : β → (ι → ℝ) → (ι → ℝ)}
    (hs : ∀ j p, PositivePrices p → ProfitMax p (E.prod j) (s j p))
    (hsc : ∀ j, ContinuousOn (s j) {p | PositivePrices p}) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y := by
  classical
  choose D hDc hD using fun a => (hreg a).exists_continuous_demand_function
  set P := {p : ι → ℝ | PositivePrices p} with hP
  set wf : α → (ι → ℝ) → ℝ := fun a p => E.wealth p (fun j => s j p) a with hwf
  have hprofit : ∀ j p, PositivePrices p → 0 ≤ cost p (s j p) := fun j p hp => by
    have := (hs j p hp).2 0 (hY0 j)
    simpa [cost] using this
  have hwge : ∀ a p, PositivePrices p → cost p (E.endow a) ≤ wf a p := fun a p hp => by
    simp only [hwf, wealth, le_add_iff_nonneg_right]
    exact sum_nonneg fun j _ => mul_nonneg (E.share_nonneg a j) (hprofit j p hp)
  have hwnn : ∀ a p, PositivePrices p → 0 ≤ wf a p := fun a p hp =>
    (cost_nonneg (fun i => (hp i).le) (E.endow_nonneg a)).trans (hwge a p hp)
  set d : α → (ι → ℝ) → ι → ℝ := fun a p =>
    if h : PositivePrices p ∧ 0 < wf a p then D a ⟨(p, wf a p), h.1, h.2⟩ else 0 with hd
  have hdmem : ∀ a p, PositivePrices p → d a p ∈ demand (prefOf (u a)) p (wf a p) :=
    fun a p hp => by
      by_cases hw : 0 < wf a p
      · have := hD a ⟨(p, wf a p), hp, hw⟩
        simp only [hd, hp, hw, and_self, ↓reduceDIte]
        rw [show demand (prefOf (u a)) p (wf a p) = _ from this]
        rfl
      · have hw0 : wf a p = cost p 0 := by
          have := hwnn a p hp; simp [cost]; linarith
        simp only [hd, hw, and_false, ↓reduceDIte]
        rw [hw0]
        exact ExchangeEconomy.demand_zero_wealth (R := prefOf (u a)) le_rfl hp
  -- Continuity.
  have hcost : Continuous fun pq : (ι → ℝ) × (ι → ℝ) => cost pq.1 pq.2 := by
    unfold cost; fun_prop
  have hwc : ∀ a, ContinuousOn (wf a) P := fun a => by
    simp only [hwf, wealth]
    refine ContinuousOn.add (hcost.comp (continuous_id.prodMk continuous_const)).continuousOn ?_
    exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      (hcost.comp_continuousOn (continuousOn_id.prodMk (hsc j)))
  have hPopen : IsOpen P := isOpen_positivePrices
  have hdc : ∀ a, ContinuousOn (d a) P := fun a p hp => by
    refine ContinuousAt.continuousWithinAt ?_
    have hwca : ContinuousAt (wf a) p := (hwc a).continuousAt (hPopen.mem_nhds hp)
    by_cases hw : 0 < wf a p
    · -- On the open set where wealth is positive, `d a` is demand composed with a continuous map.
      set U := P ∩ wf a ⁻¹' Set.Ioi 0 with hU
      have hUo : IsOpen U := (hwc a).isOpen_inter_preimage hPopen isOpen_Ioi
      have hUc : ContinuousOn (d a) U := by
        rw [continuousOn_iff_continuous_domRestrict]
        have hw' : Continuous fun q : U => wf a q.1 :=
          (continuousOn_iff_continuous_domRestrict.1 ((hwc a).mono inter_subset_left))
        have hg : Continuous fun q : U =>
            (⟨(q.1, wf a q.1), q.2.1, q.2.2⟩ : PriceWealth ι) :=
          Continuous.subtype_mk (continuous_subtype_val.prodMk hw') _
        have : U.domRestrict (d a) = fun q : U => D a ⟨(q.1, wf a q.1), q.2.1, q.2.2⟩ := by
          funext q
          show d a q.1 = _
          simp only [hd]
          rw [dite_eq_left (show PositivePrices q.1 ∧ 0 < wf a q.1 from ⟨q.2.1, q.2.2⟩)]
        rw [this]
        exact (hDc a).comp hg
      exact hUc.continuousAt (hUo.mem_nhds ⟨hp, hw⟩)
    · -- Zero wealth: demand is squeezed to `0`.
      have hw0 : wf a p = 0 := le_antisymm (not_lt.1 hw) (hwnn a p hp)
      have hdp : d a p = 0 := by simp only [hd, hw, and_false, ↓reduceDIte]
      rw [ContinuousAt, hdp, tendsto_pi_nhds]
      intro i
      have hpi : ContinuousAt (fun q : ι → ℝ => q i) p := (continuous_apply i).continuousAt
      have hlim : Tendsto (fun q => wf a q / q i) (𝓝 p) (𝓝 (wf a p / p i)) :=
        hwca.div hpi (hp i).ne'
      rw [hw0, zero_div] at hlim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [hPopen.mem_nhds hp] with q hq
        exact (hdmem a q hq).1.1 i
      · filter_upwards [hPopen.mem_nhds hp] with q hq
        have hx := hdmem a q hq
        rw [le_div_iff₀ (hq i), mul_comm]
        refine le_trans ?_ hx.1.2
        exact single_le_sum (f := fun j => q j * d a q j)
          (fun j _ => mul_nonneg (hq j).le (hx.1.1 j)) (mem_univ i)
  set z : (ι → ℝ) → ι → ℝ := fun p => ∑ a, d a p - E.totalEndowment - ∑ j, s j p with hz
  have hzc : ContinuousOn z P :=
    ((continuousOn_finsetSum _ fun a _ => hdc a).sub continuousOn_const).sub
      (continuousOn_finsetSum _ fun j _ => hsc j)
  -- Walras' law.
  have hW : ∀ p, PositivePrices p → cost p (z p) = 0 := fun p hp => by
    have hsum := E.sum_wealth p fun j => s j p
    have hdw : ∀ a, cost p (d a p) = wf a p := fun a =>
      walras_law (hreg a).lns (hdmem a p hp)
    simp only [hz, cost_sub_right, cost_sum, hdw]
    simp only [hwf] at hsum ⊢
    rw [hsum, cost_add_right, cost_sum]
    ring
  -- Bounded below.
  choose R hR0 hR using fun j => exists_coord_bound (hYc j)
  have hdnn : ∀ a p, PositivePrices p → 0 ≤ d a p := fun a p hp => (hdmem a p hp).1.1
  have hsle : ∀ p, PositivePrices p → ∀ l, ∑ j, s j p l ≤ ∑ j, R j := fun p hp l =>
    sum_le_sum fun j _ => (le_abs_self _).trans (hR j _ (hs j p hp).1 l)
  have hωle : ∀ l, E.totalEndowment l ≤ ∑ k, E.totalEndowment k := fun l =>
    single_le_sum (f := fun k => E.totalEndowment k) (fun k _ => (hω k).le) (mem_univ l)
  have hzlow : ∀ p, PositivePrices p → ∀ l,
      ∑ a, d a p l - ∑ k, E.totalEndowment k - ∑ j, R j ≤ z p l := fun p hp l => by
    have h1 := hsle p hp l
    have h2 := hωle l
    simp only [hz, Pi.sub_apply, Finset.sum_apply]
    linarith
  have hb : ExcessBoundedBelow z := by
    refine ⟨∑ k, E.totalEndowment k + ∑ j, R j + 1, fun p hp l => ?_⟩
    have h0 : 0 ≤ ∑ a, d a p l := sum_nonneg fun a _ => hdnn a p hp l
    linarith [hzlow p hp l]
  -- Boundary condition.
  have hbd : BoundaryCondition z := by
    intro pn pbar hpos hlim hne hl M
    have hcoord : ∀ i, Tendsto (fun n => pn n i) atTop (𝓝 (pbar i)) := fun i =>
      ((continuous_apply i).tendsto pbar).comp hlim
    have hpbar0 : 0 ≤ pbar := fun i => ge_of_tendsto' (hcoord i) fun n => (hpos n i).le
    obtain ⟨a, ha⟩ : ∃ a, 0 < cost pbar (E.endow a) := by
      have htot : 0 < cost pbar E.totalEndowment := by
        obtain ⟨i, hi⟩ : ∃ i, pbar i ≠ 0 := by
          by_contra h; push Not at h; exact hne (funext h)
        have hpi : 0 < pbar i := lt_of_le_of_ne (hpbar0 i) (Ne.symm hi)
        exact sum_pos' (fun j _ => mul_nonneg (hpbar0 j) (hω j).le)
          ⟨i, mem_univ i, mul_pos hpi (hω i)⟩
      rw [ExchangeEconomy.totalEndowment, cost_sum] at htot
      by_contra h; push Not at h
      exact absurd htot (not_lt.2 (sum_nonpos fun a _ => h a))
    have hcω : Tendsto (fun n => cost (pn n) (E.endow a)) atTop (𝓝 (cost pbar (E.endow a))) :=
      (hcost.tendsto (pbar, E.endow a)).comp (hlim.prodMk_nhds tendsto_const_nhds)
    have hw : ∀ᶠ n in atTop, cost pbar (E.endow a) / 2 ≤ wf a (pn n) := by
      filter_upwards [hcω.eventually (lt_mem_nhds (half_lt_self ha))] with n hn
      exact hn.le.trans (hwge a _ (hpos n))
    have hkey := (hreg a).demand_unbounded hpos hlim hl (half_pos ha) hw
      (fun n => hdmem a (pn n) (hpos n)) (M + ∑ k, E.totalEndowment k + ∑ j, R j)
    filter_upwards [hkey] with n ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hsingle : d a (pn n) k ≤ ∑ b, d b (pn n) k :=
      single_le_sum (f := fun b => d b (pn n) k) (fun b _ => hdnn b _ (hpos n) k) (mem_univ a)
    linarith [hzlow (pn n) (hpos n) k]
  obtain ⟨p, hp, hz0⟩ := exists_equilibrium_of_boundaryCondition hzc hW hb hbd
  refine ⟨p, fun a => d a p, fun j => s j p, hp, fun j => hs j p hp, fun a => ?_, ?_⟩
  · rw [hpref a]; exact hdmem a p hp
  · have := hz0
    simp only [hz, sub_sub, sub_eq_zero] at this
    rw [this, add_comm]

/-- **Continuous supply from unique profit maximization** (Berge). If a firm's
production set is compact and nonempty and its profit maximizer is unique at
every `p ≫ 0`, there is a supply function, profit-maximizing and continuous on
`p ≫ 0`. -/
theorem exists_continuous_supply {Y : Set (ι → ℝ)} (hYc : IsCompact Y) (hYne : Y.Nonempty)
    (huniq : ∀ p, PositivePrices p → {y | ProfitMax p Y y}.Subsingleton) :
    ∃ s : (ι → ℝ) → (ι → ℝ), (∀ p, PositivePrices p → ProfitMax p Y (s p)) ∧
      ContinuousOn s {p | PositivePrices p} := by
  classical
  set X := {p : ι → ℝ // PositivePrices p}
  have hf : Continuous (Function.uncurry fun (p : X) (y : ι → ℝ) => cost p.1 y) := by
    have : Continuous fun pq : (ι → ℝ) × (ι → ℝ) => cost pq.1 pq.2 := by unfold cost; fun_prop
    exact this.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ : ContinuousCorrespondence (fun _ : X => Y) :=
    ⟨UpperHemicontinuous.const, LowerHemicontinuous.const⟩
  have hne : ∀ x : X, ((fun _ : X => Y) x).Nonempty := fun _ => hYne
  have hK : ∀ x : X, IsCompact ((fun _ : X => Y) x) := fun _ => hYc
  have hex : ∀ x : X, (argmax (fun (p : X) (y : ι → ℝ) => cost p.1 y) (fun _ => Y) x).Nonempty :=
    fun x => argmax_nonempty hf (hne x) (hK x)
  choose g hg using hex
  have hsing : ∀ x : X, argmax (fun (p : X) (y : ι → ℝ) => cost p.1 y) (fun _ => Y) x = {g x} :=
    fun x => (huniq x.1 x.2).eq_singleton_of_mem (hg x)
  have hgc := continuous_of_argmax_eq_singleton hf hΦ hne hK hsing
  refine ⟨fun p => if h : PositivePrices p then g ⟨p, h⟩ else 0, fun p hp => ?_, ?_⟩
  · simp only [hp, ↓reduceDIte]; exact hg ⟨p, hp⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : Set.domRestrict {p | PositivePrices p}
        (fun p => if h : PositivePrices p then g ⟨p, h⟩ else 0) =
          fun x => g ⟨x.1, x.2⟩ := by
      funext x
      show (if h : PositivePrices x.1 then g ⟨x.1, h⟩ else 0) = g ⟨x.1, x.2⟩
      rw [dite_eq_left (show PositivePrices x.1 from x.2)]
    rw [this]; exact hgc.comp (Continuous.subtype_mk continuous_subtype_val _)

/-- **Existence with production, unique-supply form.** As
`exists_walrasianEquilibrium_production`, with continuity of supply replaced by
uniqueness of each firm's profit maximizer at strictly positive prices (true,
for example, for strictly convex production sets). -/
theorem exists_walrasianEquilibrium_production_of_unique [Nonempty ι]
    (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, RegularUtility (u a))
    (hω : PositivePrices E.totalEndowment) (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j)
    (hYc : ∀ j, IsCompact (E.prod j))
    (huniq : ∀ j p, PositivePrices p → {y | ProfitMax p (E.prod j) y}.Subsingleton) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y := by
  choose s hs hsc using fun j => exists_continuous_supply (hYc j) ⟨0, hY0 j⟩ (huniq j)
  exact E.exists_walrasianEquilibrium_production hpref hreg hω hY0 hYc hs hsc

end ProductionEconomy


namespace GEExamples

/-- Euclidean length of a price vector in `ℝ²`. -/
noncomputable def norm2 (p : Fin 2 → ℝ) : ℝ := Real.sqrt (p 0 ^ 2 + p 1 ^ 2)

/-- The disc production set: centre `(−1, −2)`, radius `√5`, so `0` is on its
boundary (inaction is possible). It lies in the half-plane `y₀ + 2 y₁ ≤ 0`, so
there is no free lunch (`discSet_noFreeLunch`); depending on prices the firm
turns one good into the other. -/
def discSet : Set (Fin 2 → ℝ) := {y | (y 0 + 1) ^ 2 + (y 1 + 2) ^ 2 ≤ 5}

/-- Supply on the disc: `c + ρ p / ‖p‖₂`. -/
noncomputable def discSupply (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-1 + Real.sqrt 5 * p 0 / norm2 p, -2 + Real.sqrt 5 * p 1 / norm2 p]

theorem norm2_pos {p : Fin 2 → ℝ} (hp : PositivePrices p) : 0 < norm2 p := by
  unfold norm2; have := hp 0; positivity

theorem norm2_sq (p : Fin 2 → ℝ) : norm2 p ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  unfold norm2; rw [Real.sq_sqrt (by positivity)]

theorem zero_mem_discSet : (0 : Fin 2 → ℝ) ∈ discSet := by
  simp only [discSet, Set.mem_ofPred_eq, Pi.zero_apply]; norm_num

/-- **No free lunch**: the only nonnegative net output in `discSet` is `0`. -/
theorem discSet_noFreeLunch {y : Fin 2 → ℝ} (hy : y ∈ discSet) (h0 : 0 ≤ y) : y = 0 := by
  simp only [discSet, Set.mem_ofPred_eq] at hy
  have a : 0 ≤ y 0 := h0 0
  have b : 0 ≤ y 1 := h0 1
  have hhalf : y 0 + 2 * y 1 ≤ 0 := by
    nlinarith [sq_nonneg (2 * (y 0 + 1) - (y 1 + 2))]
  funext i; fin_cases i <;> simp <;> linarith

theorem isCompact_discSet : IsCompact discSet := by
  have hclosed : IsClosed discSet :=
    isClosed_le (by fun_prop) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : Fin 2 → ℝ)).2 ⟨5, fun y hy => ?_⟩
  simp only [discSet, Set.mem_ofPred_eq] at hy
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have h0 := sq_nonneg (y 0 + 1); have h1 := sq_nonneg (y 1 + 2)
  fin_cases i <;> simp <;> constructor <;> nlinarith

theorem discSupply_profitMax {p : Fin 2 → ℝ} (hp : PositivePrices p) :
    ProductionEconomy.ProfitMax p discSet (discSupply p) := by
  have hN := norm2_pos hp
  have hN2 := norm2_sq p
  set ρ := Real.sqrt 5 with hρ
  have hρ2 : ρ ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  refine ⟨?_, fun y hy => ?_⟩
  · simp only [discSet, discSupply, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : (ρ * p 0 / norm2 p) ^ 2 + (ρ * p 1 / norm2 p) ^ 2 = ρ ^ 2 := by
      field_simp; rw [hN2]
    nlinarith
  · simp only [discSet, Set.mem_ofPred_eq] at hy
    simp only [cost, Fin.sum_univ_two, discSupply, Matrix.cons_val_zero, Matrix.cons_val_one]
    set a := y 0 + 1
    set b := y 1 + 2
    have hcs : (p 0 * a + p 1 * b) ^ 2 ≤ (norm2 p * ρ) ^ 2 := by
      rw [mul_pow, hN2, hρ2]
      nlinarith [sq_nonneg (p 0 * b - p 1 * a), sq_nonneg (p 0), sq_nonneg (p 1)]
    have hX : p 0 * a + p 1 * b ≤ norm2 p * ρ := by
      have : 0 ≤ norm2 p * ρ := mul_nonneg hN.le hρ0
      nlinarith
    have hval : p 0 * (-1 + ρ * p 0 / norm2 p) + p 1 * (-2 + ρ * p 1 / norm2 p) =
        -(p 0) - 2 * p 1 + norm2 p * ρ := by
      field_simp
      nlinarith [hN2]
    rw [hval]
    have hy0 : y 0 = a - 1 := by simp [a]
    have hy1 : y 1 = b - 2 := by simp [b]
    rw [hy0, hy1]
    linarith

theorem continuousOn_discSupply : ContinuousOn discSupply {p | PositivePrices p} := by
  have hN : ContinuousOn norm2 {p | PositivePrices p} := by
    unfold norm2; fun_prop
  have hne : ∀ p ∈ {p : Fin 2 → ℝ | PositivePrices p}, norm2 p ≠ 0 := fun p hp =>
    (norm2_pos hp).ne'
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · simp only [discSupply]
    exact continuousOn_const.add
      ((continuousOn_const.mul (continuous_apply 0).continuousOn).div hN hne)
  · simp only [discSupply]
    exact continuousOn_const.add
      ((continuousOn_const.mul (continuous_apply 1).continuousOn).div hN hne)

/-- Witness economy: two square-root consumers owning `(1, 0)` and `(0, 1)` and
half of one firm each; the firm's production set is the disc `discSet`. -/
noncomputable def discEconomy : ProductionEconomy (Fin 2) (Fin 1) (Fin 2) where
  pref _ := prefOf uSqrt
  endow a := fun k => if a = k then 1 else 0
  endow_nonneg a k := by simp only [Pi.zero_apply]; split_ifs <;> norm_num
  prod _ := discSet
  share _ _ := 1 / 2
  share_nonneg _ _ := by norm_num
  share_sum _ := by simp

/-- **Existence for the disc economy.** (Only existence is claimed; whether the
firm is active in equilibrium is not proved here.) -/
theorem discEconomy_exists_equilibrium :
    ∃ p x y, PositivePrices p ∧ discEconomy.IsWalrasianEquilibrium p x y := by
  refine discEconomy.exists_walrasianEquilibrium_production (u := fun _ => uSqrt)
    (fun _ => rfl) (fun _ => regularUtility_of_strictlyQuasiconcave continuous_uSqrt
      strictlyQuasiconcave_uSqrt stronglyMonotone_uSqrt) (fun k => ?_)
    (fun _ => zero_mem_discSet) (fun _ => isCompact_discSet) (s := fun _ => discSupply)
    (fun _ _ hp => discSupply_profitMax hp) (fun _ => continuousOn_discSupply)
  simp only [ExchangeEconomy.totalEndowment, discEconomy, Finset.sum_apply]
  fin_cases k <;> simp

/-- Witness with a pure shareholder: consumers `0` and `1` own `(1, 0)` and
`(0, 1)` and no shares; consumer `2` owns **no goods** and the whole firm. -/
noncomputable def discEconomy3 : ProductionEconomy (Fin 3) (Fin 1) (Fin 2) where
  pref _ := prefOf uSqrt
  endow := ![![1, 0], ![0, 1], ![0, 0]]
  endow_nonneg a k := by fin_cases a <;> fin_cases k <;> simp
  prod _ := discSet
  share a _ := if a = 2 then 1 else 0
  share_nonneg a _ := by split_ifs <;> norm_num
  share_sum _ := by simp

theorem discEconomy3_endow_two : discEconomy3.endow 2 = 0 := by
  simp [discEconomy3]

/-- **Existence with a pure shareholder.** Consumer 2 owns no goods and the whole
firm. Only existence is claimed; consumer 2's equilibrium wealth (the firm's
profit) is not computed. -/
theorem discEconomy3_exists_equilibrium :
    ∃ p x y, PositivePrices p ∧ discEconomy3.IsWalrasianEquilibrium p x y := by
  refine discEconomy3.exists_walrasianEquilibrium_production (u := fun _ => uSqrt)
    (fun _ => rfl) (fun _ => regularUtility_of_strictlyQuasiconcave continuous_uSqrt
      strictlyQuasiconcave_uSqrt stronglyMonotone_uSqrt) (fun k => ?_)
    (fun _ => zero_mem_discSet) (fun _ => isCompact_discSet) (s := fun _ => discSupply)
    (fun _ _ hp => discSupply_profitMax hp) (fun _ => continuousOn_discSupply)
  simp only [ExchangeEconomy.totalEndowment, discEconomy3, Finset.sum_apply]
  fin_cases k <;> simp [Fin.sum_univ_three]

end GEExamples

end Econ
