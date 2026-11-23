/-
# Continuity of demand and indirect utility

MWG §3.D (Prop. 3.D.2–3.D.3), §3.AA; Aliprantis–Border ch. 17.

**The economics.** How does the consumer's choice respond to small changes in
prices and wealth? Berge's maximum theorem (`Foundations/Maximum.lean`) says:
if the objective is continuous and the constraint correspondence is
*continuous* (upper and lower hemicontinuous) with nonempty compact values,
then the value function is continuous and the set of maximizers is upper
hemicontinuous.

Here the constraint is the **budget correspondence** `(p, w) ↦ B(p, w)` on the
domain of strictly positive prices `p ≫ 0` and positive wealth `w > 0`. The
main work is to show it is continuous:
* **UHC**: its graph is closed (`p · x ≤ w` is a closed condition) and, near
  any `(p, w)`, budget sets stay inside one fixed compact box.
* **LHC**: any affordable bundle `y` can be approximated by affordable bundles
  at nearby `(p', w')`. Trick: shrink `y` slightly to `t • y` so it costs
  *strictly* less than `w` (possible because `w > 0`), and a strict
  inequality survives small perturbations of `(p, w)`.

Then:
1. **Indirect utility `v(p, w)` is continuous** (MWG Prop. 3.D.3).
2. **The demand correspondence is upper hemicontinuous.**
3. **Strictly quasiconcave utility gives a unique, hence continuous, demand
   function** (MWG Prop. 3.D.2(iii) and §3.AA).

**The Lean.** Berge's theorem is stated for a correspondence on a whole space,
so we take as domain the *subtype* `PriceWealth ι` of pairs `(p, w)` with
`p ≫ 0` and `w > 0`. It is an open subset of `(ι → ℝ) × ℝ` with the subspace
topology, and Lean gives it that topology automatically.
-/
module

public import EconLean.Consumer.Duality
public import EconLean.Foundations.Maximum

@[expose] public section

namespace Econ

open Filter Topology Set

variable {ι : Type*} [Fintype ι]

/-- The domain of price–wealth pairs: strictly positive prices, positive wealth. -/
abbrev PriceWealth (ι : Type*) : Type _ :=
  {pw : (ι → ℝ) × ℝ // (∀ i, 0 < pw.1 i) ∧ 0 < pw.2}

/-- The budget correspondence `(p, w) ↦ B(p, w)`. -/
def budgetCorr (pw : PriceWealth ι) : Set (ι → ℝ) := budgetSet pw.1.1 pw.1.2

/-! ### Upper hemicontinuity -/

/-- `(p, w, x) ↦ (p · x, w)` pieces are continuous on the domain. -/
theorem continuous_cost_joint :
    Continuous fun q : PriceWealth ι × (ι → ℝ) => cost q.1.1.1 q.2 := by
  unfold cost
  fun_prop

/-- The graph of the budget correspondence is closed. -/
theorem isClosed_graph_budgetCorr : IsClosed (graph (budgetCorr (ι := ι))) := by
  have h1 : IsClosed {q : PriceWealth ι × (ι → ℝ) | 0 ≤ q.2} :=
    isClosed_le continuous_const continuous_snd
  have h2 : IsClosed {q : PriceWealth ι × (ι → ℝ) | cost q.1.1.1 q.2 ≤ q.1.1.2} :=
    isClosed_le continuous_cost_joint (by fun_prop)
  exact h1.inter h2

/-- Near `(p, w)`, prices stay above `p / 2` and wealth below `2 w`. -/
theorem eventually_near (pw : PriceWealth ι) :
    ∀ᶠ q in 𝓝 pw, (∀ i, pw.1.1 i / 2 < q.1.1 i) ∧ q.1.2 < 2 * pw.1.2 := by
  refine (eventually_all.2 fun i => ?_).and ?_
  · have hc : Continuous fun q : PriceWealth ι => q.1.1 i := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by linarith [pw.2.1 i]))
  · have hc : Continuous fun q : PriceWealth ι => q.1.2 := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by linarith [pw.2.2]))

/-- **The budget correspondence is upper hemicontinuous.** Near `(p, w)`,
every budget set lies in the compact box `[0, 4w/p]`. -/
theorem upperHemicontinuous_budgetCorr : UpperHemicontinuous (budgetCorr (ι := ι)) := by
  intro pw
  refine upperHemicontinuousAt_of_isClosed_graph isClosed_graph_budgetCorr
    (isCompact_Icc (a := (0 : ι → ℝ)) (b := fun i => 4 * pw.1.2 / pw.1.1 i)) ?_
  filter_upwards [eventually_near pw] with q hq x hx
  refine ⟨hx.1, fun i => ?_⟩
  -- From the budget: `xᵢ qᵢ ≤ w'`. With `pᵢ < 2 qᵢ` and `w' < 2w`, get
  -- `xᵢ pᵢ ≤ 4 w`.
  have hxi := le_div_of_mem_budgetSet q.2.1 hx i
  rw [le_div_iff₀ (q.2.1 i)] at hxi
  have hpi := pw.2.1 i
  rw [le_div_iff₀ hpi]
  have hx0 : 0 ≤ x i := hx.1 i
  have hprod : 0 ≤ x i * (2 * q.1.1 i - pw.1.1 i) :=
    mul_nonneg hx0 (by linarith [hq.1 i])
  nlinarith [hq.2]

/-! ### Lower hemicontinuity -/

/-- **The budget correspondence is lower hemicontinuous** (uses `w > 0`). -/
theorem lowerHemicontinuous_budgetCorr : LowerHemicontinuous (budgetCorr (ι := ι)) := by
  intro pw
  show LowerHemicontinuousAt budgetCorr pw
  refine lowerHemicontinuousAt_iff_textbook.2 ?_
  rintro U hU ⟨y, hyB, hyU⟩
  obtain ⟨⟨p, w⟩, hp, hw⟩ := pw
  -- Step 1: shrink `y` to `z = t • y` that is still in `U` and costs `< w`.
  have hcont : Continuous fun t : ℝ => t • y := continuous_id.smul continuous_const
  have hev1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t • y ∈ U :=
    nhdsWithin_le_nhds (hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hyU))
  have hev2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨t, htU, ht0, ht1⟩ := (hev1.and hev2).exists
  set z := t • y
  have hz0 : 0 ≤ z := smul_nonneg ht0.le hyB.1
  have hzc : cost p z < w := by
    have hc0 := cost_nonneg (fun i => (hp i).le) hyB.1
    have hcw : cost p y ≤ w := hyB.2
    simp only [z, cost_smul_right]
    nlinarith
  -- Step 2: the strict inequality `cost p' z < w'` persists near `(p, w)`.
  have hg : Continuous fun q : PriceWealth ι => q.1.2 - cost q.1.1 z := by
    unfold cost; fun_prop
  have hev : ∀ᶠ q in 𝓝 (⟨(p, w), hp, hw⟩ : PriceWealth ι), 0 < q.1.2 - cost q.1.1 z :=
    hg.continuousAt.eventually (lt_mem_nhds (by simpa using hzc))
  filter_upwards [hev] with q hq
  exact ⟨z, ⟨hz0, by linarith⟩, htU⟩

theorem continuousCorrespondence_budgetCorr :
    ContinuousCorrespondence (budgetCorr (ι := ι)) :=
  ⟨upperHemicontinuous_budgetCorr, lowerHemicontinuous_budgetCorr⟩

theorem budgetCorr_nonempty (pw : PriceWealth ι) : (budgetCorr pw).Nonempty :=
  ⟨0, zero_mem_budgetSet pw.2.2.le⟩

theorem isCompact_budgetCorr (pw : PriceWealth ι) : IsCompact (budgetCorr pw) :=
  isCompact_budgetSet pw.2.1 _

/-! ### Consequences of Berge's theorem -/

variable {u : (ι → ℝ) → ℝ}

omit [Fintype ι] in
/-- The UMP as a Berge problem: the objective `(p, w, x) ↦ u x` ignores `(p, w)`. -/
theorem continuous_uncurry_utility (hu : Continuous u) :
    Continuous (Function.uncurry fun (_ : PriceWealth ι) (x : ι → ℝ) => u x) :=
  hu.comp continuous_snd

/-- Berge's argmax is exactly Walrasian demand. -/
theorem argmax_eq_demand (pw : PriceWealth ι) :
    argmax (fun _ x => u x) budgetCorr pw = demand (prefOf u) pw.1.1 pw.1.2 := rfl

/-- **Indirect utility is continuous** in `(p, w)` (MWG Prop. 3.D.3). -/
theorem continuous_indirectUtility (hu : Continuous u) :
    Continuous fun pw : PriceWealth ι => indirectUtility u pw.1.1 pw.1.2 :=
  continuous_maxValue (continuous_uncurry_utility hu) continuousCorrespondence_budgetCorr
    budgetCorr_nonempty isCompact_budgetCorr

/-- **Walrasian demand is upper hemicontinuous** in `(p, w)`. -/
theorem upperHemicontinuous_demand (hu : Continuous u) :
    UpperHemicontinuous fun pw : PriceWealth ι => demand (prefOf u) pw.1.1 pw.1.2 :=
  upperHemicontinuous_argmax (continuous_uncurry_utility hu)
    continuousCorrespondence_budgetCorr budgetCorr_nonempty isCompact_budgetCorr

/-- **A single-valued demand function is continuous** (MWG §3.AA). -/
theorem continuous_demand_function (hu : Continuous u) {x : PriceWealth ι → (ι → ℝ)}
    (hx : ∀ pw, demand (prefOf u) pw.1.1 pw.1.2 = {x pw}) : Continuous x :=
  continuous_of_argmax_eq_singleton (continuous_uncurry_utility hu)
    continuousCorrespondence_budgetCorr budgetCorr_nonempty isCompact_budgetCorr hx

/-! ### Uniqueness from strict quasiconcavity (MWG Prop. 3.D.2(iii)) -/

/-- `u` is *strictly quasiconcave* on the consumption set `ℝ^ι₊`: any strict
mix of two distinct nonnegative bundles is strictly better than the worse of
the two. (Only the orthant matters, matching MWG's consumption set.) -/
def StrictlyQuasiconcave (u : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y : ι → ℝ, 0 ≤ x → 0 ≤ y → x ≠ y → ∀ t : ℝ, 0 < t → t < 1 →
    min (u x) (u y) < u (t • x + (1 - t) • y)

/-- With strictly quasiconcave utility, demand has at most one element: two
different optimal bundles could be averaged into an affordable, strictly
better one. -/
theorem demand_subsingleton (hsq : StrictlyQuasiconcave u) (p : ι → ℝ) (w : ℝ) :
    (demand (prefOf u) p w).Subsingleton := by
  intro x hx y hy
  by_contra hne
  -- The midpoint is affordable (convex budget set) ...
  have hmid : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y ∈ budgetSet p w :=
    convex_budgetSet p w hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  -- ... strictly better than the worse of `x, y` ...
  have hlt := hsq x y hx.1.1 hy.1.1 hne (1 / 2) (by norm_num) (by norm_num)
  -- ... but no better than either, since both are optimal.
  have h1 : u ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) ≤ u x := hx.2 _ hmid
  have h2 : u ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) ≤ u y := hy.2 _ hmid
  have := lt_of_lt_of_le hlt (le_min h1 h2)
  exact lt_irrefl _ this

/-- **Continuous demand function.** If `u` is continuous and strictly
quasiconcave, demand at each `(p, w)` is a single bundle, and the resulting
demand function is continuous on `p ≫ 0, w > 0`. -/
theorem exists_continuous_demand_function (hu : Continuous u) (hsq : StrictlyQuasiconcave u) :
    ∃ x : PriceWealth ι → (ι → ℝ), Continuous x ∧
      ∀ pw, demand (prefOf u) pw.1.1 pw.1.2 = {x pw} := by
  -- Pick the unique demanded bundle at each `(p, w)`.
  have hne : ∀ pw : PriceWealth ι, (demand (prefOf u) pw.1.1 pw.1.2).Nonempty :=
    fun pw => demand_nonempty hu pw.2.1 pw.2.2.le
  choose x hx using hne
  have hsing : ∀ pw, demand (prefOf u) pw.1.1 pw.1.2 = {x pw} := fun pw =>
    (demand_subsingleton hsq _ _).eq_singleton_of_mem (hx pw)
  exact ⟨x, continuous_demand_function hu hsing, hsing⟩

end Econ
