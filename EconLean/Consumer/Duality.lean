/-
# Indirect utility, expenditure minimization, and duality

MWG §3.D–3.E, §3.G (Props. 3.E.1, 3.E.3, 3.G.1-style identities).

**The economics.** Two mirror-image problems:

* **Utility maximization (UMP)**: maximize `u x` subject to `x ∈ B(p, w)`.
  Its value is the **indirect utility** `v(p, w)`; its solutions are the
  Walrasian demand `x(p, w)`.
* **Expenditure minimization (EMP)**: minimize `p · x` subject to `x ≥ 0`
  and `u x ≥ ū`. Its value is the **expenditure function** `e(p, ū)`; its
  solutions are the **Hicksian (compensated) demand** `h(p, ū)`.

The **duality theorem** says they are two views of the same choice:
* if `x` solves the UMP at `(p, w)`, then `x` solves the EMP at
  `(p, u x)`, and `e(p, v(p, w)) = w`;
* if `x` solves the EMP at `(p, ū)` (with `ū ≥ u 0`), then `x` solves the
  UMP at `(p, p · x)`, `u x = ū` exactly, and `v(p, e(p, ū)) = ū`.

Also: existence of Hicksian demand, homogeneity of `v` (degree 0) and `e`
(degree 1 in prices), monotonicity of `v` in wealth, concavity of `e` in
prices.

Standing assumptions are stated per theorem, so you can see exactly which
result needs which hypothesis: continuity of `u`, local nonsatiation, and
strictly positive prices `p ≫ 0`.

**The Lean.** We *define* `v` as a supremum (`sSup`) and `e` as an infimum
(`sInf`) of sets of reals. Mathlib's `sSup` on ℝ is total (it returns junk
when the set is unbounded or empty), so the real content is in lemmas showing
that, whenever an optimizer exists, `sSup`/`sInf` equals its value
(`IsGreatest.csSup_eq`, `IsLeast.csInf_eq`).
-/
module

public import EconLean.Consumer.Demand

@[expose] public section

namespace Econ

open Filter Topology Set

variable {ι : Type*} [Fintype ι]

/-! ### Definitions -/

/-- Indirect utility `v(p, w) = sup { u x | x ∈ B(p, w) }`. -/
noncomputable def indirectUtility (u : (ι → ℝ) → ℝ) (p : ι → ℝ) (w : ℝ) : ℝ :=
  sSup (u '' budgetSet p w)

/-- Bundles that reach utility level `ū`: `{x ≥ 0 | u x ≥ ū}`. -/
def upperSet (u : (ι → ℝ) → ℝ) (ū : ℝ) : Set (ι → ℝ) := {x | 0 ≤ x ∧ ū ≤ u x}

/-- Expenditure function `e(p, ū) = inf { p · x | x ≥ 0, u x ≥ ū }`. -/
noncomputable def expenditure (u : (ι → ℝ) → ℝ) (p : ι → ℝ) (ū : ℝ) : ℝ :=
  sInf (cost p '' upperSet u ū)

/-- Hicksian demand: the cheapest bundles reaching utility `ū`. -/
def hicksian (u : (ι → ℝ) → ℝ) (p : ι → ℝ) (ū : ℝ) : Set (ι → ℝ) :=
  {x | x ∈ upperSet u ū ∧ ∀ y ∈ upperSet u ū, cost p x ≤ cost p y}

variable {u : (ι → ℝ) → ℝ}

/-! ### Values equal the objective at an optimizer -/

/-- If `x` is demanded, then `v(p, w) = u x`. -/
theorem indirectUtility_eq {p : ι → ℝ} {w : ℝ} {x : ι → ℝ}
    (hx : x ∈ demand (prefOf u) p w) : indirectUtility u p w = u x := by
  -- `u x` is the *greatest* element of `u '' B(p, w)`.
  refine IsGreatest.csSup_eq ⟨mem_image_of_mem u hx.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hx.2 y hy

/-- If `x` is Hicksian-demanded, then `e(p, ū) = p · x`. -/
theorem expenditure_eq {p : ι → ℝ} {ū : ℝ} {x : ι → ℝ}
    (hx : x ∈ hicksian u p ū) : expenditure u p ū = cost p x := by
  refine IsLeast.csInf_eq ⟨mem_image_of_mem (cost p) hx.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hx.2 y hy

/-! ### A technical lemma: scaling down a bundle

If `y` is strictly above the utility level `ū ≥ u 0` and prices are positive,
we can shrink `y` slightly (to `t • y` with `t < 1`) and stay above `ū`
while strictly saving money. This is the workhorse of the second half of
duality and uses continuity of `u`. -/

theorem exists_cheaper_above (hu : Continuous u) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {ū : ℝ} (h0 : u 0 ≤ ū) {y : ι → ℝ} (hy : 0 ≤ y) (hyū : ū < u y) :
    ∃ z, 0 ≤ z ∧ ū < u z ∧ cost p z < cost p y := by
  -- First, `y` must cost something: if `p · y = 0` then `y = 0`, but
  -- `u 0 ≤ ū < u y`.
  have hcost : 0 < cost p y := by
    rcases (cost_nonneg (fun i => (hp i).le) hy).lt_or_eq with h | h
    · exact h
    · have : y = 0 := eq_zero_of_cost_eq_zero hp hy h.symm
      subst this
      exact absurd hyū (not_lt.2 h0)
  -- `t ↦ u (t • y)` is continuous and exceeds `ū` at `t = 1`, so it exceeds
  -- `ū` for all `t` close enough to 1 from below.
  have hcont : Continuous fun t : ℝ => u (t • y) := hu.comp (continuous_id.smul continuous_const)
  have hev1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), ū < u (t • y) := by
    have : ū < u ((1 : ℝ) • y) := by simpa using hyū
    exact nhdsWithin_le_nhds (hcont.continuousAt.eventually (lt_mem_nhds this))
  have hev2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  -- The filter `𝓝[<] 1` is nontrivial, so some `t` satisfies both.
  obtain ⟨t, ht, ⟨ht0, ht1⟩⟩ := (hev1.and hev2).exists
  refine ⟨t • y, smul_nonneg ht0.le hy, ht, ?_⟩
  rw [cost_smul_right]
  -- `t * c < c` for `0 < c` and `t < 1`.
  nlinarith

/-! ### Duality, part 1: UMP solutions solve the EMP (MWG Prop. 3.E.3(i)) -/

/-- If `x` maximizes utility at `(p, w)` and preferences are locally
nonsatiated, then `x` minimizes expenditure at `(p, u x)`. -/
theorem demand_subset_hicksian (hlns : LocallyNonsatiated (prefOf u))
    {p : ι → ℝ} {w : ℝ} {x : ι → ℝ} (hx : x ∈ demand (prefOf u) p w) :
    x ∈ hicksian u p (u x) := by
  refine ⟨⟨hx.1.1, le_rfl⟩, fun y hy => ?_⟩
  -- Suppose `y` reaches `u x` more cheaply. Then `y` leaves money unspent,
  -- so (local nonsatiation) some affordable `z` beats `y`, hence beats `x`.
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hzB, hzy⟩ :=
    exists_better_affordable hlns hy.1 (lt_of_lt_of_le hlt hx.1.2)
  have hzy' : u y < u z := ((represents_prefOf u).P_iff z y).1 hzy
  -- But `x` is optimal in `B(p, w)`, so `u z ≤ u x ≤ u y < u z`.
  have hzx : u z ≤ u x := hx.2 z hzB
  linarith [hy.2]

/-- **Duality identity `e(p, v(p, w)) = w`.** -/
theorem expenditure_indirectUtility (hu : Continuous u)
    (hlns : LocallyNonsatiated (prefOf u)) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {w : ℝ} (hw : 0 ≤ w) :
    expenditure u p (indirectUtility u p w) = w := by
  obtain ⟨x, hx⟩ := demand_nonempty hu hp hw
  rw [indirectUtility_eq hx, expenditure_eq (demand_subset_hicksian hlns hx)]
  exact walras_law hlns hx

/-! ### Duality, part 2: EMP solutions solve the UMP (MWG Prop. 3.E.3(ii)) -/

/-- **No excess utility.** A Hicksian bundle reaches *exactly* `ū`. -/
theorem utility_eq_of_mem_hicksian (hu : Continuous u) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {ū : ℝ} (h0 : u 0 ≤ ū) {x : ι → ℝ} (hx : x ∈ hicksian u p ū) : u x = ū := by
  refine le_antisymm (not_lt.1 fun hlt => ?_) hx.1.2
  -- If `u x > ū`, a scaled-down `z` still reaches `ū` and is cheaper.
  obtain ⟨z, hz0, hzū, hzc⟩ := exists_cheaper_above hu hp h0 hx.1.1 hlt
  exact absurd (hx.2 z ⟨hz0, hzū.le⟩) (not_le.2 hzc)

/-- If `x` minimizes expenditure for utility `ū ≥ u 0`, then `x` maximizes
utility at prices `p` and wealth `p · x`. -/
theorem hicksian_subset_demand (hu : Continuous u) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {ū : ℝ} (h0 : u 0 ≤ ū) {x : ι → ℝ} (hx : x ∈ hicksian u p ū) :
    x ∈ demand (prefOf u) p (cost p x) := by
  refine ⟨⟨hx.1.1, le_rfl⟩, fun y hy => ?_⟩
  -- Suppose an affordable `y` has `u y > u x ≥ ū`. Shrinking `y` gives a
  -- bundle above `ū` that is cheaper than `y`, hence cheaper than `x`.
  show u y ≤ u x
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hz0, hzū, hzc⟩ := exists_cheaper_above hu hp h0 hy.1 (lt_of_le_of_lt hx.1.2 hlt)
  have := hx.2 z ⟨hz0, hzū.le⟩
  linarith [hy.2]

/-! ### Existence of Hicksian demand -/

/-- If utility `ū` is reachable at all (by some `x₀ ≥ 0`), Hicksian demand is
nonempty. We restrict to the compact set of bundles reaching `ū` that cost no
more than `x₀`, and minimize cost there. -/
theorem hicksian_nonempty (hu : Continuous u) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {ū : ℝ} {x₀ : ι → ℝ} (hx₀ : x₀ ∈ upperSet u ū) : (hicksian u p ū).Nonempty := by
  set K := budgetSet p (cost p x₀) ∩ {x | ū ≤ u x} with hK
  have hKc : IsCompact K :=
    (isCompact_budgetSet hp _).inter_right (isClosed_le continuous_const hu)
  have hx₀K : x₀ ∈ K := ⟨⟨hx₀.1, le_rfl⟩, hx₀.2⟩
  obtain ⟨x, hxK, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ (continuous_cost p).continuousOn
  refine ⟨x, ⟨hxK.1.1, hxK.2⟩, fun y hy => ?_⟩
  -- Either `y` is in `K` (then use minimality), or it costs more than `x₀`.
  by_cases hyc : cost p y ≤ cost p x₀
  · exact hmin ⟨⟨hy.1, hyc⟩, hy.2⟩
  · exact (hmin hx₀K).trans (le_of_lt (not_le.1 hyc))

/-- **Duality identity `v(p, e(p, ū)) = ū`** (for reachable `ū ≥ u 0`). -/
theorem indirectUtility_expenditure (hu : Continuous u) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {ū : ℝ} (h0 : u 0 ≤ ū) {x₀ : ι → ℝ} (hx₀ : x₀ ∈ upperSet u ū) :
    indirectUtility u p (expenditure u p ū) = ū := by
  obtain ⟨x, hx⟩ := hicksian_nonempty hu hp hx₀
  rw [expenditure_eq hx, indirectUtility_eq (hicksian_subset_demand hu hp h0 hx)]
  exact utility_eq_of_mem_hicksian hu hp h0 hx

/-! ### Properties of `v` and `e` (MWG Props. 3.D.3, 3.E.2) -/

/-- `v` is homogeneous of degree zero in `(p, w)`. -/
theorem indirectUtility_smul {α : ℝ} (hα : 0 < α) (p : ι → ℝ) (w : ℝ) :
    indirectUtility u (α • p) (α * w) = indirectUtility u p w := by
  simp only [indirectUtility, budgetSet_smul hα]

/-- `v` is nondecreasing in wealth. -/
theorem indirectUtility_mono (hu : Continuous u) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {w w' : ℝ} (hw : 0 ≤ w) (hww' : w ≤ w') :
    indirectUtility u p w ≤ indirectUtility u p w' := by
  obtain ⟨x, hx⟩ := demand_nonempty hu hp hw
  obtain ⟨x', hx'⟩ := demand_nonempty hu hp (hw.trans hww')
  rw [indirectUtility_eq hx, indirectUtility_eq hx']
  -- `x` is still affordable with more wealth, so `x'` is at least as good.
  exact hx'.2 x ⟨hx.1.1, hx.1.2.trans hww'⟩

/-- Hicksian demand is unchanged when all prices are scaled by α > 0. -/
theorem hicksian_smul {α : ℝ} (hα : 0 < α) (p : ι → ℝ) (ū : ℝ) :
    hicksian u (α • p) ū = hicksian u p ū := by
  ext x
  simp only [hicksian, cost_smul_left, mul_le_mul_iff_right₀ hα]

/-- `e` is homogeneous of degree one in prices. -/
theorem expenditure_smul {α : ℝ} (hα : 0 < α) {p : ι → ℝ} {ū : ℝ} {x : ι → ℝ}
    (hx : x ∈ hicksian u p ū) : expenditure u (α • p) ū = α * expenditure u p ū := by
  have hx' : x ∈ hicksian u (α • p) ū := (hicksian_smul hα p ū).symm ▸ hx
  rw [expenditure_eq hx', expenditure_eq hx, cost_smul_left]

/-- **`e` is concave in prices.** For `a, b ≥ 0` with `a + b = 1`,
`e(a p + b q, ū) ≥ a e(p, ū) + b e(q, ū)`.

Intuition: the bundle that is cheapest at the mixed prices is feasible, but
not necessarily cheapest, at `p` and at `q`. -/
theorem expenditure_concave {p q : ι → ℝ} {ū a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {xp xq xm : ι → ℝ} (hxp : xp ∈ hicksian u p ū) (hxq : xq ∈ hicksian u q ū)
    (hxm : xm ∈ hicksian u (a • p + b • q) ū) :
    a * expenditure u p ū + b * expenditure u q ū ≤ expenditure u (a • p + b • q) ū := by
  rw [expenditure_eq hxp, expenditure_eq hxq, expenditure_eq hxm, cost_add_left,
    cost_smul_left, cost_smul_left]
  -- `xm` reaches `ū`, so it costs at least the minimum at `p` and at `q`.
  have h1 := hxp.2 xm hxm.1
  have h2 := hxq.2 xm hxm.1
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end Econ
