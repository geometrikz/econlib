/-
# Existence of equilibrium without convex preferences (Aumann 1966)

**The economics.** In an economy with a continuum of negligible traders,
aggregate demand is convex even when individual preferences are not, so
Walrasian equilibria exist without any convexity assumption (Aumann 1966;
Hildenbrand 1974, ch. 2; the finite-economy shadow is the Shapley–Folkman /
Starr approximate-equilibrium theorem). This is one of the cleanest
micro-to-macro statements in general equilibrium: an aggregate property
(existence) holds although the individual property behind it in finite
economies (convexity) fails.

**Results (finitely many types).**
* `AumannExistence.exists_convexifiedEquilibrium`: a finite economy of types
  `t` with masses `mₜ > 0`, continuous strongly monotone utilities (no
  quasiconcavity) and endowments `ωₜ ≫ 0` has prices `p ≫ 0` and bundles
  `x̄ₜ ∈ conv (demandₜ p)` with `∑ mₜ x̄ₜ = ∑ mₜ ωₜ`. Kakutani is applied to the
  **convex hull** of truncated demand (closed graph by
  `isClosed_graph_convexHull`).
* `AumannExistence.eventually_lt_sum_of_mem_truncDemand`: the boundary
  behaviour that replaces convexity in removing the truncation: near a price
  vector with a free good, every truncated demand has a large total quantity,
  uniformly in the box size. `exists_pos_le_of_notMem` turns this into a
  uniform lower bound `π > 0` on equilibrium prices, chosen before the box.
* `ContinuumEconomy.exists_isWalrasianEquilibrium_of_types_nonconvex`: a
  nonatomic continuum economy with finitely many such types has a Walrasian
  equilibrium at positive prices (convexified equilibrium, then the Lyapunov
  splitting bridge of `GE/ContinuumExistence.lean`).
* Witness `sqContinuum`: utility `x₀² + x₁²` (strongly monotone, not
  quasiconcave, `not_quasiconcaveOn_uSq`); an equilibrium exists, and in every
  equilibrium at positive prices identical traders consume different bundles
  (`sqContinuum_exists_asymmetric_equilibrium`,
  `sqContinuum_no_symmetric_equilibrium`): no equilibrium allocation treats
  identical traders identically.

**Scope.** Compared with Aumann (1966):
* finitely many types rather than a measurable preference map (infinitely many
  types would need measurable selections and a Fatou lemma in several
  dimensions); the type map fixes preferences and endowments for every trader
  (not a.e.), and every type has positive mass;
* preferences are given by continuous utilities on `ℝᴸ` rather than continuous
  relations on `ℝᴸ₊`; for complete, transitive, continuous preferences this is
  no loss (Debreu's representation theorem and a Tietze extension), but it
  excludes the incomplete or intransitive preferences of Schmeidler (1969);
* strong monotonicity on `ℝᴸ₊` is Aumann's own desirability assumption;
* every type's endowment is strictly positive, whereas Aumann (and Hildenbrand
  1974) need only the aggregate endowment `∫ e ≫ 0`;
* the population measure may be any finite measure (Aumann normalizes
  `μ(Ω) = 1`).
-/
module

public import EconLean.GE.ContinuumExistence
public import EconLean.Foundations.ConvexifiedCorrespondence
public import EconLean.GE.ExistenceArrowDebreu

@[expose] public section

noncomputable section

namespace Econ

namespace AumannExistence

open Filter Topology Set Finset

variable {ι : Type*} [Fintype ι]

/-- The value of the unit bundle of good `i` is its price. -/
theorem cost_single (p : ι → ℝ) [DecidableEq ι] (i : ι) : cost p (Pi.single i 1) = p i := by
  simp [cost, Pi.single_apply]

/-- **Truncated demand without convexity**: for a continuous utility the
maximizers on the truncated budget set are nonempty and form a closed graph in
`(p, w, x)` (Berge). Unlike `truncDemand_props`, no quasiconcavity is assumed,
and the values need not be convex. -/
theorem truncDemand_closed_nonempty {u : (ι → ℝ) → ℝ} (hu : Continuous u) (c m : ℝ)
    (hc : 0 ≤ c) (hm : 0 < m) :
    IsClosed (graph (argmax (fun (_ : (ι → ℝ) × ℝ) x => u x) (truncBudget c m))) ∧
      ∀ pw, (argmax (fun _ x => u x) (truncBudget c m) pw).Nonempty := by
  have hf : Continuous (Function.uncurry fun (_ : (ι → ℝ) × ℝ) (x : ι → ℝ) => u x) :=
    hu.comp continuous_snd
  have hne : ∀ pw, (truncBudget (ι := ι) c m pw).Nonempty := by
    intro pw
    have h0 : cost pw.1 (0 : ι → ℝ) ≤ max pw.2 m := by
      simp only [cost, Pi.zero_apply, mul_zero, sum_const_zero]
      exact le_max_of_le_right hm.le
    exact ⟨0, ⟨le_rfl, fun _ => hc⟩, h0⟩
  have hK : ∀ pw, IsCompact (truncBudget (ι := ι) c m pw) := fun pw =>
    isCompact_Icc.of_isClosed_subset (isClosed_truncBudget c m pw) fun _ h => h.1
  have hΦ := continuousCorrespondence_truncBudget (ι := ι) c m hm
  exact ⟨isClosed_graph_of_upperHemicontinuous (upperHemicontinuous_argmax hf hΦ hne hK)
    fun pw => (isCompact_argmax hf (hne pw) (hK pw)).isClosed,
    fun pw => argmax_nonempty hf (hne pw) (hK pw)⟩

/-- The **truncated demand** of a consumer with utility `u` and endowment `ω` at
prices `q`: maximizers of `u` on bundles in the box `[0, c]ᴸ` costing at most
`max (q · ω) m`. -/
def truncDemand (u : (ι → ℝ) → ℝ) (ω : ι → ℝ) (c m : ℝ) (q : ι → ℝ) : Set (ι → ℝ) :=
  argmax (fun (_ : (ι → ℝ) × ℝ) x => u x) (truncBudget c m) (q, cost q ω)

/-- **Demand explodes near a free good** (the boundary behaviour behind
MWG Prop. 17.C.1(v), here without convexity and uniformly in the truncation).
Let `u` be continuous and strongly monotone, and let good `i` be free at `p`.
Then for prices `q` near `p` and every box size `c ≥ B + 1`, every truncated
demand has total quantity `∑ⱼ dⱼ > B`.

Proof: a bundle `d₀ ≥ 0` with `∑ d₀ ≤ B` that is affordable at `p` is beaten by
`s (d₀ + eᵢ)` for some `s < 1`, which is strictly cheaper than the wealth at `p`
and lies in the box; both facts persist near `(p, d₀)`. Bundles unaffordable at
`p` stay unaffordable nearby. The set of such `d₀` is compact. -/
theorem eventually_lt_sum_of_mem_truncDemand [DecidableEq ι] {u : (ι → ℝ) → ℝ}
    (hu : Continuous u) (hmono : StronglyMonotone (prefOf u)) {m : ℝ} (hm : 0 < m)
    (ω : ι → ℝ) {p : ι → ℝ} {i : ι} (hpi : p i = 0) (B : ℝ) :
    ∀ᶠ q in 𝓝 p, ∀ c, B + 1 ≤ c → ∀ d ∈ truncDemand u ω c m q, B < ∑ j, d j := by
  set K : Set (ι → ℝ) := {d | 0 ≤ d ∧ ∑ j, d j ≤ B} with hKdef
  have hKsub : K ⊆ Icc 0 (fun _ => B) := fun d hd =>
    ⟨hd.1, fun j => (Finset.single_le_sum (fun k _ => hd.1 k) (mem_univ j)).trans hd.2⟩
  have hKcl : IsClosed K :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKcl hKsub
  have hcost : Continuous fun z : (ι → ℝ) × (ι → ℝ) => cost z.1 z.2 := by
    unfold cost; fun_prop
  have hw : Continuous fun q : ι → ℝ => max (cost q ω) m := by
    unfold cost; fun_prop
  have key : ∀ d₀ ∈ K, ∀ᶠ z : (ι → ℝ) × (ι → ℝ) in 𝓝 (p, d₀),
      ∀ c, B + 1 ≤ c → z.2 ∉ truncDemand u ω c m z.1 := by
    rintro d₀ ⟨hd0, hdB⟩
    by_cases hcase : cost p d₀ ≤ max (cost p ω) m
    · set d₁ : ι → ℝ := d₀ + Pi.single i 1 with hd₁
      have he0 : (0 : ι → ℝ) ≤ Pi.single i 1 := by
        intro j; by_cases h : j = i
        · subst h; simp
        · simp [h]
      have hne : d₀ ≠ d₁ := by
        intro h
        have := congrFun h i
        simp [hd₁] at this
      have hlt : u d₀ < u d₁ := by
        have := hmono d₀ d₁ hd0 (le_add_of_nonneg_right he0) hne
        exact lt_of_not_ge this.2
      -- shrink `d₁` slightly
      have hev : ∀ᶠ s in 𝓝 (1 : ℝ), u d₀ < u (s • d₁) := by
        have hc1 : ContinuousAt (fun s : ℝ => u (s • d₁)) 1 := by fun_prop
        have : u d₀ < (fun s : ℝ => u (s • d₁)) 1 := by simpa using hlt
        exact hc1.eventually (lt_mem_nhds this)
      obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
      set s : ℝ := max (1 / 2) (1 - ε / 2) with hs
      have hs1 : s < 1 := max_lt (by norm_num) (by linarith)
      have hs0 : 0 ≤ s := le_max_of_le_left (by norm_num)
      have hsd : dist s 1 < ε := by
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor
        · linarith
        · have : 1 - ε / 2 ≤ s := le_max_right _ _
          linarith
      set y : ι → ℝ := s • d₁ with hy
      have huy : u d₀ < u y := hεP hsd
      have hcy : cost p y < max (cost p ω) m := by
        have h1 : cost p y = s * cost p d₀ := by
          rw [hy, cost_smul_right, hd₁, cost_add_right, cost_single, hpi, add_zero]
        have hpos : 0 < max (cost p ω) m := lt_of_lt_of_le hm (le_max_right _ _)
        rw [h1]
        calc s * cost p d₀ ≤ s * max (cost p ω) m := mul_le_mul_of_nonneg_left hcase hs0
          _ < max (cost p ω) m := by nlinarith
      have hybox : ∀ c, B + 1 ≤ c → y ∈ Icc (0 : ι → ℝ) (fun _ => c) := by
        intro c hc
        have hd1 : 0 ≤ d₁ := add_nonneg hd0 he0
        refine ⟨smul_nonneg hs0 hd1, fun j => ?_⟩
        have hdj : d₀ j ≤ B := (hKsub ⟨hd0, hdB⟩).2 j
        have hej : (Pi.single i (1 : ℝ) : ι → ℝ) j ≤ 1 := by
          by_cases h : j = i
          · subst h; simp
          · simp [h]
        have h1 : d₁ j ≤ B + 1 := by simp only [hd₁, Pi.add_apply]; linarith
        have h2 : y j = s * d₁ j := rfl
        have h3 : 0 ≤ d₁ j := hd1 j
        show y j ≤ c
        rw [h2]
        nlinarith
      have hA : ∀ᶠ z : (ι → ℝ) × (ι → ℝ) in 𝓝 (p, d₀), cost z.1 y < max (cost z.1 ω) m :=
        ContinuousAt.eventually_lt (f := fun z : (ι → ℝ) × (ι → ℝ) => cost z.1 y)
          (by unfold cost; fun_prop) ((hw.comp continuous_fst).continuousAt) hcy
      have hB : ∀ᶠ z : (ι → ℝ) × (ι → ℝ) in 𝓝 (p, d₀), u z.2 < u y :=
        ContinuousAt.eventually_lt (hu.comp continuous_snd).continuousAt continuousAt_const huy
      filter_upwards [hA, hB] with z hzA hzB c hc hd
      exact absurd (hd.2 y ⟨hybox c hc, hzA.le⟩) (not_le.2 hzB)
    · replace hcase := not_le.1 hcase
      have hA : ∀ᶠ z : (ι → ℝ) × (ι → ℝ) in 𝓝 (p, d₀), max (cost z.1 ω) m < cost z.1 z.2 :=
        ContinuousAt.eventually_lt (hw.comp continuous_fst).continuousAt hcost.continuousAt hcase
      filter_upwards [hA] with z hz c hc hd
      exact absurd hd.1.2 (not_le.2 hz)
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun q d => ∀ c, B + 1 ≤ c → d ∉ truncDemand u ω c m q) key] with q hq c hc d hd
  by_contra hle
  replace hle := not_lt.1 hle
  exact hq d ⟨hd.1.1.1, hle⟩ c hc hd

/-! ### Convexity of half-spaces cut out by values -/

theorem convex_cost_le (p : ι → ℝ) (r : ℝ) : Convex ℝ {y : ι → ℝ | cost p y ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, cost_add_right, cost_smul_right] at *
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_le_cost (p : ι → ℝ) (r : ℝ) : Convex ℝ {y : ι → ℝ | r ≤ cost p y} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, cost_add_right, cost_smul_right] at *
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_lt_cost (p : ι → ℝ) (r : ℝ) : Convex ℝ {y : ι → ℝ | r < cost p y} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, cost_add_right, cost_smul_right] at *
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simpa using hy
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem sum_eq_cost_one (d : ι → ℝ) : ∑ j, d j = cost (fun _ => 1) d := by simp [cost]

/-- **Prices bounded away from zero off a neighbourhood of the boundary.** If a
set `U` is a neighbourhood of every boundary point of the price simplex, then
prices in the simplex outside `U` are uniformly bounded below by some `π > 0`. -/
theorem exists_pos_le_of_notMem [Nonempty ι] {U : Set (ι → ℝ)}
    (hU : ∀ p ∈ priceSimplex ι, ∀ i, p i = 0 → U ∈ 𝓝 p) :
    ∃ π > 0, ∀ q ∈ priceSimplex ι, q ∉ U → ∀ i, π ≤ q i := by
  set C := priceSimplex ι \ interior U with hC
  have hCc : IsCompact C := isCompact_priceSimplex.diff isOpen_interior
  have hCpos : ∀ q ∈ C, ∀ i, 0 < q i := by
    rintro q ⟨hqΔ, hqU⟩ i
    refine lt_of_le_of_ne (hqΔ.1 i) fun h => hqU ?_
    exact mem_interior_iff_mem_nhds.2 (hU q hqΔ i h.symm)
  have hsub : ∀ q ∈ priceSimplex ι, q ∉ U → q ∈ C := fun q hq hqU =>
    ⟨hq, fun h => hqU (interior_subset h)⟩
  by_cases hne : C.Nonempty
  · have hmin : ∀ i, ∃ πi > 0, ∀ q ∈ C, πi ≤ q i := by
      intro i
      obtain ⟨q₀, hq₀, hmin⟩ := hCc.exists_isMinOn hne (continuous_apply i).continuousOn
      exact ⟨q₀ i, hCpos q₀ hq₀ i, fun q hq => hmin hq⟩
    choose πi hπi0 hπi using hmin
    refine ⟨univ.inf' univ_nonempty πi, (Finset.lt_inf'_iff _).2 fun i _ => hπi0 i,
      fun q hq hqU i => ?_⟩
    exact (Finset.inf'_le _ (mem_univ i)).trans (hπi i q (hsub q hq hqU))
  · exact ⟨1, one_pos, fun q hq hqU => absurd ⟨q, hsub q hq hqU⟩ hne⟩

/-! ### Existence for a finite economy with convexified demand -/

/-- **Equilibrium of the convexified economy** (the finite core of Aumann 1966,
finitely many types, no convexity). Types `t` have masses `mₜ > 0`, continuous
strongly monotone utilities `uₜ` (**not** assumed quasiconcave) and endowments
`ωₜ ≫ 0`. Then there are prices `p ≫ 0` and, for each type, a bundle `x̄ₜ` in
the **convex hull** of its demand, with `∑ₜ mₜ x̄ₜ = ∑ₜ mₜ ωₜ`.

Proof: Kakutani on `Δ × [0, c]^{T × L}` with the convex hull of truncated demand
(closed graph by `isClosed_graph_convexHull`), and prices maximizing the value
of excess demand. At a fixed point, excess demand is `≤ 0`; since convex hulls
of truncated demands near a free good have large total quantity
(`eventually_lt_sum_of_mem_truncDemand`) while feasible bundles do not, prices
are bounded below by a constant `π > 0` chosen before `c`; with `c` above the
largest affordable quantity the truncation does not bind, and budgets bind by
strong monotonicity. -/
theorem exists_convexifiedEquilibrium [Nonempty ι] [DecidableEq ι] {T : Type*} [Fintype T]
    [Nonempty T] (mass : T → ℝ) (hmass : ∀ t, 0 < mass t) {u : T → (ι → ℝ) → ℝ}
    (hu : ∀ t, Continuous (u t)) (hmono : ∀ t, StronglyMonotone (prefOf (u t)))
    {ω : T → ι → ℝ} (hω : ∀ t, PositivePrices (ω t)) :
    ∃ (p : ι → ℝ) (xbar : T → ι → ℝ), PositivePrices p ∧
      (∀ t, xbar t ∈ convexHull ℝ (demand (prefOf (u t)) p (cost p (ω t)))) ∧
      ∑ t, mass t • xbar t = ∑ t, mass t • ω t := by
  classical
  -- floors `mₜ = minᵢ ωₜᵢ > 0`
  have hm : ∀ t, ∃ m, 0 < m ∧ ∀ i, m ≤ ω t i := fun t => by
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image univ (ω t) univ_nonempty
    exact ⟨ω t i0, hω t i0, fun i => hi0 i (mem_univ i)⟩
  choose mt hmt0 hmtle using hm
  have hω0 : ∀ t, 0 ≤ ω t := fun t i => (hω t i).le
  set S : ι → ℝ := ∑ t, mass t • ω t with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => smul_nonneg (hmass t).le (hω0 t)
  set t₀ : T := Classical.arbitrary T
  set B : ℝ := (∑ i, S i) / mass t₀ with hB
  have hB0 : 0 ≤ B := div_nonneg (Finset.sum_nonneg fun i _ => hS0 i) (hmass t₀).le
  set U : Set (ι → ℝ) := {q | ∀ c, B + 1 ≤ c →
    ∀ d ∈ truncDemand (u t₀) (ω t₀) c (mt t₀) q, B < ∑ j, d j} with hU
  obtain ⟨π, hπ0, hπ⟩ := exists_pos_le_of_notMem (U := U) fun p _ i hpi =>
    eventually_lt_sum_of_mem_truncDemand (hu t₀) (hmono t₀) (hmt0 t₀) (ω t₀) hpi B
  set Wb : ℝ := ∑ t, ∑ i, ω t i with hWb
  have hWb0 : 0 ≤ Wb := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ => hω0 t i
  set c : ℝ := B + 1 + Wb / π with hc
  have hcB : B + 1 ≤ c := le_add_of_nonneg_right (div_nonneg hWb0 hπ0.le)
  have hc0 : 0 ≤ c := by linarith
  set D : T → (ι → ℝ) → Set (ι → ℝ) := fun t q => truncDemand (u t) (ω t) c (mt t) q with hD
  have hDp := fun t => truncDemand_closed_nonempty (hu t) c (mt t) hc0 (hmt0 t)
  have hDbox : ∀ t q, D t q ⊆ Icc 0 (fun _ => c) := fun _ _ _ h => h.1.1
  have hDgraph : ∀ t, IsClosed (graph (D t)) := fun t =>
    (hDp t).1.preimage (f := fun r : (ι → ℝ) × (ι → ℝ) => ((r.1, cost r.1 (ω t)), r.2))
      (by unfold cost; fun_prop)
  have hGc : ∀ t, IsClosed (graph fun q => convexHull ℝ (D t q)) := fun t =>
    isClosed_graph_convexHull isCompact_Icc (hDbox t) (hDgraph t)
  -- Kakutani
  set Δ := priceSimplex ι with hΔ
  set zf : (T → ι → ℝ) → ι → ℝ := fun x => ∑ t, mass t • x t - S with hzf
  have hzc : Continuous zf := by
    simp only [hzf]
    fun_prop
  set s : Set ((ι → ℝ) × (T → ι → ℝ)) := Δ ×ˢ Icc (0 : T → ι → ℝ) (fun _ _ => c) with hs
  set φ : (ι → ℝ) × (T → ι → ℝ) → Set ((ι → ℝ) × (T → ι → ℝ)) := fun v =>
    {v' | (v'.1 ∈ Δ ∧ ∀ r ∈ Δ, cost r (zf v.2) ≤ cost v'.1 (zf v.2)) ∧
      ∀ t, v'.2 t ∈ convexHull ℝ (D t v.1)} with hφ
  have hconv : Convex ℝ s := convex_priceSimplex.prod (convex_Icc _ _)
  have hcomp : IsCompact s := isCompact_priceSimplex.prod isCompact_Icc
  obtain ⟨p0, hp0⟩ := priceSimplex_nonempty (ι := ι)
  have hsne : s.Nonempty := ⟨(p0, 0), hp0, ⟨le_rfl, fun _ _ => hc0⟩⟩
  have hmaps : ∀ v ∈ s, φ v ⊆ s := by
    rintro v - v' ⟨⟨hΔ', -⟩, hx⟩
    exact ⟨hΔ', fun t => (convexHull_min (hDbox t v.1) (convex_Icc _ _) (hx t)).1,
      fun t => (convexHull_min (hDbox t v.1) (convex_Icc _ _) (hx t)).2⟩
  have hφne : ∀ v ∈ s, (φ v).Nonempty := by
    intro v _
    obtain ⟨p', hp', hmax⟩ := isCompact_priceSimplex.exists_isMaxOn (priceSimplex_nonempty (ι := ι))
      (show Continuous fun q : ι → ℝ => cost q (zf v.2) by unfold cost; fun_prop).continuousOn
    exact ⟨(p', fun t => ((hDp t).2 (v.1, cost v.1 (ω t))).some),
      ⟨hp', fun r hr => hmax hr⟩, fun t => subset_convexHull ℝ _ ((hDp t).2 _).some_mem⟩
  have hφconv : ∀ v ∈ s, Convex ℝ (φ v) := by
    intro v _
    rintro ⟨a1, a2⟩ ⟨⟨ha1, ha1m⟩, ha2⟩ ⟨b1, b2⟩ ⟨⟨hb1, hb1m⟩, hb2⟩ α β hα hβ hαβ
    refine ⟨⟨?_, fun r hr => ?_⟩, fun t => ?_⟩
    · exact convex_priceSimplex ha1 hb1 hα hβ hαβ
    · show cost r (zf v.2) ≤ cost (α • a1 + β • b1) (zf v.2)
      rw [cost_add_left, cost_smul_left, cost_smul_left]
      have h1 := ha1m r hr
      have h2 := hb1m r hr
      have hr' : α * cost r (zf v.2) + β * cost r (zf v.2) = cost r (zf v.2) := by
        rw [← add_mul, hαβ, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 hα, mul_le_mul_of_nonneg_left h2 hβ]
    · exact (convex_convexHull ℝ _) (ha2 t) (hb2 t) hα hβ hαβ
  have hgraph : IsClosed {q : ((ι → ℝ) × (T → ι → ℝ)) × ((ι → ℝ) × (T → ι → ℝ)) |
      q.1 ∈ s ∧ q.2 ∈ φ q.1} := by
    have heq : {q : ((ι → ℝ) × (T → ι → ℝ)) × ((ι → ℝ) × (T → ι → ℝ)) | q.1 ∈ s ∧ q.2 ∈ φ q.1} =
        {q | q.1 ∈ s} ∩ ({q | q.2.1 ∈ Δ} ∩ ((⋂ r ∈ Δ, {q | cost r (zf q.1.2) ≤ cost q.2.1 (zf q.1.2)}) ∩
          ⋂ t, {q | q.2.2 t ∈ convexHull ℝ (D t q.1.1)})) := by
      ext q
      simp only [hφ, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      tauto
    rw [heq]
    have hcost : Continuous fun z : (ι → ℝ) × (ι → ℝ) => cost z.1 z.2 := by
      unfold cost; fun_prop
    refine (hcomp.isClosed.preimage continuous_fst).inter
      ((isCompact_priceSimplex.isClosed.preimage (continuous_fst.comp continuous_snd)).inter
        ((isClosed_biInter fun r _ => isClosed_le ?_ ?_).inter
          (isClosed_iInter fun t => (hGc t).preimage (f := fun q :
            ((ι → ℝ) × (T → ι → ℝ)) × ((ι → ℝ) × (T → ι → ℝ)) => (q.1.1, q.2.2 t)) ?_)))
    · exact (continuous_cost r).comp (hzc.comp (continuous_snd.comp continuous_fst))
    · exact hcost.comp ((continuous_fst.comp continuous_snd).prodMk
        (hzc.comp (continuous_snd.comp continuous_fst)))
    · exact (continuous_fst.comp continuous_fst).prodMk
        ((continuous_apply t).comp (continuous_snd.comp continuous_snd))
  obtain ⟨⟨p, x⟩, ⟨hpΔ, hxbox⟩, ⟨⟨-, hpmax⟩, hxD⟩⟩ :=
    kakutani_fixedPoint hconv hcomp hsne hmaps hφne hφconv hgraph
  -- consequences of the fixed point
  have hx0 : ∀ t, 0 ≤ x t := fun t => hxbox.1 t
  have hwge : ∀ t, mt t ≤ cost p (ω t) := fun t => by
    calc mt t = ∑ i, p i * mt t := by rw [← Finset.sum_mul, hpΔ.2, one_mul]
      _ ≤ ∑ i, p i * ω t i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmtle t i) (hpΔ.1 i)
  have hmaxeq : ∀ t, max (cost p (ω t)) (mt t) = cost p (ω t) := fun t => max_eq_left (hwge t)
  have hbud : ∀ t, cost p (x t) ≤ cost p (ω t) := fun t =>
    convexHull_min (fun d hd => by
      have h := hd.1.2
      simp only at h
      rw [hmaxeq] at h
      exact h) (convex_cost_le p _) (hxD t)
  have hcz : cost p (zf x) = ∑ t, mass t * cost p (x t) - ∑ t, mass t * cost p (ω t) := by
    simp only [hzf, hS, cost_sub_right, cost_sum, cost_smul_right]
  have hz : cost p (zf x) ≤ 0 := by
    rw [hcz, sub_nonpos]
    exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hbud t) (hmass t).le
  have hzle : ∀ i, zf x i ≤ 0 := by
    intro i
    have hei : (Pi.single i 1 : ι → ℝ) ∈ Δ := by
      refine ⟨fun j => ?_, ?_⟩
      · by_cases h : j = i
        · subst h; simp
        · simp [h]
      · simp
    have h := hpmax _ hei
    have : cost (Pi.single i 1) (zf x) = zf x i := by simp [cost, Pi.single_apply]
    linarith
  have hSle : ∑ t, mass t • x t ≤ S := fun i => by
    have := hzle i
    simp only [hzf, Pi.sub_apply] at this
    linarith
  have hsumB : ∑ j, x t₀ j ≤ B := by
    have h1 : mass t₀ • x t₀ ≤ ∑ t, mass t • x t :=
      Finset.single_le_sum (f := fun t => mass t • x t)
        (fun t _ => smul_nonneg (hmass t).le (hx0 t)) (mem_univ t₀)
    have h2 : mass t₀ * ∑ j, x t₀ j ≤ ∑ i, S i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        have := (h1.trans hSle) j
        simpa using this
    rw [hB, le_div_iff₀ (hmass t₀)]
    linarith
  have hpU : p ∉ U := by
    intro hpU
    have hall := hpU c hcB
    have hconvx : x t₀ ∈ {v : ι → ℝ | B < cost (fun _ => 1) v} :=
      convexHull_min (fun d hd => by
        show B < cost (fun _ => 1) d
        rw [← sum_eq_cost_one]
        exact hall d hd) (convex_lt_cost _ B) (hxD t₀)
    have : B < ∑ j, x t₀ j := by rw [sum_eq_cost_one]; exact hconvx
    linarith
  have hπp : ∀ i, π ≤ p i := hπ p hpΔ hpU
  have hpos : PositivePrices p := fun i => lt_of_lt_of_le hπ0 (hπp i)
  -- the truncation does not bind
  have hDdem : ∀ t, D t p ⊆ demand (prefOf (u t)) p (cost p (ω t)) := by
    intro t d hd
    have hd2 := hd.1.2
    simp only at hd2
    rw [hmaxeq] at hd2
    refine ⟨⟨hd.1.1.1, hd2⟩, fun y hy => hd.2 y ⟨⟨hy.1, fun j => ?_⟩, ?_⟩⟩
    · have h1 : p j * y j ≤ cost p y :=
        Finset.single_le_sum (f := fun k => p k * y k)
          (fun k _ => mul_nonneg (hpΔ.1 k) (hy.1 k)) (mem_univ j)
      have h2 : cost p (ω t) ≤ ∑ i, ω t i :=
        Finset.sum_le_sum fun i _ => by
          have h : p i ≤ 1 := le_one_of_mem_priceSimplex hpΔ i
          exact mul_le_of_le_one_left (hω0 t i) h
      have h3 : ∑ i, ω t i ≤ Wb :=
        Finset.single_le_sum (f := fun t => ∑ i, ω t i)
          (fun t _ => Finset.sum_nonneg fun i _ => hω0 t i) (mem_univ t)
      have h4 : π * y j ≤ Wb := by
        have := mul_le_mul_of_nonneg_right (hπp j) (hy.1 j)
        linarith [hy.2]
      have h5 : y j ≤ Wb / π := by rw [le_div_iff₀ hπ0]; linarith
      show y j ≤ c
      linarith
    · show cost p y ≤ max (cost p (ω t)) (mt t)
      rw [hmaxeq]; exact hy.2
  -- budgets bind
  have hxeq : ∀ t, cost p (x t) = cost p (ω t) := by
    intro t
    refine le_antisymm (hbud t) ?_
    have : x t ∈ {y : ι → ℝ | cost p (ω t) ≤ cost p y} :=
      convexHull_min (fun d hd => by
        show cost p (ω t) ≤ cost p d
        exact (walras_law (hmono t).locallyNonsatiated (hDdem t hd)).ge) (convex_le_cost p _)
        (hxD t)
    exact this
  have hz0 : cost p (zf x) = 0 := by
    rw [hcz, sub_eq_zero]
    exact Finset.sum_congr rfl fun t _ => by rw [hxeq t]
  have hzero : zf x = 0 := by
    have hterms := (Finset.sum_eq_zero_iff_of_nonpos (s := univ)
      (f := fun i => p i * zf x i)
      (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hpos i).le (hzle i))).1 hz0
    funext i
    have := hterms i (mem_univ i)
    exact (mul_eq_zero.1 this).resolve_left (hpos i).ne'
  refine ⟨p, x, hpos, fun t => convexHull_mono (hDdem t) (hxD t), ?_⟩
  have := hzero
  simp only [hzf] at this
  exact sub_eq_zero.1 this

end AumannExistence

namespace Continuum
namespace ContinuumEconomy

open MeasureTheory Set Filter

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

/-- **Existence of equilibrium without convex preferences** (Aumann 1966, for
finitely many types). Let the traders form a finite nonatomic measure space,
partitioned by a measurable type map `τ` into finitely many types of positive
mass; type `t` has a continuous, strongly monotone utility `uₜ` (**not**
assumed quasiconcave) and endowment `ωₜ ≫ 0`. Then a Walrasian equilibrium
exists, at strictly positive prices.

Proof: `exists_convexifiedEquilibrium` gives prices and mean bundles in the
convex hulls of the types' demands that clear the market; the convexification
bridge splits each type into groups consuming demanded bundles (Lyapunov). -/
theorem exists_isWalrasianEquilibrium_of_types_nonconvex [Nonempty ι] [IsFiniteMeasure E.μ]
    (hμ : Lyapunov.Nonatomic E.μ) {T : Type*} [Fintype T] [Nonempty T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {τ : Ω → T} (hτ : Measurable τ)
    {u : T → (ι → ℝ) → ℝ} {ω : T → ι → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u (τ a))) (hω : ∀ a, E.endow a = ω (τ a))
    (hmass : ∀ t, 0 < E.μ.real (τ ⁻¹' {t}))
    (hu : ∀ t, Continuous (u t)) (hmono : ∀ t, StronglyMonotone (prefOf (u t)))
    (hωpos : ∀ t, PositivePrices (ω t)) :
    ∃ (p : ι → ℝ) (x : Ω → ι → ℝ), PositivePrices p ∧ E.IsWalrasianEquilibrium p x := by
  classical
  obtain ⟨p, xbar, hp, hx, hclear⟩ :=
    AumannExistence.exists_convexifiedEquilibrium (fun t => E.μ.real (τ ⁻¹' {t})) hmass hu hmono
      hωpos
  obtain ⟨x, hxeq⟩ := E.exists_allocation_isWalrasianEquilibrium_of_mem_convexHull hμ τ hτ
    (fun t => prefOf (u t)) ω hpref hω p xbar hx hclear
  exact ⟨p, x, hp, hxeq⟩

/-! ### Witness: a non-convex economy with only asymmetric equilibria

One type of traders, uniform on `[0, 1]`, endowment `(1, 1)` and the utility
`x₀² + x₁²`, which is continuous and strongly monotone on `ℝ²₊` but **not**
quasiconcave (preferences are not convex): `(2, 0)` and `(0, 2)` are each
better than their midpoint `(1, 1)`. The theorem gives an equilibrium at
positive prices; no trader ever demands `(1, 1)`, so in every such
equilibrium identical traders consume different bundles. -/

/-- The utility `x₀² + x₁²`. -/
def uSq (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- One type, endowment `(1, 1)`, utility `x₀² + x₁²`. -/
noncomputable def sqContinuum : ContinuumEconomy ℝ (Fin 2) where
  μ := volume.restrict (Icc (0 : ℝ) 1)
  pref _ := prefOf uSq
  endow _ := one2
  endow_nonneg _ _ := zero_le_one
  endow_integrable := integrable_const _

instance : IsFiniteMeasure sqContinuum.μ := by unfold sqContinuum; infer_instance

theorem continuous_uSq : Continuous uSq := by unfold uSq; fun_prop

theorem stronglyMonotone_uSq : StronglyMonotone (prefOf uSq) := by
  intro x y hx hxy hne
  have hle : ∀ i, x i ^ 2 ≤ y i ^ 2 := fun i =>
    pow_le_pow_left₀ (hx i) (hxy i) 2
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hlt : x i ^ 2 < y i ^ 2 :=
    pow_lt_pow_left₀ (lt_of_le_of_ne (hxy i) hi) (hx i) two_ne_zero
  have hsum : uSq x < uSq y := by
    simp only [uSq]
    fin_cases i
    · have := hle 1; simp at hlt; linarith
    · have := hle 0; simp at hlt; linarith
  exact ⟨hsum.le, not_le.2 hsum⟩

/-- Preferences are **not convex**: `x₀² + x₁²` is not quasiconcave on `ℝ²₊`. -/
theorem not_quasiconcaveOn_uSq : ¬ QuasiconcaveOn ℝ (Ici 0) uSq := by
  intro h
  have h2 := h (uSq ![2, 0]) (x := ![2, 0]) (y := ![0, 2])
    ⟨fun i => by fin_cases i <;> simp, le_rfl⟩
    ⟨fun i => by fin_cases i <;> simp, by simp [uSq]⟩ (a := 1/2) (b := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := h2.2
  simp [uSq] at h3
  norm_num at h3

/-- **No trader demands `(1, 1)`** at any positive prices: spending all wealth
on the cheaper good gives utility at least `4 > 2`. -/
theorem sqContinuum_one2_not_demanded {p : Fin 2 → ℝ} (hp : PositivePrices p) :
    one2 ∉ demand (prefOf uSq) p (cost p one2) := by
  rintro ⟨-, hopt⟩
  have hw : cost p one2 = p 0 + p 1 := by simp [cost, one2, Fin.sum_univ_two]
  have h0 := hp 0; have h1 := hp 1
  have hu1 : uSq one2 = 2 := by norm_num [uSq, one2]
  rcases le_total (p 0) (p 1) with hle | hle
  · set y : Fin 2 → ℝ := ![(p 0 + p 1) / p 0, 0]
    have hy : y ∈ budgetSet p (cost p one2) := by
      refine ⟨fun i => ?_, ?_⟩
      · fin_cases i
        · show (0:ℝ) ≤ (p 0 + p 1) / p 0
          positivity
        · simp [y]
      · rw [hw]; simp [y, cost, Fin.sum_univ_two]; field_simp; rfl
    have := hopt y hy
    change uSq y ≤ uSq one2 at this
    rw [hu1] at this
    simp only [uSq, y, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    have hge : 2 ≤ (p 0 + p 1) / p 0 := by rw [le_div_iff₀ h0]; linarith
    nlinarith
  · set y : Fin 2 → ℝ := ![0, (p 0 + p 1) / p 1]
    have hy : y ∈ budgetSet p (cost p one2) := by
      refine ⟨fun i => ?_, ?_⟩
      · fin_cases i
        · simp [y]
        · show (0:ℝ) ≤ (p 0 + p 1) / p 1
          positivity
      · rw [hw]; simp [y, cost, Fin.sum_univ_two]; field_simp; rfl
    have := hopt y hy
    change uSq y ≤ uSq one2 at this
    rw [hu1] at this
    simp only [uSq, y, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    have hge : 2 ≤ (p 0 + p 1) / p 1 := by rw [le_div_iff₀ h1]; linarith
    nlinarith

/-- Hence **no equilibrium at positive prices gives (almost) all traders the
same bundle**. -/
theorem sqContinuum_no_symmetric_equilibrium {p : Fin 2 → ℝ} (hp : PositivePrices p)
    (c : Fin 2 → ℝ) {x : ℝ → Fin 2 → ℝ} (hx : x =ᵐ[sqContinuum.μ] fun _ => c) :
    ¬ sqContinuum.IsWalrasianEquilibrium p x := by
  rintro ⟨⟨-, -, hint⟩, hdem⟩
  have hvol : sqContinuum.μ.real univ = 1 := by
    show (volume.restrict (Icc (0:ℝ) 1)).real univ = 1
    simp [Real.volume_real_Icc]
  have hc : c = one2 := by
    have h := hint
    have he : (∫ a, sqContinuum.endow a ∂sqContinuum.μ) = one2 := by
      show ∫ _, one2 ∂sqContinuum.μ = one2
      rw [integral_const, hvol, one_smul]
    rw [integral_congr_ae hx, integral_const, hvol, one_smul, he] at h
    exact h
  subst hc
  have hne : (ae sqContinuum.μ).NeBot := by
    rw [ae_neBot]
    intro h0
    have := congrArg (fun μ => μ.real univ) h0
    simp only [hvol] at this
    simp at this
  obtain ⟨a, ha, hxa⟩ := (hdem.and hx).exists
  rw [hxa] at ha
  exact sqContinuum_one2_not_demanded hp ha

/-- **The non-convex economy has an equilibrium** at positive prices (by the
theorem; necessarily one in which identical traders consume different bundles). -/
theorem sqContinuum_exists_equilibrium :
    ∃ (p : Fin 2 → ℝ) (x : ℝ → Fin 2 → ℝ), PositivePrices p ∧
      sqContinuum.IsWalrasianEquilibrium p x :=
  sqContinuum.exists_isWalrasianEquilibrium_of_types_nonconvex
    (T := Fin 1) (τ := fun _ => 0) Lyapunov.nonatomic_volume_Icc measurable_const
    (u := fun _ => uSq) (ω := fun _ => one2) (fun _ => rfl) (fun _ => rfl)
    (fun t => by
      fin_cases t
      show 0 < (volume.restrict (Icc (0:ℝ) 1)).real ((fun _ : ℝ => (0 : Fin 1)) ⁻¹' {0})
      simp [Real.volume_real_Icc])
    (fun _ => continuous_uSq) (fun _ => stronglyMonotone_uSq)
    (fun _ _ => by simp [one2])

/-- There is an equilibrium at positive prices whose allocation is not a.e.
constant; by `sqContinuum_no_symmetric_equilibrium`, every equilibrium at positive
prices is of this kind. -/
theorem sqContinuum_exists_asymmetric_equilibrium :
    ∃ (p : Fin 2 → ℝ) (x : ℝ → Fin 2 → ℝ), PositivePrices p ∧
      sqContinuum.IsWalrasianEquilibrium p x ∧ ∀ c : Fin 2 → ℝ, ¬ x =ᵐ[sqContinuum.μ] fun _ => c := by
  obtain ⟨p, x, hp, hx⟩ := sqContinuum_exists_equilibrium
  exact ⟨p, x, hp, hx, fun c hc => sqContinuum_no_symmetric_equilibrium hp c hc hx⟩

end ContinuumEconomy
end Continuum

end Econ
