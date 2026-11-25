/-
# Existence of Walrasian equilibrium with unbounded production sets

PLAN.md §1 (M4). Arrow & Debreu (1954), Assumption I (a)–(c) on production;
Debreu (1959) ch. 5 (boundedness of attainable states); MWG §17.B and
Appendix 17.BB.

`GE/ExistenceProduction.lean` proves existence when each production set `Yⱼ` is
compact. Here `Yⱼ` may be **unbounded**: each `Yⱼ` is closed and strictly
convex with `0 ∈ Yⱼ`, and the aggregate production set `Y = ∑ⱼ Yⱼ` satisfies
the canonical Arrow–Debreu conditions

* no free lunch, `Y ∩ ℝᴸ₊ ⊆ {0}` (`NoFreeLunch`), and
* irreversibility, `Y ∩ (−Y) ⊆ {0}` (`Irreversible`).

Proof.
1. **Attainable production is bounded** (`exists_bound_attainable`): if
   `yⁿ ∈ ∏ⱼ Yⱼ` with `∑ⱼ yⁿⱼ ≥ −ω̄` and `‖yⁿ‖ → ∞`, a limit point `d` of
   `yⁿ / ‖yⁿ‖` has `dⱼ ∈ Yⱼ` (convexity, `0 ∈ Yⱼ`, closedness), `∑ⱼ dⱼ ≥ 0`,
   hence `∑ⱼ dⱼ = 0` (no free lunch) and every `dⱼ = 0` (irreversibility),
   contradicting `‖d‖ = 1`. Only the canonical cone argument's first step is
   needed, since convexity with `0 ∈ Yⱼ` puts the normalized points in `Yⱼ`.
2. **Truncate** each `Yⱼ` to `Yⱼ ∩ {z | ∑ᵢ zᵢ² ≤ ρ}`, a Euclidean ball whose
   interior contains each firm's component `yⱼ` of every attainable plan. The truncated sets are
   compact and strictly convex, so profit maximizers are unique
   (`profitMax_trunc_subsingleton`), and the compact theorem gives an
   equilibrium of the truncated economy.
3. **Lift back**: equilibrium production is attainable, so it lies in the
   interior of the ball; a profitable plan in `Yⱼ` would give, by convexity, a
   profitable plan in the truncated set nearby.

Scope. Strict convexity of each `Yⱼ` (used for single-valued supply) is much
stronger than Arrow–Debreu's convexity: in Mathlib it forces each `Yⱼ ≠ {0}` to
have nonempty interior, so every firm must be able to vary every good's net
output, and constant returns, linear activities, flat facets and free disposal
are all excluded. Set-valued supply (Kakutani) is handled in
`GE/ExistenceArrowDebreu.lean`, at the cost of strictly positive endowments. Consumers have
consumption set `ℝᴸ₊` and single-valued demand (`RegularUtility`); individual
endowments may be zero.

This theorem and the compact one are not nested: this one drops compactness of
`Yⱼ` but adds strict convexity and the aggregate no-free-lunch and
irreversibility conditions, which the compact theorem does not need.

Witness: `parabolaEconomy`, one firm (so the aggregate conditions are the
firm's own; a multi-firm witness is open) with the unbounded production set
`{y | y₁ ≤ −y₀ − y₀²}` (`not_isBounded_parabolaSet`).
-/
module

public import EconLean.GE.ExistenceProduction
public import EconLean.Producer.Production

@[expose] public section

namespace Econ

open Filter Topology Set Finset

namespace ProductionEconomy

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-- The **aggregate production set** `Y = ∑ⱼ Yⱼ`. -/
def aggProd (E : ProductionEconomy α β ι) : Set (ι → ℝ) :=
  {z | ∃ y : β → ι → ℝ, (∀ j, y j ∈ E.prod j) ∧ ∑ j, y j = z}

omit [Fintype ι] in
/-- With inaction possible, no free lunch and irreversibility of the aggregate
production set, production plans with nonnegative aggregate net output are all
zero. -/
theorem eq_zero_of_sum_nonneg (E : ProductionEconomy α β ι)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) {y : β → ι → ℝ} (hy : ∀ j, y j ∈ E.prod j)
    (h0 : 0 ≤ ∑ j, y j) : y = 0 := by
  classical
  have hsum : ∑ j, y j = 0 := hnfl _ ⟨y, hy, rfl⟩ h0
  funext k
  set s : β → ι → ℝ := fun j => if j = k then y k else 0
  set r : β → ι → ℝ := fun j => if j = k then 0 else y j
  have hs : ∑ j, s j = y k := by simp [s]
  have hsr : ∑ j, r j + y k = 0 := by
    rw [← hs, ← sum_add_distrib, ← hsum]
    refine sum_congr rfl fun j _ => ?_
    simp only [r, s]; split_ifs with h <;> simp [h]
  have hr : ∑ j, r j = -y k := eq_neg_of_add_eq_zero_left hsr
  apply hirr
  · refine ⟨s, fun j => ?_, hs⟩
    simp only [s]; split_ifs with h
    · exact h ▸ hy k
    · exact hY0 j
  · refine ⟨r, fun j => ?_, hr⟩
    simp only [r]; split_ifs
    · exact hY0 j
    · exact hy j

/-- **Attainable production is bounded** (Debreu 1959 ch. 5, attainable states):
for closed convex `Yⱼ ∋ 0` with no free lunch and irreversibility, the plans
`y ∈ ∏ⱼ Yⱼ` with `∑ⱼ yⱼ ≥ c` form a bounded set, for every `c`. -/
theorem exists_bound_attainable (E : ProductionEconomy α β ι)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) (c : ι → ℝ) :
    ∃ R, ∀ y : β → ι → ℝ, (∀ j, y j ∈ E.prod j) → c ≤ ∑ j, y j → ‖y‖ ≤ R := by
  by_contra hcon
  push Not at hcon
  choose yn hyn hcn hRn using fun n : ℕ => hcon ((n : ℝ) + 1)
  have hs1 : ∀ n, 1 ≤ ‖yn n‖ := fun n => by
    have := hRn n; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  set dn : ℕ → β → ι → ℝ := fun n => ‖yn n‖⁻¹ • yn n with hdn_def
  have hdn : ∀ n, ‖dn n‖ = 1 := fun n => by
    have := (zero_lt_one.trans_le (hs1 n)).ne'
    simp only [dn, norm_smul, norm_inv, norm_norm]
    field_simp
  obtain ⟨d, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : β → ι → ℝ) 1).tendsto_subseq
    (x := dn) fun n => by simp [hdn]
  have hdnorm : ‖d‖ = 1 := by
    have h1 := (continuous_norm.tendsto d).comp hlim
    have h2 : Tendsto (fun n => ‖dn (φ n)‖) atTop (𝓝 1) := by simp [hdn]
    exact tendsto_nhds_unique h1 h2
  have hmem : ∀ j, d j ∈ E.prod j := by
    intro j
    refine (hYcl j).mem_of_tendsto (((continuous_apply j).tendsto d).comp hlim)
      (Eventually.of_forall fun n => ?_)
    have := (hYcv j).smul_mem_of_zero_mem (hY0 j) (hyn (φ n) j)
      ⟨inv_nonneg.2 (norm_nonneg (yn (φ n))), inv_le_one_of_one_le₀ (hs1 (φ n))⟩
    simpa [dn] using this
  have hinv : Tendsto (fun n => ‖yn (φ n)‖⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      tendsto_natCast_atTop_atTop)
    have h1 := hRn (φ n)
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith
  have hsum : 0 ≤ ∑ j, d j := by
    intro i
    simp only [Pi.zero_apply, Finset.sum_apply]
    have hcont : Continuous fun z : β → ι → ℝ => ∑ j, z j i :=
      continuous_finsetSum _ fun j _ => (continuous_apply i).comp (continuous_apply j)
    have hlim_i := (hcont.tendsto d).comp hlim
    have hlow : Tendsto (fun n => ‖yn (φ n)‖⁻¹ * c i) atTop (𝓝 0) := by
      simpa using hinv.mul_const (c i)
    refine le_of_tendsto_of_tendsto hlow hlim_i (Eventually.of_forall fun n => ?_)
    have hc := hcn (φ n) i
    simp only [Finset.sum_apply] at hc
    simp only [Function.comp_apply, dn, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hc (inv_nonneg.2 (norm_nonneg _))
  have hd0 := E.eq_zero_of_sum_nonneg hY0 hnfl hirr hmem hsum
  rw [hd0, norm_zero] at hdnorm
  exact zero_ne_one hdnorm

/-- The Euclidean truncation set `{z | ∑ᵢ zᵢ² ≤ ρ}`. -/
def truncSet (ρ : ℝ) : Set (ι → ℝ) := {z | ∑ i, z i ^ 2 ≤ ρ}

theorem isClosed_truncSet (ρ : ℝ) : IsClosed (truncSet (ι := ι) ρ) :=
  isClosed_le (by fun_prop) continuous_const

theorem isBounded_truncSet (ρ : ℝ) : Bornology.IsBounded (truncSet (ι := ι) ρ) := by
  refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := |ρ| + 1)).subset
    fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hi : z i ^ 2 ≤ ρ :=
    (single_le_sum (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) (mem_univ i)).trans hz
  rw [Real.norm_eq_abs]
  have := le_abs_self ρ
  exact abs_le.2 ⟨by nlinarith [sq_nonneg (z i + 1)], by nlinarith [sq_nonneg (z i - 1)]⟩

/-- **Unique profit maximizers on a truncated strictly convex set**: the
midpoint of two distinct maximizers lies in the interior of `Y` and strictly
inside the ball, so moving from it in the direction `p` raises profit. -/
theorem profitMax_trunc_subsingleton [Nonempty ι] {Y : Set (ι → ℝ)}
    (hY : StrictConvex ℝ Y) (ρ : ℝ) {p : ι → ℝ} (hp : PositivePrices p) :
    {y | ProfitMax p (Y ∩ truncSet ρ) y}.Subsingleton := by
  intro y₁ h₁ y₂ h₂
  by_contra hne
  set m : ι → ℝ := (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ with hm
  have hmY : m ∈ interior Y := hY h₁.1.1 h₂.1.1 hne (by norm_num) (by norm_num) (by norm_num)
  have key : ∀ i, m i ^ 2 + (y₁ i - y₂ i) ^ 2 / 4 = (y₁ i ^ 2 + y₂ i ^ 2) / 2 := fun i => by
    simp only [m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hsumk : ∑ i, m i ^ 2 + ∑ i, (y₁ i - y₂ i) ^ 2 / 4 =
      (∑ i, y₁ i ^ 2 + ∑ i, y₂ i ^ 2) / 2 := by
    rw [← sum_add_distrib, sum_congr rfl fun i _ => key i, ← sum_div, sum_add_distrib]
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  have hpos : 0 < ∑ i, (y₁ i - y₂ i) ^ 2 / 4 := by
    refine sum_pos' (fun i _ => by positivity) ⟨k, mem_univ k, ?_⟩
    have : y₁ k - y₂ k ≠ 0 := sub_ne_zero.2 hk
    positivity
  have h1 : ∑ i, y₁ i ^ 2 ≤ ρ := h₁.1.2
  have h2 : ∑ i, y₂ i ^ 2 ≤ ρ := h₂.1.2
  have hmK : ∑ i, m i ^ 2 < ρ := by linarith
  set U := interior Y ∩ {z : ι → ℝ | ∑ i, z i ^ 2 < ρ}
  have hU : IsOpen U := isOpen_interior.inter (isOpen_lt (by fun_prop) continuous_const)
  have hUsub : U ⊆ Y ∩ truncSet ρ := fun z hz => ⟨interior_subset hz.1, by
    simp only [truncSet, mem_ofPred_eq]; exact hz.2.le⟩
  have hpath : Tendsto (fun t : ℝ => m + t • p) (𝓝[>] 0) (𝓝 m) := by
    have : Continuous fun t : ℝ => m + t • p := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, htU, ht⟩ := ((hpath.eventually (hU.mem_nhds ⟨hmY, hmK⟩)).and
    self_mem_nhdsWithin).exists
  have hcm : cost p m = (cost p y₁ + cost p y₂) / 2 := by
    simp only [m, cost_add_right, cost_smul_right]; ring
  have hle₁ := h₁.2 y₂ h₂.1
  have hle₂ := h₂.2 y₁ h₁.1
  have hpp : 0 < cost p p := by
    unfold cost
    exact sum_pos (fun i _ => mul_pos (hp i) (hp i)) univ_nonempty
  have hz := h₁.2 _ (hUsub htU)
  rw [cost_add_right, cost_smul_right, hcm] at hz
  have : 0 < t * cost p p := mul_pos ht hpp
  linarith

/-- **Existence of Walrasian equilibrium with unbounded production sets**
(Arrow–Debreu 1954 with strictly convex technologies and single-valued demand,
`RegularUtility`): regular utilities, a
strictly positive aggregate endowment, and closed, strictly convex production
sets `Yⱼ ∋ 0` whose sum satisfies no free lunch and irreversibility. No
boundedness of production sets is assumed, and none on individual endowments. -/
theorem exists_walrasianEquilibrium_unbounded [Nonempty ι] (E : ProductionEconomy α β ι)
    {u : α → (ι → ℝ) → ℝ} (hpref : ∀ a, E.pref a = prefOf (u a))
    (hreg : ∀ a, RegularUtility (u a)) (hω : PositivePrices E.totalEndowment)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYsc : ∀ j, StrictConvex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y := by
  obtain ⟨R, hR⟩ := E.exists_bound_attainable hY0 hYcl (fun j => (hYsc j).convex) hnfl hirr
    (-E.totalEndowment)
  set ρ : ℝ := Fintype.card ι * R ^ 2 + 1 with hρ
  let E' : ProductionEconomy α β ι :=
    { E with prod := fun j => E.prod j ∩ truncSet ρ }
  have h0ρ : (0 : ι → ℝ) ∈ truncSet ρ := by
    simp only [truncSet, mem_ofPred_eq, Pi.zero_apply]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, hρ]
    positivity
  obtain ⟨p, x, y, hp, hprof, hdem, hclear⟩ :=
    E'.exists_walrasianEquilibrium_production_of_unique (u := u) hpref hreg hω
      (fun j => ⟨hY0 j, h0ρ⟩)
      (fun j => Metric.isCompact_of_isClosed_isBounded ((hYcl j).inter (isClosed_truncSet ρ))
        ((isBounded_truncSet ρ).subset inter_subset_right))
      (fun j _ hq => profitMax_trunc_subsingleton (hYsc j) ρ hq)
  have hyY : ∀ j, y j ∈ E.prod j := fun j => (hprof j).1.1
  have hx0 : ∀ a, 0 ≤ x a := fun a => (hdem a).1.1
  have hatt : -E.totalEndowment ≤ ∑ j, y j := by
    have : 0 ≤ ∑ a, x a := sum_nonneg fun a _ => hx0 a
    have hc : ∑ a, x a = E.totalEndowment + ∑ j, y j := hclear
    rw [hc] at this
    intro i; have := this i
    simp only [Pi.zero_apply, Pi.add_apply] at this
    simp only [Pi.neg_apply]; linarith
  have hyR := hR y hyY hatt
  have hin : ∀ j, ∑ i, y j i ^ 2 < ρ := by
    intro j
    have hcoord : ∀ i, y j i ^ 2 ≤ R ^ 2 := fun i => by
      have h := (norm_le_pi_norm (y j) i).trans ((norm_le_pi_norm y j).trans hyR)
      rw [Real.norm_eq_abs] at h
      have h0 : 0 ≤ |y j i| := abs_nonneg _
      calc y j i ^ 2 = |y j i| ^ 2 := (sq_abs _).symm
        _ ≤ R ^ 2 := pow_le_pow_left₀ h0 h 2
    calc ∑ i, y j i ^ 2 ≤ ∑ _i : ι, R ^ 2 := sum_le_sum fun i _ => hcoord i
      _ = Fintype.card ι * R ^ 2 := by simp
      _ < ρ := by rw [hρ]; linarith
  refine ⟨p, x, y, hp, fun j => ⟨hyY j, fun z hz => ?_⟩, hdem, hclear⟩
  by_contra hlt
  push Not at hlt
  have hpath : Tendsto (fun t : ℝ => y j + t • (z - y j)) (𝓝[>] 0) (𝓝 (y j)) := by
    have : Continuous fun t : ℝ => y j + t • (z - y j) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hopen : IsOpen {w : ι → ℝ | ∑ i, w i ^ 2 < ρ} := isOpen_lt (by fun_prop) continuous_const
  have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
  obtain ⟨t, ⟨htK, ht1⟩, ht0⟩ := (((hpath.eventually (hopen.mem_nhds (hin j))).and hlt1).and
    self_mem_nhdsWithin).exists
  have ht0' : (0 : ℝ) < t := ht0
  have hw : y j + t • (z - y j) ∈ E'.prod j :=
    ⟨(hYsc j).convex.add_smul_sub_mem (hyY j) hz ⟨ht0'.le, ht1.le⟩, le_of_lt htK⟩
  have := (hprof j).2 _ hw
  rw [cost_add_right, cost_smul_right, cost_sub_right] at this
  have : 0 < t * (cost p z - cost p (y j)) := mul_pos ht0' (by linarith)
  linarith

end ProductionEconomy

namespace GEExamples

/-- An **unbounded** strictly convex production set: `y₁ ≤ −y₀ − y₀²`. Using
`a = −y₀ ∈ [0, 1]` units of good 0 yields up to `a − a²` units of good 1 (for
`a > 1` good 1 is an input too); using good 1 yields good 0 at increasing
marginal cost. -/
def parabolaSet : Set (Fin 2 → ℝ) := {y | y 1 ≤ -y 0 - y 0 ^ 2}

theorem zero_mem_parabolaSet : (0 : Fin 2 → ℝ) ∈ parabolaSet := by
  simp [parabolaSet]

theorem isClosed_parabolaSet : IsClosed parabolaSet :=
  isClosed_le (continuous_apply 1) (by fun_prop)

theorem strictConvex_parabolaSet : StrictConvex ℝ parabolaSet := by
  intro x hx y hy hxy a b ha hb hab
  have hopen : IsOpen {z : Fin 2 → ℝ | z 1 < -z 0 - z 0 ^ 2} :=
    isOpen_lt (continuous_apply 1) (by fun_prop)
  refine interior_maximal (fun z hz => by
    simp only [parabolaSet, mem_ofPred_eq] at hz ⊢; exact hz.le) hopen ?_
  simp only [parabolaSet, mem_ofPred_eq] at hx hy
  simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  by_cases h0 : x 0 = y 0
  · have h1 : x 1 ≠ y 1 := fun h1 => hxy (funext fun i => by fin_cases i <;> simp [h0, h1])
    rw [h0] at hx ⊢
    rcases lt_or_gt_of_ne h1 with h | h
    · nlinarith
    · nlinarith
  · have : 0 < (x 0 - y 0) ^ 2 := by positivity
    nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) this]

theorem noFreeLunch_parabolaSet {y : Fin 2 → ℝ} (hy : y ∈ parabolaSet) (h0 : 0 ≤ y) :
    y = 0 := by
  simp only [parabolaSet, mem_ofPred_eq] at hy
  have a := h0 0
  have b := h0 1
  simp only [Pi.zero_apply] at a b
  have e0 : y 0 = 0 := by nlinarith
  have e1 : y 1 = 0 := by nlinarith
  funext i; fin_cases i <;> simp [e0, e1]

theorem irreversible_parabolaSet {y : Fin 2 → ℝ} (hy : y ∈ parabolaSet)
    (hny : -y ∈ parabolaSet) : y = 0 := by
  simp only [parabolaSet, mem_ofPred_eq, Pi.neg_apply] at hy hny
  have e0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0)]
  have e1 : y 1 = 0 := by rw [e0] at hy hny; linarith
  funext i; fin_cases i <;> simp [e0, e1]

/-- The parabola technology is **unbounded**, so the compact-production theorem
does not apply to it. -/
theorem not_isBounded_parabolaSet : ¬ Bornology.IsBounded parabolaSet := by
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  set t : ℝ := |C| + 1
  have hmem : (![-t, t - t ^ 2] : Fin 2 → ℝ) ∈ parabolaSet := by
    simp [parabolaSet]
  have h := (norm_le_pi_norm (![-t, t - t ^ 2] : Fin 2 → ℝ) 0).trans (hC _ hmem)
  simp only [Matrix.cons_val_zero, norm_neg, Real.norm_eq_abs] at h
  have : |t| = t := abs_of_pos (by positivity)
  have := le_abs_self C
  linarith

/-- Witness economy: two square-root consumers owning `(1, 0)` and `(0, 1)`,
consumer `0` owning the one firm, whose production set `parabolaSet` is
unbounded. -/
noncomputable def parabolaEconomy : ProductionEconomy (Fin 2) (Fin 1) (Fin 2) where
  pref _ := prefOf uSqrt
  endow a := fun k => if a = k then 1 else 0
  endow_nonneg a k := by simp only [Pi.zero_apply]; split_ifs <;> norm_num
  prod _ := parabolaSet
  share a _ := if a = 0 then 1 else 0
  share_nonneg a _ := by split_ifs <;> norm_num
  share_sum _ := by simp

theorem parabolaEconomy_aggProd : parabolaEconomy.aggProd = parabolaSet := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [parabolaEconomy] using hy 0
  · intro hz
    exact ⟨fun _ => z, fun _ => hz, by simp⟩

/-- **Existence with an unbounded technology.** (Only existence is claimed.) -/
theorem parabolaEconomy_exists_equilibrium :
    ∃ p x y, PositivePrices p ∧ parabolaEconomy.IsWalrasianEquilibrium p x y := by
  refine parabolaEconomy.exists_walrasianEquilibrium_unbounded (u := fun _ => uSqrt)
    (fun _ => rfl) (fun _ => regularUtility_of_strictlyQuasiconcave continuous_uSqrt
      strictlyQuasiconcave_uSqrt stronglyMonotone_uSqrt) (fun k => ?_)
    (fun _ => zero_mem_parabolaSet) (fun _ => isClosed_parabolaSet)
    (fun _ => strictConvex_parabolaSet) ?_ ?_
  · simp only [ExchangeEconomy.totalEndowment, parabolaEconomy, Finset.sum_apply]
    fin_cases k <;> simp
  · rw [parabolaEconomy_aggProd]; exact fun y hy h0 => noFreeLunch_parabolaSet hy h0
  · rw [parabolaEconomy_aggProd]; exact fun y hy hny => irreversible_parabolaSet hy hny

end GEExamples

end Econ
