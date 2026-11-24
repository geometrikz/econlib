/-
# Uniform commodity taxation (Atkinson–Stiglitz)

Atkinson and Stiglitz (1976), "The Design of Tax Structure: Direct versus
Indirect Taxation", JPubE; Laroque (2005), "Indirect Taxation is Superfluous
under Separability and Taxation of Labor Income", Econ. Letters;
Kaplow (2006), JPubE.

**Setting.** Goods `i` with producer prices `p > 0` and commodity taxes `t`
(consumer prices `q = p + t ≥ 0`). Preferences are **weakly separable**:
every type shares a continuous goods subutility `v`, and type `θ` choosing
the option (net income `c`, pre-tax income `y`) gets `U θ (V q c) y`, where
* `V q c = sup {v z | z ≥ 0, q · z ≤ c}` is the indirect subutility
  (`V`, over the budget set `budget`), and
* `e u = inf {p · z | z ≥ 0, v z ≥ u}` is the expenditure function at
  producer prices (`e`).
Options are indexed by `j ∈ κ` (take `κ = ℝ` to include every point of an
income-tax schedule, so that deviations to any income are covered). In the
old regime option `j` gives net income `c_j`, and `x_j` is an optimal bundle
at prices `q` (`IsOptimal`).

**Results.**
* `V_old`: `V q c_j = v x_j` (from optimality).
* `e_le`: `e(v x_j) ≤ p · x_j` (`x_j` is a candidate bundle).
* `V_e`: duality `V p (e u) = u` for `u = v x_j`, derived from continuity of
  `v`, positive producer prices, attainment of the expenditure minimum, and
  `v 0 ≤ v x_j` (the agent could buy nothing).
* `utility_eq`, `ic_iff`: replacing commodity taxes by the net-income
  schedule `c'_j = e(v x_j)` at producer prices leaves the payoff of every
  type from every option unchanged, hence every incentive constraint.
* `c'_schedule`: if `c` is a function of pre-tax income, so is `c'`: the
  replacement is an income-tax schedule.
* `revenue_ge`, `aggregate_revenue_ge`: revenue from every option, and in
  aggregate, weakly rises.
* `income_tax_dominates`: hence any allocation implemented with commodity
  taxes is weakly dominated by one with an income tax only; at an optimum,
  differentiated commodity taxes are superfluous (Atkinson–Stiglitz).

* `exists_expenditure_min`: the expenditure minimum is attained
  (compactness), so no extra regularity is assumed; `example_regime`: the
  assumptions hold with a nonzero commodity tax.

**Deviations.** Laroque's dominance form (no optimality of the original
allocation is needed).
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

noncomputable section

namespace Econ
namespace AtkinsonStiglitz

open Matrix Set

variable {ι κ Θ : Type*} [Fintype ι]

/-- The budget set at prices `q` with spending `c`. -/
def budget (q : ι → ℝ) (c : ℝ) : Set (ι → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ q ⬝ᵥ z ≤ c}

/-- Indirect subutility. (Lean's `sSup` is `0` for empty or unbounded
sets; every result below only uses `V` where the supremum is attained.) -/
def V (v : (ι → ℝ) → ℝ) (q : ι → ℝ) (c : ℝ) : ℝ := sSup (v '' budget q c)

/-- Expenditure function at prices `p`. (Lean's `sInf` of an empty set is
`0`, not `+∞`; results only use `e` at attainable utility levels.) -/
def e (v : (ι → ℝ) → ℝ) (p : ι → ℝ) (u : ℝ) : ℝ :=
  sInf ((fun z => p ⬝ᵥ z) '' {z | (∀ i, 0 ≤ z i) ∧ u ≤ v z})

/-- `x` is optimal in the budget set. -/
def IsOptimal (v : (ι → ℝ) → ℝ) (q : ι → ℝ) (c : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ budget q c ∧ ∀ z ∈ budget q c, v z ≤ v x

variable {v : (ι → ℝ) → ℝ} {p t : ι → ℝ}

theorem V_of_optimal {q : ι → ℝ} {c : ℝ} {x : ι → ℝ} (h : IsOptimal v q c x) : V v q c = v x := by
  have : IsGreatest (v '' budget q c) (v x) :=
    ⟨mem_image_of_mem v h.1, by rintro _ ⟨z, hz, rfl⟩; exact h.2 z hz⟩
  exact this.csSup_eq

theorem dot_nonneg {a z : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hz : ∀ i, 0 ≤ z i) : 0 ≤ a ⬝ᵥ z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hz i)

/-- `x` itself is a candidate in the expenditure problem. -/
theorem e_le (hp : ∀ i, 0 < p i) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : e v p (v x) ≤ p ⬝ᵥ x := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact dot_nonneg (fun i => (hp i).le) hz.1
  · exact ⟨x, ⟨hx, le_rfl⟩, rfl⟩

/-- **Duality** `V p (e u) = u`. -/
theorem V_e (hv : Continuous v) (hp : ∀ i, 0 < p i) {u : ℝ} (h0 : v 0 ≤ u)
    (hatt : ∃ z, (∀ i, 0 ≤ z i) ∧ u ≤ v z ∧ p ⬝ᵥ z = e v p u) : V v p (e v p u) = u := by
  obtain ⟨z₀, hz₀, hu₀, hc₀⟩ := hatt
  have hbdd : BddBelow ((fun z => p ⬝ᵥ z) '' {z | (∀ i, 0 ≤ z i) ∧ u ≤ v z}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact dot_nonneg (fun i => (hp i).le) hz.1
  -- nothing affordable at `p` with spending `e u` gives more than `u`
  have hup : ∀ z ∈ budget p (e v p u), v z ≤ u := by
    intro z hz
    by_contra hlt
    push Not at hlt
    by_cases hz0 : p ⬝ᵥ z = 0
    · have : z = 0 := by
        funext i
        have hsum := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => mul_nonneg (hp j).le (hz.1 j))).1 hz0 i (Finset.mem_univ _)
        rcases mul_eq_zero.1 hsum with h | h
        · exact absurd h (hp i).ne'
        · exact h
      subst this; linarith
    · have hzpos : 0 < p ⬝ᵥ z := lt_of_le_of_ne (dot_nonneg (fun i => (hp i).le) hz.1) (Ne.symm hz0)
      have hopen : IsOpen {s : ℝ | u < v (s • z)} :=
        isOpen_lt continuous_const (hv.comp (continuous_id.smul continuous_const))
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 1 (by simpa using hlt)
      set s : ℝ := 1 - min (ε / 2) (1 / 2)
      have hs1 : s < 1 := by simp only [s]; have := lt_min (half_pos hε) (by norm_num : (0:ℝ) < 1 / 2); linarith
      have hs0 : 0 ≤ s := by simp only [s]; have := min_le_right (ε / 2) (1 / 2); linarith
      have hsb : s ∈ Metric.ball (1 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
        simp only [s]; have := min_le_left (ε / 2) (1 / 2); linarith
      have hvs : u < v (s • z) := hball hsb
      have hle : e v p u ≤ p ⬝ᵥ (s • z) := csInf_le hbdd
        ⟨s • z, ⟨fun i => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs0 (hz.1 i),
          hvs.le⟩, rfl⟩
      rw [dotProduct_smul, smul_eq_mul] at hle
      have := hz.2
      nlinarith
  have hz₀b : z₀ ∈ budget p (e v p u) := ⟨hz₀, hc₀.le⟩
  have hveq : v z₀ = u := le_antisymm (hup z₀ hz₀b) hu₀
  have : IsGreatest (v '' budget p (e v p u)) u :=
    ⟨⟨z₀, hz₀b, hveq⟩, by rintro _ ⟨z, hz, rfl⟩; exact hup z hz⟩
  exact this.csSup_eq

/-- The replacement net-income schedule. -/
def c' (v : (ι → ℝ) → ℝ) (p : ι → ℝ) (x : κ → ι → ℝ) (j : κ) : ℝ := e v p (v (x j))

/-- **The expenditure minimum is attained** (compactness): for continuous
`v`, positive prices and a nonnegative bundle `x`, some `z ≥ 0` with
`v z ≥ v x` costs exactly `e (v x)`. -/
theorem exists_expenditure_min (hv : Continuous v) (hp : ∀ i, 0 < p i) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    ∃ z, (∀ i, 0 ≤ z i) ∧ v x ≤ v z ∧ p ⬝ᵥ z = e v p (v x) := by
  set M := p ⬝ᵥ x
  set K : Set (ι → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ v x ≤ v z ∧ p ⬝ᵥ z ≤ M}
  have hdot : Continuous fun z : ι → ℝ => p ⬝ᵥ z := by
    simp only [dotProduct]; fun_prop
  have hKsub : K ⊆ Set.pi univ fun i => Icc 0 (M / p i) := by
    intro z hz i _
    refine ⟨hz.1 i, ?_⟩
    rw [le_div_iff₀ (hp i)]
    have : z i * p i ≤ p ⬝ᵥ z := by
      rw [dotProduct, mul_comm]
      exact Finset.single_le_sum (f := fun j => p j * z j)
        (fun j _ => mul_nonneg (hp j).le (hz.1 j)) (Finset.mem_univ i)
    linarith [hz.2.2]
  have hKc : IsCompact K := by
    apply (isCompact_univ_pi fun i => isCompact_Icc).of_isClosed_subset _ hKsub
    have h1 : IsClosed {z : ι → ℝ | ∀ i, 0 ≤ z i} := by
      simp only [ofPred_forall]; exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact h1.inter ((isClosed_le continuous_const hv).inter (isClosed_le hdot continuous_const))
  have hxK : x ∈ K := ⟨hx, le_rfl, le_rfl⟩
  obtain ⟨z, hzK, hzmin⟩ := hKc.exists_isMinOn ⟨x, hxK⟩ hdot.continuousOn
  refine ⟨z, hzK.1, hzK.2.1, ?_⟩
  have hleast : IsLeast ((fun z => p ⬝ᵥ z) '' {z | (∀ i, 0 ≤ z i) ∧ v x ≤ v z}) (p ⬝ᵥ z) := by
    refine ⟨⟨z, ⟨hzK.1, hzK.2.1⟩, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    by_cases hwM : p ⬝ᵥ w ≤ M
    · exact hzmin ⟨hw.1, hw.2, hwM⟩
    · push Not at hwM
      exact (hzmin hxK).trans hwM.le
  exact (hleast.csInf_eq).symm

/-- Standing assumptions on the old regime. -/
structure Regime (v : (ι → ℝ) → ℝ) (p t : ι → ℝ) (c : κ → ℝ) (x : κ → ι → ℝ) : Prop where
  cont : Continuous v
  hp : ∀ i, 0 < p i
  hq : ∀ i, 0 ≤ p i + t i
  opt : ∀ j, IsOptimal v (p + t) (c j) (x j)

variable {c : κ → ℝ} {x : κ → ι → ℝ}

theorem V_new (hR : Regime v p t c x) (j : κ) : V v p (c' v p x j) = v (x j) := by
  apply V_e hR.cont hR.hp _ (exists_expenditure_min hR.cont hR.hp (hR.opt j).1.1)
  have hc : 0 ≤ c j := (dot_nonneg hR.hq (hR.opt j).1.1).trans (hR.opt j).1.2
  exact (hR.opt j).2 0 ⟨fun _ => le_rfl, by simp [hc]⟩

/-- **Payoffs are unchanged** for every type and every option. -/
theorem utility_eq (hR : Regime v p t c x) (U : Θ → ℝ → ℝ → ℝ) (y : κ → ℝ) (θ : Θ) (j : κ) :
    U θ (V v p (c' v p x j)) (y j) = U θ (V v (p + t) (c j)) (y j) := by
  rw [V_new hR, V_of_optimal (hR.opt j)]

/-- **Incentive constraints are unchanged.** -/
theorem ic_iff (hR : Regime v p t c x) (U : Θ → ℝ → ℝ → ℝ) (y : κ → ℝ) (θ : Θ) (i j : κ) :
    U θ (V v p (c' v p x j)) (y j) ≤ U θ (V v p (c' v p x i)) (y i) ↔
      U θ (V v (p + t) (c j)) (y j) ≤ U θ (V v (p + t) (c i)) (y i) := by
  rw [utility_eq hR U y θ j, utility_eq hR U y θ i]

/-- **The replacement is an income-tax schedule**: options with equal
pre-tax income and equal old net income get equal new net income. -/
theorem c'_schedule (hR : Regime v p t c x) (y : κ → ℝ) (hc : ∀ i j, y i = y j → c i = c j)
    {i j : κ} (h : y i = y j) : c' v p x i = c' v p x j := by
  simp only [c']
  rw [← V_of_optimal (hR.opt i), ← V_of_optimal (hR.opt j), hc i j h]

/-- **Revenue weakly rises** option by option. -/
theorem revenue_ge (hR : Regime v p t c x) (y : κ → ℝ) (j : κ) :
    (y j - c j) + t ⬝ᵥ x j ≤ y j - c' v p x j := by
  have h1 := e_le (v := v) hR.hp (hR.opt j).1.1
  have h2 := (hR.opt j).1.2
  rw [add_dotProduct] at h2
  simp only [c']
  linarith

/-- **Aggregate revenue weakly rises** for any nonnegative population weights. -/
theorem aggregate_revenue_ge [Fintype κ] (hR : Regime v p t c x) (y μ : κ → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) :
    ∑ j, μ j * ((y j - c j) + t ⬝ᵥ x j) ≤ ∑ j, μ j * (y j - c' v p x j) :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (revenue_ge hR y j) (hμ j)

/-- **Income taxation dominates commodity taxation** (Atkinson–Stiglitz in
Laroque's form): the pure income tax `c'` at producer prices leaves every
payoff and every incentive constraint unchanged and weakly raises revenue
from every option. -/
theorem income_tax_dominates (hR : Regime v p t c x) (U : Θ → ℝ → ℝ → ℝ) (y : κ → ℝ) :
    (∀ θ j, U θ (V v p (c' v p x j)) (y j) = U θ (V v (p + t) (c j)) (y j)) ∧
      (∀ θ i j, U θ (V v p (c' v p x j)) (y j) ≤ U θ (V v p (c' v p x i)) (y i) ↔
        U θ (V v (p + t) (c j)) (y j) ≤ U θ (V v (p + t) (c i)) (y i)) ∧
      (∀ j, (y j - c j) + t ⬝ᵥ x j ≤ y j - c' v p x j) :=
  ⟨fun θ j => utility_eq hR U y θ j, fun θ i j => ic_iff hR U y θ i j,
    fun j => revenue_ge hR y j⟩

/-- **Non-vacuity**: one good, `v z = z`, `p = 1`, a commodity tax `t = 1`,
net income `c = 2`, bundle `x = 1`. -/
theorem example_regime :
    Regime (ι := Unit) (κ := Unit) (fun z => z ()) (fun _ => 1) (fun _ => 1) (fun _ => 2)
      (fun _ _ => 1) := by
  refine ⟨continuous_apply (), fun _ => one_pos, fun _ => by norm_num, fun _ => ?_⟩
  refine ⟨⟨fun _ => zero_le_one, by simp [dotProduct]; norm_num⟩, fun z hz => ?_⟩
  have := hz.2
  simp [dotProduct] at this
  show z () ≤ 1
  linarith

end AtkinsonStiglitz
end Econ

end
