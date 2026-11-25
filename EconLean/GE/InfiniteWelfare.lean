/-
# The First Welfare Theorem with infinitely many goods and agents

Catalog B4.6. Debreu (1954), "Valuation equilibrium and Pareto optimum";
Shell (1971), "Notes on the economics of infinity"; Balasko–Shell (1980), "The
overlapping-generations model, I", Prop. 5.6; Ljungqvist–Sargent §9.2.

**The economics.** With finitely many agents, the First Welfare Theorem
(`ExchangeEconomy.first_welfare_theorem`) sums budget inequalities over
agents. With infinitely many agents and goods (overlapping generations,
infinite horizons) that sum can diverge, and the theorem can fail: the
Samuelson economy (`Macro/OLG/Samuelson.lean`) has an inefficient competitive
equilibrium. The repair (Shell 1971): **if the aggregate endowment has finite
value at the equilibrium prices, the equilibrium is Pareto optimal.**

**Setup.** Goods `G` and agents `A` are arbitrary types (e.g. `ℕ`, dates and
generations). Bundles and prices are nonnegative (`G → ℝ≥0`), and the value of
a bundle is `p · y = ∑' g, p g * y g ∈ [0, ∞]`, computed in `ℝ≥0∞` so that
sums can always be exchanged. An allocation is feasible if each good's
consumption sums (as a convergent series over agents) to the aggregate
endowment. Preferences are arbitrary transitive relations satisfying
**local nonsatiation with respect to value** (`ValueLNS`): any bundle can be
strictly improved at arbitrarily small extra cost. This is a value-metric
analogue of local nonsatiation that delivers Debreu (1954)'s cost-minimisation
property directly and needs no topology on the commodity space. It is a joint
condition on preferences and prices, and is not comparable to topological local
nonsatiation in general (they agree, e.g., for the sup norm and summable prices).

**Results.**
* `first_welfare_theorem_infinite`: a competitive equilibrium in which the
  aggregate endowment has finite value is Pareto optimal.
* `hotelEconomy_*` (Shell 1971's "Hilbert hotel"): goods and agents `ℕ`,
  agent `a` owns one unit of good `a` and has utility `x_a + x_{a+1}`. At prices
  `1` autarky is an equilibrium, preferences are value-locally nonsatiated, but
  the aggregate endowment has infinite value, and shifting every agent's
  consumption one good up makes agent `0` strictly better off and nobody worse
  off. So the finite-value hypothesis cannot be dropped.
* `ownGoodEconomy_*`: with the same endowments, utility `x_a` and prices
  `2^{-g}`, the aggregate endowment has value `2` and autarky is Pareto optimal
  by the theorem. This is a sanity check that the hypotheses are jointly
  satisfiable; its conclusion is also immediate by inspection.

**Deviations.** Exchange only; budget sets are value constraints on
nonnegative bundles (no consumption sets beyond `ℝ≥0^G`). Debreu (1954) works in
a general linear space with a linear price functional; here prices are
nonnegative coordinates and values may be infinite. Feasibility is market
clearing with equality (no free disposal), so Pareto optimality is tested
against exactly-feasible allocations only.
-/
module

public import EconLean.Preferences.Utility
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

noncomputable section

namespace Econ
namespace InfiniteWelfare

open scoped NNReal ENNReal

variable {A G : Type*}

/-- The **value** `p · y = ∑' g, p_g y_g ∈ [0, ∞]` of a bundle at prices `p`. -/
def value (p y : G → ℝ≥0) : ℝ≥0∞ := ∑' g, (p g : ℝ≥0∞) * (y g : ℝ≥0∞)

/-- An allocation `y` is **feasible** for the aggregate endowment `ωbar` if, for
every good, consumption over all agents sums to `ωbar g`. -/
def Feasible (ωbar : G → ℝ≥0) (y : A → G → ℝ≥0) : Prop :=
  ∀ g, HasSum (fun a => y a g) (ωbar g)

/-- `(p, x)` is a **competitive equilibrium** of the exchange economy with
preferences `R`, endowments `ω` and aggregate endowment `ωbar`: every `x a` is
best for agent `a` among bundles worth at most `p · ωₐ`, and markets clear.
Prices are not normalised; `p = 0` is ruled out in the welfare theorem by
`ValueLNS`. -/
def IsEquilibrium (R : A → (G → ℝ≥0) → (G → ℝ≥0) → Prop) (ω : A → G → ℝ≥0)
    (ωbar : G → ℝ≥0) (p : G → ℝ≥0) (x : A → G → ℝ≥0) : Prop :=
  (∀ a, value p (x a) ≤ value p (ω a) ∧ ∀ y, value p y ≤ value p (ω a) → R a (x a) y) ∧
    Feasible ωbar x

/-- `x` is **Pareto optimal**: no feasible allocation makes everyone at least
as well off and someone strictly better off. -/
def ParetoOptimal (R : A → (G → ℝ≥0) → (G → ℝ≥0) → Prop) (ωbar : G → ℝ≥0)
    (x : A → G → ℝ≥0) : Prop :=
  ¬ ∃ y, Feasible ωbar y ∧ (∀ a, R a (y a) (x a)) ∧ ∃ a, P (R a) (y a) (x a)

/-- **Local nonsatiation with respect to value**: every bundle can be strictly
improved at an extra cost below any `ε > 0`. A value-metric analogue of local
nonsatiation that yields Debreu (1954)'s cost-minimisation step; it depends on
`p`. -/
def ValueLNS (R : (G → ℝ≥0) → (G → ℝ≥0) → Prop) (p : G → ℝ≥0) : Prop :=
  ∀ y, ∀ ε : ℝ≥0∞, 0 < ε → ∃ z, value p z ≤ value p y + ε ∧ P R z y

/-- For a feasible allocation, the values of the agents' bundles add up to the
value of the aggregate endowment (sums of nonnegative terms commute). -/
theorem tsum_value_of_feasible {ωbar : G → ℝ≥0} {y : A → G → ℝ≥0} (hy : Feasible ωbar y)
    (p : G → ℝ≥0) : ∑' a, value p (y a) = value p ωbar := by
  unfold value
  rw [tsum_comm]
  refine tsum_congr fun g => ?_
  rw [ENNReal.tsum_mul_left, ← ENNReal.coe_tsum (hy g).summable, (hy g).tsum_eq]

/-- **First Welfare Theorem with infinitely many goods and agents** (Shell 1971;
Balasko–Shell 1980): a competitive equilibrium with transitive, value-locally
nonsatiated preferences, in which the **aggregate endowment has finite value**,
is Pareto optimal. -/
theorem first_welfare_theorem_infinite {R : A → (G → ℝ≥0) → (G → ℝ≥0) → Prop}
    (htr : ∀ a x y z, R a x y → R a y z → R a x z) {ω : A → G → ℝ≥0} {ωbar : G → ℝ≥0}
    (hω : Feasible ωbar ω) {p : G → ℝ≥0} (hlns : ∀ a, ValueLNS (R a) p)
    (hfin : value p ωbar ≠ ∞) {x : A → G → ℝ≥0} (heq : IsEquilibrium R ω ωbar p x) :
    ParetoOptimal R ωbar x := by
  rintro ⟨y, hy, hweak, a0, hstrict⟩
  -- Everyone's new bundle costs at least their wealth (local nonsatiation).
  have hge : ∀ a, value p (ω a) ≤ value p (y a) := by
    intro a
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hz, hzP⟩ := hlns a (y a) (value p (ω a) - value p (y a)) (tsub_pos_of_lt hlt)
    rw [add_tsub_cancel_of_le hlt.le] at hz
    have hxz := (heq.1 a).2 z hz
    exact hzP.2 (htr a _ _ _ (hweak a) hxz)
  -- The strictly better-off agent's new bundle is unaffordable.
  have hlt : value p (ω a0) < value p (y a0) := by
    by_contra hle
    push Not at hle
    exact hstrict.2 ((heq.1 a0).2 _ hle)
  have hsum := ENNReal.tsum_lt_tsum (by rw [tsum_value_of_feasible hω]; exact hfin) hge hlt
  rw [tsum_value_of_feasible hω, tsum_value_of_feasible hy] at hsum
  exact lt_irrefl _ hsum

/-! ### Witnesses on `ℕ` -/

/-- One unit of good `k`. -/
def unit (k : ℕ) : ℕ → ℝ≥0 := fun g => if g = k then 1 else 0

theorem value_unit (p : ℕ → ℝ≥0) (k : ℕ) : value p (unit k) = p k := by
  unfold value unit
  have : ∀ g, (p g : ℝ≥0∞) * ((if g = k then 1 else 0 : ℝ≥0) : ℝ≥0∞) =
      if g = k then (p k : ℝ≥0∞) else 0 := by
    intro g; split_ifs with h <;> simp [h]
  simp only [this]
  exact tsum_ite_eq k _

/-- Endowments `ωₐ = unit a` add up to one unit of every good. -/
theorem feasible_unit : Feasible (A := ℕ) (fun _ => 1) unit := by
  intro g
  have : (fun a => unit a g) = fun a => if a = g then 1 else 0 := by
    funext a; simp only [unit]; split_ifs <;> simp_all
  rw [this]
  exact hasSum_ite_eq g 1

theorem value_add_unit (p y : ℕ → ℝ≥0) (k : ℕ) (δ : ℝ≥0) :
    value p (y + δ • unit k) = value p y + (p k : ℝ≥0∞) * δ := by
  unfold value
  have : ∀ g, (p g : ℝ≥0∞) * ((y + δ • unit k) g : ℝ≥0)
      = (p g : ℝ≥0∞) * (y g : ℝ≥0∞) + if g = k then (p k : ℝ≥0∞) * δ else 0 := by
    intro g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, ENNReal.coe_add,
      ENNReal.coe_mul]
    split_ifs with h
    · subst h; simp [mul_add]
    · simp
  simp only [this]
  rw [tsum_add, tsum_ite_eq]

/-- A small positive amount `δ` of good `k` costs at most `ε`. -/
theorem exists_pos_mul_le (q : ℝ≥0) (hq : 0 < q) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ (q : ℝ≥0∞) * δ ≤ ε := by
  obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  refine ⟨r / q, div_pos (by exact_mod_cast hr0) hq, ?_⟩
  rw [← ENNReal.coe_mul, mul_div_cancel₀ _ hq.ne']
  exact hrε.le

/-! #### The Hilbert hotel: infinite value, inefficient equilibrium -/

/-- Agent `a` likes goods `a` and `a + 1` equally. -/
def hotelU (a : ℕ) (x : ℕ → ℝ≥0) : ℝ := (x a : ℝ) + x (a + 1)

/-- Unit prices. -/
def hotelPrice : ℕ → ℝ≥0 := fun _ => 1

theorem hotel_value_le (y : ℕ → ℝ≥0) (a : ℕ) :
    ((y a + y (a + 1) : ℝ≥0) : ℝ≥0∞) ≤ value hotelPrice y := by
  unfold value hotelPrice
  simp only [ENNReal.coe_one, one_mul, ENNReal.coe_add]
  have := sum_le_tsum (f := fun g => (y g : ℝ≥0∞)) ({a, a + 1} : Finset ℕ)
  rwa [Finset.sum_pair (by omega)] at this

/-- Autarky is a competitive equilibrium of the hotel economy at unit prices. -/
theorem hotelEconomy_isEquilibrium :
    IsEquilibrium (fun a => prefOf (hotelU a)) unit (fun _ => 1) hotelPrice unit := by
  refine ⟨fun a => ⟨le_rfl, fun y hy => ?_⟩, feasible_unit⟩
  show hotelU a y ≤ hotelU a (unit a)
  rw [value_unit] at hy
  have h1 := (hotel_value_le y a).trans hy
  simp only [hotelPrice, ENNReal.coe_one] at h1
  have h2 : y a + y (a + 1) ≤ 1 := by exact_mod_cast h1
  have hne : a + 1 ≠ a := by omega
  simp only [hotelU, unit, ↓reduceIte, hne, NNReal.coe_one, NNReal.coe_zero, add_zero]
  have : ((y a + y (a + 1) : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h2
  push_cast at this
  linarith

theorem hotelEconomy_valueLNS (a : ℕ) : ValueLNS (prefOf (hotelU a)) hotelPrice := by
  intro y ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_le 1 one_pos hε
  refine ⟨y + δ • unit a, ?_, ?_⟩
  · rw [value_add_unit]; gcongr; simpa [hotelPrice] using hδε
  · have hne : a + 1 ≠ a := by omega
    have hlt : hotelU a y < hotelU a (y + δ • unit a) := by
      simp only [hotelU, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, ↓reduceIte, hne,
        mul_one, mul_zero, add_zero, NNReal.coe_add]
      have : (0 : ℝ) < δ := hδ
      linarith
    exact ⟨hlt.le, not_le.2 hlt⟩

/-- The aggregate endowment has **infinite value** at unit prices. -/
theorem hotelEconomy_value_top : value hotelPrice (fun _ => 1) = ∞ := by
  unfold value hotelPrice
  simp only [ENNReal.coe_one, mul_one]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- The shifted allocation: agent `0` gets goods `0` and `1`; agent `a ≥ 1`
gets good `a + 1`. -/
def hotelShift (a : ℕ) : ℕ → ℝ≥0 := if a = 0 then unit 0 + unit 1 else unit (a + 1)

theorem hotelShift_feasible : Feasible (fun _ => (1 : ℝ≥0)) hotelShift := by
  intro g
  show HasSum _ 1
  have key : ∀ a, hotelShift a g = if a = (if g ≤ 1 then 0 else g - 1) then 1 else 0 := by
    intro a
    rcases Nat.lt_or_ge g 2 with hg | hg
    · rw [show (if g ≤ 1 then 0 else g - 1) = 0 by rw [ite_eq_left_iff]; omega]
      by_cases ha : a = 0
      · subst ha
        rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl <;> simp [hotelShift, unit]
      · have : g ≠ a + 1 := by omega
        simp [hotelShift, unit, ha, this]
    · rw [show (if g ≤ 1 then 0 else g - 1) = g - 1 by rw [ite_eq_right_iff]; omega]
      by_cases ha : a = 0
      · subst ha
        have h0 : g ≠ 0 := by omega
        have h1 : g ≠ 1 := by omega
        have h2 : (0 : ℕ) ≠ g - 1 := by omega
        simp [hotelShift, unit, h0, h1, h2]
      · have : (g = a + 1) ↔ (a = g - 1) := by omega
        simp [hotelShift, unit, ha, this]
  rw [show (fun a => hotelShift a g) = _ from funext key]
  exact hasSum_ite_eq _ 1

/-- **The First Welfare Theorem fails without finite value** (Shell 1971): the
shifted allocation is feasible, leaves every agent as well off as in the
autarkic equilibrium, and makes agent `0` strictly better off. -/
theorem hotelEconomy_not_paretoOptimal :
    ¬ ParetoOptimal (fun a => prefOf (hotelU a)) (fun _ => 1) unit := by
  intro hpo
  refine hpo ⟨hotelShift, hotelShift_feasible, fun a => ?_, 0, ?_⟩
  · show hotelU a (unit a) ≤ hotelU a (hotelShift a)
    by_cases ha : a = 0
    · subst ha; simp [hotelU, hotelShift, unit]
    · simp [hotelU, hotelShift, unit, ha]
  · have : hotelU 0 (unit 0) < hotelU 0 (hotelShift 0) := by
      simp [hotelU, hotelShift, unit]
    exact ⟨this.le, not_le.2 this⟩

/-! #### Summable prices: finite value, efficient equilibrium -/

/-- Agent `a` cares only about good `a`. -/
def ownU (a : ℕ) (x : ℕ → ℝ≥0) : ℝ := x a

/-- Prices `2^{-g}`. -/
def halfPrice : ℕ → ℝ≥0 := fun g => (2⁻¹ : ℝ≥0) ^ g

theorem halfPrice_pos (g : ℕ) : 0 < halfPrice g := pow_pos (by norm_num) g

theorem ownGoodEconomy_isEquilibrium :
    IsEquilibrium (fun a => prefOf (ownU a)) unit (fun _ => 1) halfPrice unit := by
  refine ⟨fun a => ⟨le_rfl, fun y hy => ?_⟩, feasible_unit⟩
  show ownU a y ≤ ownU a (unit a)
  rw [value_unit] at hy
  have h1 : (halfPrice a : ℝ≥0∞) * y a ≤ value halfPrice y :=
    le_tsum (fun g => (halfPrice g : ℝ≥0∞) * y g) a
  have h2 : ((halfPrice a * y a : ℝ≥0) : ℝ≥0∞) ≤ (halfPrice a : ℝ≥0∞) * 1 := by
    rw [mul_one, ENNReal.coe_mul]; exact h1.trans hy
  rw [← ENNReal.coe_one, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h2
  have h3 : y a ≤ 1 := le_of_mul_le_mul_left h2 (halfPrice_pos a)
  simp only [ownU, unit, ↓reduceIte, NNReal.coe_one]
  exact_mod_cast h3

theorem ownGoodEconomy_valueLNS (a : ℕ) : ValueLNS (prefOf (ownU a)) halfPrice := by
  intro y ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_le (halfPrice a) (halfPrice_pos a) hε
  refine ⟨y + δ • unit a, ?_, ?_⟩
  · rw [value_add_unit]; gcongr
  · have hlt : ownU a y < ownU a (y + δ • unit a) := by
      simp only [ownU, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, ↓reduceIte, mul_one,
        NNReal.coe_add]
      have : (0 : ℝ) < δ := hδ
      linarith
    exact ⟨hlt.le, not_le.2 hlt⟩

/-- The aggregate endowment has **finite value** `∑ 2^{-g} = 2`. -/
theorem ownGoodEconomy_value_ne_top : value halfPrice (fun _ => 1) ≠ ∞ := by
  unfold value halfPrice
  simp only [ENNReal.coe_one, mul_one, ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero,
    ENNReal.coe_ofNat]
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

/-- **Autarky is Pareto optimal** in the own-good economy, by the infinite First
Welfare Theorem. (A sanity check of joint satisfiability: since each agent
values only their own good, the conclusion is also immediate.) -/
theorem ownGoodEconomy_paretoOptimal :
    ParetoOptimal (fun a => prefOf (ownU a)) (fun _ => 1) unit :=
  first_welfare_theorem_infinite (R := fun a => prefOf (ownU a))
    (fun _ _ _ _ h1 h2 => le_trans h2 h1) feasible_unit
    ownGoodEconomy_valueLNS ownGoodEconomy_value_ne_top ownGoodEconomy_isEquilibrium

end InfiniteWelfare
end Econ
