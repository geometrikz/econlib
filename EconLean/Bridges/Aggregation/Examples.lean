/-
# Non-vacuity witnesses for the aggregation (bridge B0) and production files

PLAN.md §8.2: each headline theorem gets a concrete instance of all of its
hypotheses.

1. **Gross substitutes, two goods.** `z(p) = (p₁/p₀ − 1, p₀/p₁ − 1)` (the excess
   demand of a symmetric two-consumer Cobb–Douglas economy) is homogeneous of
   degree zero, satisfies Walras' law, and is gross substitute. The uniqueness
   theorem then says every equilibrium is proportional to `(1, 1)`.
2. **Law of demand.** `z(p) = −p` satisfies the strict law of demand, and the
   aggregation theorem applies to any number of such consumers.
3. **Gorman form.** Two consumers with demands `cₐ + w β` have Gorman form, so
   aggregate demand depends only on aggregate wealth; the converse theorem
   recovers the common slope.
4. **Production.** One consumer, one firm with constant returns technology
   `Y = {y | y₀ ≤ 0, y₁ ≤ −y₀}` (one unit of good 0 makes one unit of good 1).
   At prices `(1, 1)` the firm makes zero profit at `y = 0` and the consumer
   keeps the endowment: a Walrasian equilibrium, to which the production
   First Welfare Theorem applies; the Second Welfare Theorem's hypotheses
   (convex production set, convex LNS preferences) all hold.
-/
module

public import EconLean.Bridges.Aggregation.GrossSubstitutes
public import EconLean.Bridges.Aggregation.LawOfDemand
public import EconLean.Bridges.Aggregation.Gorman
public import EconLean.GE.Production
public import EconLean.GE.Examples

@[expose] public section

namespace Econ

namespace AggregationExamples

/-! ### 1. Gross substitutes -/

/-- Two-good excess demand `(p₁/p₀ − 1, p₀/p₁ − 1)`. -/
noncomputable def zCD (p : Fin 2 → ℝ) : Fin 2 → ℝ := ![p 1 / p 0 - 1, p 0 / p 1 - 1]

theorem zCD_homogeneous : HomogeneousZero zCD := by
  intro p hp t ht
  funext i
  fin_cases i <;> simp [zCD, mul_div_mul_left _ _ ht.ne']

theorem zCD_walras : WalrasLaw zCD {p | PositivePrices p} := by
  intro p hp
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  simp only [cost, Fin.sum_univ_two, zCD, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

theorem zCD_grossSubstitutes : GrossSubstitutes zCD := by
  intro p l t hp hlt k hkl
  fin_cases l <;> fin_cases k
  · exact absurd rfl hkl
  · -- Raise `p₀`: `z₁ = p₀ / p₁ − 1` rises.
    simp only [zCD]
    simp [Function.update_of_ne]
    exact div_lt_div_of_pos_right hlt (hp 1)
  · simp only [zCD]
    simp [Function.update_of_ne]
    exact div_lt_div_of_pos_right hlt (hp 0)
  · exact absurd rfl hkl

/-- **Uniqueness, applied.** Every positive equilibrium of `zCD` is a positive
multiple of `(1, 1)`. -/
theorem zCD_unique {p : Fin 2 → ℝ} (hp : PositivePrices p) (hz : zCD p = 0) :
    ∃ t : ℝ, 0 < t ∧ p = t • (fun _ => (1 : ℝ)) := by
  have h11 : zCD (fun _ => 1) = 0 := by
    funext i; fin_cases i <;> simp [zCD]
  exact zCD_grossSubstitutes.unique_equilibrium zCD_homogeneous (fun _ => one_pos) hp h11 hz

/-- `zCD` satisfies the weak axiom on all strictly positive prices. With
`D = p₀p₁' − p₁p₀'`, we have `p · z(p') ∝ (p₁' − p₀') D` and
`p' · z(p) ∝ −(p₁ − p₀) D`, and the sign conditions follow by cases on `D`. -/
theorem zCD_warp : ExcessWARP zCD {p | PositivePrices p} := by
  intro p hp p' hp' hne hle
  have ha := hp 0; have hb := hp 1; have hc := hp' 0; have hd := hp' 1
  simp only [Set.mem_ofPred_eq] at *
  set D := p 0 * p' 1 - p 1 * p' 0 with hD
  have e1 : cost p (zCD p') * (p' 0 * p' 1) = (p' 1 - p' 0) * D := by
    simp only [cost, Fin.sum_univ_two, zCD, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hD]
    field_simp
    ring
  have e2 : cost p' (zCD p) * (p 0 * p 1) = -((p 1 - p 0) * D) := by
    simp only [cost, Fin.sum_univ_two, zCD, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hD]
    field_simp
    ring
  -- Different excess demands force `D ≠ 0`.
  have hD0 : D ≠ 0 := by
    intro h0
    apply hne
    have hr : p 1 / p 0 = p' 1 / p' 0 := by
      rw [div_eq_div_iff ha.ne' hc.ne']; linarith
    have hr' : p 0 / p 1 = p' 0 / p' 1 := by
      rw [div_eq_div_iff hb.ne' hd.ne']; linarith
    funext i; fin_cases i <;> simp [zCD, hr, hr']
  have hle' : (p' 1 - p' 0) * D ≤ 0 := by
    rw [← e1]; exact mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
  have hgoal : 0 < -((p 1 - p 0) * D) := by
    rcases lt_or_gt_of_ne hD0 with hneg | hpos
    · have : 0 ≤ p' 1 - p' 0 := by nlinarith
      have : p 0 < p 1 := by nlinarith
      nlinarith
    · have : p' 1 - p' 0 ≤ 0 := by nlinarith
      have : p 1 < p 0 := by nlinarith
      nlinarith
  rw [← e2] at hgoal
  exact pos_of_mul_pos_left hgoal (by positivity)

/-- **WARP ⇒ convex equilibrium set, applied**: the equilibrium prices of `zCD`
form a convex set (they are the ray through `(1, 1)`). -/
example : Convex ℝ {p | p ∈ {p : Fin 2 → ℝ | PositivePrices p} ∧ zCD p = 0} := by
  refine zCD_warp.convex_equilibria ?_ zCD_walras
  intro p hp q hq s t hs ht hst i
  simp only [Set.mem_ofPred_eq, PositivePrices] at *
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases hs.lt_or_eq with hs' | hs'
  · nlinarith [hp i, hq i]
  · subst hs'; simp at hst; subst hst; simp [hq i]

/-! ### 2. Law of demand -/

theorem lawOfDemand_neg : LawOfDemand (fun p : Fin 2 → ℝ => -p) Set.univ := by
  intro p _ p' _ hne
  -- `(p' − p) · (−p' + p) = −‖p' − p‖² < 0`.
  have hne' : p' - p ≠ 0 := fun h => hne (by rw [sub_eq_zero] at h; rw [h])
  obtain ⟨i, hi⟩ : ∃ i, (p' - p) i ≠ 0 := by
    by_contra h; push Not at h; exact hne' (funext h)
  have : cost (p' - p) (-p' - -p) = -∑ j, (p' - p) j * (p' - p) j := by
    simp only [cost, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.sub_apply, Pi.neg_apply]; ring
  rw [this, neg_lt_zero]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ i, mul_self_pos.2 hi⟩

/-- Three consumers with excess demand `−p`: the aggregate satisfies the law
of demand. -/
example : LawOfDemand (fun p : Fin 2 → ℝ => ∑ _a ∈ (Finset.univ : Finset (Fin 3)), -p)
    Set.univ :=
  LawOfDemand.sum (z := fun _ p => -p) _ fun _ _ => lawOfDemand_neg

/-! ### 3. Gorman form -/

/-- Two consumers with different intercepts and common slope `(1/2, 1/2)`.
At prices `(1, 1)` each intercept costs `0` and the slope costs `1`, so the
demands are budget-balanced: `(1,1) · x_a(w) = w`. -/
noncomputable def xG (a : Fin 2) (w : ℝ) : Fin 2 → ℝ :=
  ![(a : ℝ), -(a : ℝ)] + w • (fun _ => (1 / 2 : ℝ))

theorem xG_budget (a : Fin 2) (w : ℝ) : cost (fun _ => 1) (xG a w) = w := by
  simp [xG, cost, Fin.sum_univ_two]; ring

theorem xG_gorman : GormanForm xG := ⟨fun _ => 1 / 2, fun a w => by simp [xG]⟩

/-- The nonnegative-wealth Gorman theorem applies to `xG`. -/
example : ∃ β : Fin 2 → ℝ, ∀ a, ∀ w, 0 ≤ w → xG a w = xG a 0 + w • β :=
  gorman_of_aggregatesThroughWealthNonneg
    (by obtain ⟨X, hX⟩ := aggregatesThroughWealth_of_gorman xG_gorman
        exact ⟨X, fun w _ => hX w⟩)
    (fun a => by unfold xG; exact Continuous.continuousOn (by fun_prop))

example : AggregatesThroughWealth xG := aggregatesThroughWealth_of_gorman xG_gorman

/-- The converse theorem's hypotheses hold for `xG` (two consumers, continuous
demands, aggregation through wealth). -/
example : GormanForm xG :=
  gorman_of_aggregatesThroughWealth (aggregatesThroughWealth_of_gorman xG_gorman)
    (fun a => by unfold xG; fun_prop)

/-! ### 4. Production -/

open GEExamples

/-- Constant-returns technology: turn good 0 into good 1 one-for-one. -/
def techY : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ -y 0}

theorem convex_techY : Convex ℝ techY := by
  intro y₁ h₁ y₂ h₂ s t hs ht hst
  simp only [techY, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- One consumer (perfect substitutes, endowment `(1, 1)`), one firm. -/
def prodEconomy : ProductionEconomy (Fin 1) (Fin 1) (Fin 2) where
  pref _ := prefOf uLin
  endow _ := fun _ => 1
  endow_nonneg _ := fun _ => zero_le_one
  prod _ := techY
  share _ _ := 1
  share_nonneg _ _ := zero_le_one
  share_sum _ := by simp

theorem prodEconomy_eq :
    prodEconomy.IsWalrasianEquilibrium pOne (fun _ _ => 1) (fun _ => 0) := by
  refine ⟨fun j => ⟨⟨le_rfl, by simp⟩, fun y hy => ?_⟩, fun a => ⟨⟨fun _ => zero_le_one, ?_⟩,
    fun y hy => ?_⟩, ?_⟩
  · -- Profit `y₀ + y₁ ≤ 0 = p · 0`.
    simp only [cost, pOne, Fin.sum_univ_two, one_mul, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero]
    have := hy.2; linarith
  · simp [ProductionEconomy.wealth, cost, pOne, prodEconomy]
  · show uLin y ≤ uLin (fun _ => 1)
    rw [← cost_pOne, ← cost_pOne]
    have := hy.2
    simpa [ProductionEconomy.wealth, prodEconomy, cost] using this
  · funext i
    simp [ExchangeEconomy.totalEndowment, prodEconomy]

theorem prodEconomy_paretoOptimal :
    prodEconomy.ParetoOptimal (fun _ _ => 1) (fun _ => 0) :=
  ProductionEconomy.first_welfare_theorem (fun _ => (represents_prefOf uLin).rational)
    (fun _ => lns_lin 0) prodEconomy_eq

/-- The production Second Welfare Theorem applies (all hypotheses hold). -/
example : ∃ p : Fin 2 → ℝ, p ≠ 0 ∧ prodEconomy.IsPriceQuasiEquilibriumWithTransfers p
    (fun a => cost p ((fun _ _ => (1 : ℝ)) a)) (fun _ _ => 1) (fun _ => 0) :=
  ProductionEconomy.second_welfare_theorem (fun _ => (represents_prefOf uLin).rational)
    (fun _ => convexPref_lin 0) (fun _ => lns_lin 0) (fun _ => convex_techY)
    prodEconomy_paretoOptimal

/-! #### Production with nonzero output and split ownership

Two consumers, each with `u(x) = x₀ + 2x₁`, endowment `(1, 0)` and a half
share of the firm. At prices `(1, 1)` the firm converts both units of good 0
into good 1 (`y = (−2, 2)`, zero profit under constant returns) and each
consumer buys `(0, 1)`. This exercises profit maximization at a nonzero plan,
the wealth formula with shares, and market clearing with production. -/

/-- Utility favouring good 1. -/
def uTwo (x : Fin 2 → ℝ) : ℝ := x 0 + 2 * x 1

/-- The two-consumer production economy. -/
noncomputable def prodEconomy2 : ProductionEconomy (Fin 2) (Fin 1) (Fin 2) where
  pref _ := prefOf uTwo
  endow _ := ![1, 0]
  endow_nonneg _ := by intro i; fin_cases i <;> simp
  prod _ := techY
  share _ _ := 1 / 2
  share_nonneg _ _ := by norm_num
  share_sum _ := by simp

theorem prodEconomy2_eq : prodEconomy2.IsWalrasianEquilibrium pOne
    (fun _ => ![0, 1]) (fun _ => ![-2, 2]) := by
  refine ⟨fun j => ⟨?_, fun y hy => ?_⟩, fun a => ⟨⟨?_, ?_⟩, fun y hy => ?_⟩, ?_⟩
  · show (![-2, 2] : Fin 2 → ℝ) ∈ techY
    simp [techY]
  · -- Any feasible plan has profit `y₀ + y₁ ≤ 0 = p · (−2, 2)`.
    have := hy.2
    simp [cost, pOne, Fin.sum_univ_two]
    linarith
  · intro i; fin_cases i <;> simp
  · simp [ProductionEconomy.wealth, cost, pOne, prodEconomy2, Fin.sum_univ_two]
  · -- On the budget line `y₀ + y₁ ≤ 1`, `u(y) = y₀ + 2y₁ ≤ 2 = u(0, 1)`.
    have hb : y 0 + y 1 ≤ 1 := by
      have := hy.2
      simp [ProductionEconomy.wealth, cost, pOne, prodEconomy2, Fin.sum_univ_two] at this
      linarith
    have h0 : 0 ≤ y 0 := hy.1 0
    show uTwo y ≤ uTwo ![0, 1]
    simp [uTwo]
    linarith
  · funext i
    fin_cases i <;> simp [ExchangeEconomy.totalEndowment, prodEconomy2]

theorem rational_two : Rational (prefOf uTwo) := (represents_prefOf uTwo).rational

theorem lns_two : LocallyNonsatiated (prefOf uTwo) := by
  refine StronglyMonotone.locallyNonsatiated fun x y _ hxy hne => ?_
  have hlt : uTwo x < uTwo y := by
    have h0 := hxy 0
    have h1 := hxy 1
    by_contra hle
    push Not at hle
    simp only [uTwo] at hle
    apply hne
    funext i
    fin_cases i
    · show x 0 = y 0; linarith
    · show x 1 = y 1; linarith
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- Production First Welfare Theorem in the nondegenerate economy. -/
theorem prodEconomy2_paretoOptimal :
    prodEconomy2.ParetoOptimal (fun _ => ![0, 1]) (fun _ => ![-2, 2]) :=
  ProductionEconomy.first_welfare_theorem (fun _ => rational_two) (fun _ => lns_two)
    prodEconomy2_eq

end AggregationExamples

end Econ
