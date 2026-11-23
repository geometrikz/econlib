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
public import EconLean.Bridges.Aggregation.Tatonnement
public import EconLean.GE.ExistenceInterior
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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

/-! #### MWG Prop. 17.C.1: `zCD` satisfies the boundary-condition hypotheses

`zCD` blows up at the boundary of the price simplex, like the excess demand of a
Cobb–Douglas economy, so the closed-simplex existence theorem does not apply to
it, but `exists_equilibrium_of_boundaryCondition` does. -/

section Boundary

open Filter Topology

theorem zCD_continuousOn : ContinuousOn zCD {p | PositivePrices p} := by
  refine continuousOn_pi.2 fun i => ?_
  have h0 : ContinuousOn (fun p : Fin 2 → ℝ => p 0) {p | PositivePrices p} :=
    (continuous_apply 0).continuousOn
  have h1 : ContinuousOn (fun p : Fin 2 → ℝ => p 1) {p | PositivePrices p} :=
    (continuous_apply 1).continuousOn
  fin_cases i
  · exact (h1.div h0 fun p hp => (hp 0).ne').sub continuousOn_const
  · exact (h0.div h1 fun p hp => (hp 1).ne').sub continuousOn_const

theorem zCD_boundedBelow : ExcessBoundedBelow zCD := by
  refine ⟨1, fun p hp l => ?_⟩
  fin_cases l
  · have := div_pos (hp 1) (hp 0); simp [zCD]; linarith
  · have := div_pos (hp 0) (hp 1); simp [zCD]; linarith

/-- If `aₙ → 0⁺` and `bₙ → B > 0`, then `bₙ / aₙ − 1` eventually exceeds any `M`. -/
theorem eventually_lt_div_sub_one {a b : ℕ → ℝ} {B : ℝ} (ha : ∀ n, 0 < a n)
    (halim : Tendsto a atTop (𝓝 0)) (hblim : Tendsto b atTop (𝓝 B)) (hB : 0 < B) (M : ℝ) :
    ∀ᶠ n in atTop, M < b n / a n - 1 := by
  have ha' : Tendsto a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨halim, Eventually.of_forall ha⟩
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp ha'
  have hprod : Tendsto (fun n => b n * (a n)⁻¹) atTop atTop := hblim.pos_mul_atTop hB hinv
  filter_upwards [hprod.eventually_gt_atTop (M + 1)] with n hn
  rw [div_eq_mul_inv]; linarith

theorem zCD_boundary : BoundaryCondition zCD := by
  intro pn pbar hpos hlim hne ⟨l, hl⟩ M
  have hcoord : ∀ i, Tendsto (fun n => pn n i) atTop (𝓝 (pbar i)) := fun i =>
    ((continuous_apply i).tendsto pbar).comp hlim
  have hnonneg : ∀ i, 0 ≤ pbar i := fun i =>
    ge_of_tendsto' (hcoord i) fun n => (hpos n i).le
  -- The other price is strictly positive in the limit.
  have hother : ∀ k, k ≠ l → 0 < pbar k := by
    intro k hk
    refine lt_of_le_of_ne (hnonneg k) fun h => hne ?_
    funext i
    fin_cases i <;> fin_cases k <;> fin_cases l <;> simp_all
  have hl0 : Tendsto (fun n => pn n l) atTop (𝓝 0) := hl ▸ hcoord l
  fin_cases l
  · have h := eventually_lt_div_sub_one (fun n => hpos n 0) (by simpa using hl0)
      (hcoord 1) (hother 1 (by decide)) M
    filter_upwards [h] with n hn
    exact ⟨0, by simpa [zCD] using hn⟩
  · have h := eventually_lt_div_sub_one (fun n => hpos n 1) (by simpa using hl0)
      (hcoord 0) (hother 0 (by decide)) M
    filter_upwards [h] with n hn
    exact ⟨1, by simpa [zCD] using hn⟩

/-- MWG Prop. 17.C.1 applied to `zCD`: an equilibrium with positive prices exists. -/
example : ∃ p, PositivePrices p ∧ zCD p = 0 :=
  exists_equilibrium_of_boundaryCondition zCD_continuousOn (fun p hp => zCD_walras p hp)
    zCD_boundedBelow zCD_boundary

end Boundary

/-- **Tâtonnement, two goods.** For `zCD`, gross substitutes gives
`p* · z(q) > 0` at every disequilibrium price, with `p* = (1, 1)`. -/
theorem zCD_cost_pos {q : Fin 2 → ℝ} (hq : PositivePrices q) (hz : zCD q ≠ 0) :
    0 < cost (fun _ => (1 : ℝ)) (zCD q) := by
  have h11 : zCD (fun _ => 1) = 0 := by
    funext i; fin_cases i <;> simp [zCD]
  exact zCD_grossSubstitutes.cost_pos_two_goods zCD_homogeneous (fun q hq => zCD_walras q hq)
    (fun _ => one_pos) hq h11 hz

/-- Along any tâtonnement path for `zCD` that stays in positive prices for
`t ≥ 0`, the distance to the equilibrium `(1, 1)` never increases. -/
theorem zCD_tatonnement_antitone {p : ℝ → Fin 2 → ℝ} (hpath : IsTatonnementPath zCD p)
    (hpos : ∀ t, 0 ≤ t → PositivePrices (p t)) :
    AntitoneOn (fun t => priceDistSq (p t) (fun _ => (1 : ℝ))) (Set.Ici 0) :=
  tatonnement_antitone hpath (fun t ht => zCD_walras (p t) (hpos t ht))
    (fun t ht hz => zCD_cost_pos (hpos t ht) hz)

/-! #### A nonconstant tâtonnement path

The excess demand `zArc q = (π/4 − arctan(q₁/q₀)) · (−q₁, q₀)` satisfies Walras'
law, and the path `p(t) = (cos φ(t), sin φ(t))` with `φ(t) = π/4 − (π/8) e^{−t}`
solves `ṗ = zArc(p)`: prices rotate on the unit circle toward the equilibrium
ray through `(1, 1)`. It witnesses that the hypotheses of `tatonnement_strictAnti`
hold for a path that is never at equilibrium.

`zArc` is **not** the excess demand of an economy (it is homogeneous of degree
one, not zero, and not gross substitute); it only shows the abstract hypotheses
are jointly satisfiable by a nonconstant path. -/

section Arc

open Real

/-- The angle of the example path. -/
noncomputable def φArc (t : ℝ) : ℝ := π / 4 - π / 8 * Real.exp (-t)

/-- The example excess demand. -/
noncomputable def zArc (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (π / 4 - Real.arctan (q 1 / q 0)) • ![-q 1, q 0]

/-- The example path. -/
noncomputable def pArc (t : ℝ) : Fin 2 → ℝ := ![Real.cos (φArc t), Real.sin (φArc t)]

theorem φArc_bounds {t : ℝ} (ht : 0 ≤ t) : π / 8 ≤ φArc t ∧ φArc t < π / 4 := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  constructor <;> simp only [φArc] <;> nlinarith [Real.pi_pos]

theorem hasDerivAt_φArc (t : ℝ) : HasDerivAt φArc (π / 8 * Real.exp (-t)) t := by
  have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul (π / 8)
  exact (h.const_sub (π / 4)).congr_deriv (by ring)

theorem arctan_pArc {t : ℝ} (ht : 0 ≤ t) : Real.arctan (pArc t 1 / pArc t 0) = φArc t := by
  obtain ⟨h1, h2⟩ := φArc_bounds ht
  simp only [pArc, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  rw [← Real.tan_eq_sin_div_cos, Real.arctan_tan] <;> linarith [Real.pi_pos]

theorem zArc_pArc {t : ℝ} (ht : 0 ≤ t) :
    zArc (pArc t) = (π / 8 * Real.exp (-t)) • ![-Real.sin (φArc t), Real.cos (φArc t)] := by
  rw [zArc, arctan_pArc ht]
  simp only [pArc, φArc, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  congr 1; ring

theorem pArc_isTatonnementPath : IsTatonnementPath zArc pArc := fun t ht => by
  refine HasDerivAt.hasDerivWithinAt ?_
  rw [zArc_pArc ht, hasDerivAt_pi]
  intro i
  fin_cases i
  · have := (Real.hasDerivAt_cos (φArc t)).comp t (hasDerivAt_φArc t)
    simp only [pArc, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply,
      smul_eq_mul]
    exact this.congr_deriv (by ring)
  · have := (Real.hasDerivAt_sin (φArc t)).comp t (hasDerivAt_φArc t)
    simp only [pArc, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.smul_apply, smul_eq_mul]
    exact this.congr_deriv (by ring)

theorem pArc_walras (t : ℝ) (ht : 0 ≤ t) : cost (pArc t) (zArc (pArc t)) = 0 := by
  rw [zArc_pArc ht]
  simp only [cost, Fin.sum_univ_two, pArc, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem sin_lt_cos_φArc {t : ℝ} (ht : 0 ≤ t) : Real.sin (φArc t) < Real.cos (φArc t) := by
  obtain ⟨h1, h2⟩ := φArc_bounds ht
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) (by linarith)

theorem pArc_cost_pos (t : ℝ) (ht : 0 ≤ t) : 0 < cost (fun _ => (1 : ℝ)) (zArc (pArc t)) := by
  rw [zArc_pArc ht]
  simp only [cost, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
  have := sin_lt_cos_φArc ht
  have he := Real.exp_pos (-t)
  nlinarith [Real.pi_pos, mul_pos (mul_pos (by positivity : (0:ℝ) < π / 8) he)
    (sub_pos.2 this)]

theorem zArc_pArc_ne (t : ℝ) (ht : 0 ≤ t) : zArc (pArc t) ≠ 0 := by
  intro h
  have := pArc_cost_pos t ht
  rw [h] at this; simp [cost] at this

/-- **Non-vacuity of tâtonnement stability.** The example path never reaches
equilibrium and moves strictly closer to `(1, 1)` for all `t ≥ 0`. -/
theorem pArc_strictAnti :
    StrictAntiOn (fun t => priceDistSq (pArc t) (fun _ => (1 : ℝ))) (Set.Ici 0) :=
  tatonnement_strictAnti pArc_isTatonnementPath pArc_walras
    (fun t ht _ => pArc_cost_pos t ht) (fun t ht => zArc_pArc_ne t (le_of_lt ht))

end Arc

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
