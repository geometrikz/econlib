/-
# Existence with production: witnesses for free disposal and several firms

Companion to `GE/ExistenceArrowDebreu.lean` (MWG §17.B–C, Arrow–Debreu 1954).

**Why disposal can be needed.** `exists_freeDisposalEquilibrium_arrowDebreu`
only promises a *free-disposal* equilibrium: aggregate demand is at most supply,
and any excess supply is of zero-priced goods. `badEconomy` shows this is the
right conclusion: exact clearing at nonnegative prices can genuinely fail. Its
single consumer
regards good `1` as a **bad** (`u x = x₀ − x₁`), is endowed with one unit of
each good, and the only firm can do nothing (`Y = {0}`). All hypotheses of the
free-disposal theorem hold (continuous, linear hence quasiconcave, locally
nonsatiated utility, `ω ≫ 0`, `Y` closed, convex, with no free lunch and
irreversibility), yet:
* `badEconomy_no_walrasianEquilibrium`: at **no** nonnegative prices is there a
  Walrasian equilibrium with exact market clearing (the consumer always prefers
  to throw good `1` away);
* `badEconomy_excess_supply`: hence every free-disposal equilibrium (at
  nonnegative prices) has strict excess supply, and `badEconomy_disposal_needed`
  exhibits one, via the existence theorem. So the hypothesis `hfd` (some firm
  with free disposal) of `exists_walrasianEquilibrium_arrowDebreu_lns` cannot be
  dropped;
* `badEconomy_negativePrice_equilibrium`: the failure is due to the sign
  restriction on prices: at `p = (1, −1)` (a negative price for the bad),
  autarky is an exact-clearing equilibrium.

**Several firms.** `twoFirmEconomy`: two square-root consumers; consumer `0`
owns a constant-returns firm (`linearSet`) and consumer `1` owns a
capacity-constrained, more productive firm (`capSet`: two units of good `1` per
unit of good `0`, at most two units of output), which earns positive profit, so
ownership shares matter. `exists_walrasianEquilibrium_arrowDebreu` applies to
the aggregate technology `linearSet + capSet`, which is strictly larger than
either firm's set.
-/
module

public import EconLean.GE.ExistenceArrowDebreu

@[expose] public section

noncomputable section

namespace Econ
namespace GEExamples

open Set Finset ProductionEconomy

/-! ### A bad good: disposal is needed -/

/-- Good `0` is a good, good `1` is a bad. -/
def uBad (x : Fin 2 → ℝ) : ℝ := x 0 - x 1

theorem continuous_uBad : Continuous uBad := by unfold uBad; fun_prop

theorem quasiconcaveOn_uBad : QuasiconcaveOn ℝ (Ici 0) uBad := by
  intro r x hx y hy a b ha hb hab
  refine ⟨(convex_Ici (0 : Fin 2 → ℝ)) hx.1 hy.1 ha hb hab, ?_⟩
  have h1 : r ≤ uBad x := hx.2
  have h2 : r ≤ uBad y := hy.2
  have k := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  rw [← add_mul, hab, one_mul] at k
  show r ≤ uBad (a • x + b • y)
  simp only [uBad, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at k ⊢
  linarith

/-- Local nonsatiation: add a little of good `0`. -/
theorem lns_uBad : LocallyNonsatiated (prefOf uBad) := by
  intro x hx ε hε
  refine ⟨x + Pi.single 0 (ε / 2), ?_, ?_, ?_⟩
  · intro i
    have := hx i
    fin_cases i <;> simp at this ⊢ <;> linarith
  · rw [dist_pi_lt_iff hε]
    intro i
    fin_cases i <;> simp [abs_of_pos hε] <;> linarith
  · have h : uBad (x + Pi.single 0 (ε / 2)) = uBad x + ε / 2 := by simp [uBad]; ring
    refine ⟨?_, ?_⟩
    · show uBad x ≤ uBad (x + Pi.single 0 (ε / 2)); rw [h]; linarith
    · show ¬ uBad (x + Pi.single 0 (ε / 2)) ≤ uBad x; rw [h]; linarith

/-- One consumer with a bad, endowed with `(1, 1)`; one firm that can only be
inactive. -/
def badEconomy : ProductionEconomy (Fin 1) (Fin 1) (Fin 2) where
  pref _ := prefOf uBad
  endow _ := fun _ => 1
  endow_nonneg _ _ := by norm_num
  prod _ := {0}
  share _ _ := 1
  share_nonneg _ _ := by norm_num
  share_sum _ := by simp

theorem badEconomy_aggProd : badEconomy.aggProd = {0} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : y 0 = 0 := hy 0
    simp [this]
  · intro hz
    rw [mem_singleton_iff] at hz
    exact ⟨fun _ => 0, fun _ => rfl, by simp [hz]⟩

/-- **No exact-clearing equilibrium** at any nonnegative prices: the
endowment `(1, 1)` is never demanded, since `(1, 0)` is affordable and better. -/
theorem badEconomy_no_walrasianEquilibrium (p : Fin 2 → ℝ) (hp : 0 ≤ p)
    (x : Fin 1 → Fin 2 → ℝ) (y : Fin 1 → Fin 2 → ℝ) :
    ¬ badEconomy.IsWalrasianEquilibrium p x y := by
  rintro ⟨hpm, hd, hclear⟩
  have hy : y 0 = 0 := (hpm 0).1
  have hx : x 0 = fun _ => 1 := by
    have := hclear
    simp only [Fin.sum_univ_one, hy, add_zero] at this
    rw [this]
    simp [badEconomy, ExchangeEconomy.totalEndowment]
  have hdem := (hd 0).2 ![1, 0]
  have hbud : ![1, 0] ∈ budgetSet p (badEconomy.wealth p y 0) := by
    refine ⟨fun i => by fin_cases i <;> simp, ?_⟩
    simp only [ProductionEconomy.wealth, badEconomy, hy, cost, Fin.sum_univ_two,
      Fin.sum_univ_one]
    have := hp 1
    simp at this ⊢
    linarith
  have := hdem hbud
  change uBad ![1, 0] ≤ uBad (x 0) at this
  rw [hx] at this
  simp [uBad] at this
  norm_num at this

/-- At any nonnegative prices, profit maximization and utility maximization are
incompatible with exact market clearing: any free-disposal equilibrium has
strict excess supply. -/
theorem badEconomy_excess_supply (p : Fin 2 → ℝ) (hp : 0 ≤ p) (x : Fin 1 → Fin 2 → ℝ)
    (y : Fin 1 → Fin 2 → ℝ) (hpm : ∀ j, ProfitMax p (badEconomy.prod j) (y j))
    (hd : ∀ a, x a ∈ demand (badEconomy.pref a) p (badEconomy.wealth p y a)) :
    ∑ a, x a ≠ badEconomy.totalEndowment + ∑ j, y j := fun heq =>
  badEconomy_no_walrasianEquilibrium p hp x y ⟨hpm, hd, heq⟩

/-- With a **negative price** on the bad, autarky is an exact-clearing
Walrasian equilibrium: the failure above comes from requiring `p ≥ 0`. -/
theorem badEconomy_negativePrice_equilibrium :
    badEconomy.IsWalrasianEquilibrium ![1, -1] (fun _ => fun _ => 1) 0 := by
  refine ⟨fun j => ⟨rfl, fun y' hy' => by rw [hy']; simp⟩, fun a => ⟨⟨fun i => by simp, ?_⟩, ?_⟩, ?_⟩
  · simp [ProductionEconomy.wealth, badEconomy, cost, Fin.sum_univ_two]
  · rintro z ⟨hz0, hz⟩
    simp only [ProductionEconomy.wealth, badEconomy, cost, Fin.sum_univ_two] at hz
    simp at hz
    change uBad z ≤ uBad (fun _ => 1)
    simp only [uBad]
    linarith
  · simp [badEconomy, ExchangeEconomy.totalEndowment]

/-- All hypotheses of `exists_freeDisposalEquilibrium_arrowDebreu` hold, so a
free-disposal equilibrium exists, and (by `badEconomy_excess_supply`) it has
strict excess supply: disposal is genuinely needed. -/
theorem badEconomy_disposal_needed :
    ∃ (p : Fin 2 → ℝ) (x : Fin 1 → Fin 2 → ℝ) (y : Fin 1 → Fin 2 → ℝ), p ∈ priceSimplex (Fin 2) ∧
      (∀ j, ProfitMax p (badEconomy.prod j) (y j)) ∧
      (∀ a, x a ∈ demand (badEconomy.pref a) p (badEconomy.wealth p y a)) ∧
      ∑ a, x a ≤ badEconomy.totalEndowment + ∑ j, y j ∧
      cost p (∑ a, x a - badEconomy.totalEndowment - ∑ j, y j) = 0 ∧
      ∑ a, x a ≠ badEconomy.totalEndowment + ∑ j, y j := by
  obtain ⟨p, x, y, hp, hpm, hd, hle, hcost⟩ :=
    badEconomy.exists_freeDisposalEquilibrium_arrowDebreu (u := fun _ => uBad)
      (fun _ => rfl) (fun _ => continuous_uBad) (fun _ => quasiconcaveOn_uBad)
      (fun _ => lns_uBad) (fun _ _ => by simp [badEconomy]) (fun _ => rfl)
      (fun _ => isClosed_singleton) (fun _ => convex_singleton _)
      (by rw [badEconomy_aggProd]; intro y hy _; exact hy)
      (by rw [badEconomy_aggProd]; intro y hy _; exact hy)
  exact ⟨p, x, y, hp, hpm, hd, hle, hcost, badEconomy_excess_supply p hp.1 x y hpm hd⟩

/-! ### Two firms -/

/-- A **capacity-constrained** technology: two units of good `1` per unit of
good `0`, at most two units of output, with free disposal. -/
def capSet : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ -2 * y 0 ∧ y 1 ≤ 2}

theorem zero_mem_capSet : (0 : Fin 2 → ℝ) ∈ capSet := by
  simp [capSet]

theorem isClosed_capSet : IsClosed capSet :=
  show IsClosed ({y : Fin 2 → ℝ | y 0 ≤ 0} ∩ ({y | y 1 ≤ -2 * y 0} ∩ {y | y 1 ≤ 2})) from
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le (continuous_apply 1) (by fun_prop)).inter
      (isClosed_le (continuous_apply 1) continuous_const))

theorem convex_capSet : Convex ℝ capSet := by
  intro x hx y hy a b ha hb hab
  simp only [capSet, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2.1, hy.2.1], ?_⟩
  have : a * 2 + b * 2 = 2 := by rw [← add_mul, hab, one_mul]
  nlinarith [hx.2.2, hy.2.2]

/-- Two square-root consumers each owning `(1, 1)`; consumer `0` owns the
constant-returns firm `linearSet`, consumer `1` owns the capacity-constrained
firm `capSet`. -/
def twoFirmEconomy : ProductionEconomy (Fin 2) (Fin 2) (Fin 2) where
  pref _ := prefOf uSqrt
  endow _ := fun _ => 1
  endow_nonneg _ _ := by norm_num
  prod j := if j = 0 then linearSet else capSet
  share a j := if a = j then 1 else 0
  share_nonneg a j := by split_ifs <;> norm_num
  share_sum j := by simp

theorem mem_twoFirmEconomy_aggProd {z : Fin 2 → ℝ} (hz : z ∈ twoFirmEconomy.aggProd) :
    ∃ a ∈ linearSet, ∃ b ∈ capSet, z = a + b := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y 0, by simpa [twoFirmEconomy] using hy 0, y 1, by simpa [twoFirmEconomy] using hy 1,
    by simp [Fin.sum_univ_two]⟩

theorem twoFirmEconomy_noFreeLunch : NoFreeLunch twoFirmEconomy.aggProd := by
  intro z hz h0
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_twoFirmEconomy_aggProd hz
  simp only [linearSet, capSet, mem_ofPred_eq] at ha hb
  have e0 := h0 0
  have e1 := h0 1
  simp only [Pi.zero_apply, Pi.add_apply] at e0 e1
  have ha0 : a 0 = 0 := by linarith [ha.1, hb.1]
  have hb0 : b 0 = 0 := by linarith [ha.1, hb.1]
  have h1 : a 1 + b 1 = 0 := by linarith [ha.2, hb.2.1]
  funext i; fin_cases i <;> simp [ha0, hb0, h1]

theorem twoFirmEconomy_irreversible : Irreversible twoFirmEconomy.aggProd := by
  intro z hz hnz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_twoFirmEconomy_aggProd hz
  obtain ⟨c, hc, d, hd, hcd⟩ := mem_twoFirmEconomy_aggProd hnz
  simp only [linearSet, capSet, mem_ofPred_eq] at ha hb hc hd
  have k0 := congrFun hcd 0
  have k1 := congrFun hcd 1
  simp only [Pi.neg_apply, Pi.add_apply] at k0 k1
  have ha0 : a 0 = 0 := by linarith [ha.1, hb.1, hc.1, hd.1]
  have hb0 : b 0 = 0 := by linarith [ha.1, hb.1, hc.1, hd.1]
  have hc0 : c 0 = 0 := by linarith [ha.1, hb.1, hc.1, hd.1]
  have hd0 : d 0 = 0 := by linarith [ha.1, hb.1, hc.1, hd.1]
  have h1 : a 1 + b 1 = 0 := by
    linarith [ha.2, hb.2.1, hc.2, hd.2.1]
  funext i; fin_cases i <;> simp [ha0, hb0, h1]

/-- The aggregate technology is strictly larger than either firm's: `(-2, 3)`
needs both firms. -/
theorem twoFirmEconomy_aggProd_ne :
    ![-2, 3] ∈ twoFirmEconomy.aggProd ∧ ![-2, 3] ∉ linearSet ∧ ![-2, 3] ∉ capSet := by
  refine ⟨⟨![![-1, 1], ![-1, 2]] , fun j => ?_, ?_⟩, ?_, ?_⟩
  · fin_cases j <;> simp [twoFirmEconomy, linearSet, capSet]
  · funext i; fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  · simp [linearSet]; norm_num
  · simp [capSet]; norm_num

/-- The capacity-constrained firm earns **positive profit** at equal prices, so
ownership shares affect wealth. -/
theorem capSet_positive_profit : ![(-1 : ℝ), 2] ∈ capSet ∧ cost ![1, 1] ![(-1 : ℝ), 2] = 1 := by
  refine ⟨by simp [capSet], by simp [cost, Fin.sum_univ_two]; norm_num⟩

/-- **Existence with two different firms.** (Only existence is claimed.) -/
theorem twoFirmEconomy_exists_equilibrium :
    ∃ p x y, PositivePrices p ∧ twoFirmEconomy.IsWalrasianEquilibrium p x y := by
  refine twoFirmEconomy.exists_walrasianEquilibrium_arrowDebreu (u := fun _ => uSqrt)
    (fun _ => rfl) (fun _ => continuous_uSqrt) (fun _ => strictlyQuasiconcave_uSqrt)
    (fun _ => stronglyMonotone_uSqrt) (fun _ _ => by simp [twoFirmEconomy])
    (fun j => ?_) (fun j => ?_) (fun j => ?_) twoFirmEconomy_noFreeLunch
    twoFirmEconomy_irreversible
  · by_cases h : j = 0 <;> simp [twoFirmEconomy, h, zero_mem_linearSet, zero_mem_capSet]
  · by_cases h : j = 0 <;> simp [twoFirmEconomy, h, isClosed_linearSet, isClosed_capSet]
  · by_cases h : j = 0 <;> simp [twoFirmEconomy, h, convex_linearSet, convex_capSet]

end GEExamples
end Econ
