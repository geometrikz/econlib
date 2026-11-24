/-
# Cobb–Douglas consumers: existence of equilibrium for every exponent

PLAN.md §1 (M4). MWG Example 3.D.1, Prop. 17.C.1; review finding 3 of
`Audit/REVIEW-existence-regular.md`.

The Cobb–Douglas utility `u(x) = ∏ᵢ xᵢ^{αᵢ}` with all `αᵢ > 0` is the textbook
consumer that is *not* strongly monotone: it is `0` on the whole boundary of the
orthant. We prove it is `InteriorRegular` for **every** positive exponent vector
(`interiorRegular_cobbDouglas`), so every exchange economy of Cobb–Douglas
consumers with a strictly positive aggregate endowment has a Walrasian
equilibrium at strictly positive prices, even if some consumers own nothing
(`exists_walrasianEquilibrium_cobbDouglas`).

The proof works through logarithms: on the interior
`u(x) = exp (∑ᵢ αᵢ log xᵢ)`, and `∑ᵢ αᵢ log xᵢ` is strictly increasing and
strictly concave there.
-/
module

public import EconLean.GE.ExistenceRegular
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

namespace Econ

open Real Finset

variable {ι : Type*} [Fintype ι]

/-- The **Cobb–Douglas utility** with exponents `α`: `u(x) = ∏ᵢ xᵢ^{αᵢ}`. -/
noncomputable def cobbDouglas (α : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, x i ^ α i

/-- The log form on the interior. -/
noncomputable def logCobbDouglas (α : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, α i * log (x i)

theorem cobbDouglas_eq_exp (α : ι → ℝ) {x : ι → ℝ} (hx : PositivePrices x) :
    cobbDouglas α x = exp (logCobbDouglas α x) := by
  unfold cobbDouglas logCobbDouglas
  rw [exp_sum]
  refine prod_congr rfl fun i _ => ?_
  rw [rpow_def_of_pos (hx i), mul_comm]

theorem continuous_cobbDouglas {α : ι → ℝ} (hα : ∀ i, 0 < α i) :
    Continuous (cobbDouglas α) := by
  unfold cobbDouglas
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_apply i).rpow_const fun _ => Or.inr (hα i).le

theorem logCobbDouglas_strictMono {α : ι → ℝ} (hα : ∀ i, 0 < α i) {x y : ι → ℝ}
    (hx : PositivePrices x) (hxy : x ≤ y) (hne : x ≠ y) :
    logCobbDouglas α x < logCobbDouglas α y := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra h; push Not at h; exact hne (funext h)
  refine sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ j, ?_⟩
  · exact mul_le_mul_of_nonneg_left (log_le_log (hx i) (hxy i)) (hα i).le
  · exact mul_lt_mul_of_pos_left (log_lt_log (hx j) (lt_of_le_of_ne (hxy j) hj)) (hα j)

theorem logCobbDouglas_strictConcave {α : ι → ℝ} (hα : ∀ i, 0 < α i) {x y : ι → ℝ}
    (hx : PositivePrices x) (hy : PositivePrices y) (hne : x ≠ y) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    t * logCobbDouglas α x + (1 - t) * logCobbDouglas α y <
      logCobbDouglas α (t • x + (1 - t) • y) := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra h; push Not at h; exact hne (funext h)
  unfold logCobbDouglas
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ j, ?_⟩
  · have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (hx i)) (Set.mem_Ioi.2 (hy i))
      ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    simp only [smul_eq_mul] at hc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hα i]
  · have hc := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 (hx j)) (Set.mem_Ioi.2 (hy j)) hj
      ht0 (by linarith : (0 : ℝ) < 1 - t) (by ring)
    simp only [smul_eq_mul] at hc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hα j]

omit [Fintype ι] in
theorem positive_combo {x y : ι → ℝ} (hx : PositivePrices x) (hy : PositivePrices y) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : PositivePrices (t • x + (1 - t) • y) := fun i => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := hx i; have := hy i
  have : 0 < 1 - t := by linarith
  positivity

/-- **Every Cobb–Douglas utility with positive exponents is interior-regular.** -/
theorem interiorRegular_cobbDouglas {α : ι → ℝ} (hα : ∀ i, 0 < α i) :
    InteriorRegular (cobbDouglas α) where
  cont := continuous_cobbDouglas hα
  mono x y hx hxy hne := by
    have hy : PositivePrices y := fun i => (hx i).trans_le (hxy i)
    rw [cobbDouglas_eq_exp α hx, cobbDouglas_eq_exp α hy]
    exact exp_lt_exp.2 (logCobbDouglas_strictMono hα hx hxy hne)
  sqc x y hx hy hne t ht0 ht1 := by
    rw [cobbDouglas_eq_exp α hx, cobbDouglas_eq_exp α hy,
      cobbDouglas_eq_exp α (positive_combo hx hy ht0 ht1)]
    have h := logCobbDouglas_strictConcave hα hx hy hne ht0 ht1
    rcases le_total (logCobbDouglas α x) (logCobbDouglas α y) with h' | h'
    · rw [min_eq_left (exp_le_exp.2 h'), exp_lt_exp]; nlinarith
    · rw [min_eq_right (exp_le_exp.2 h'), exp_lt_exp]; nlinarith
  boundary x y _ hi hy := by
    obtain ⟨i, hi⟩ := hi
    have h0 : cobbDouglas α x = 0 := by
      unfold cobbDouglas
      exact prod_eq_zero (mem_univ i) (by rw [hi, zero_rpow (hα i).ne'])
    rw [h0, cobbDouglas_eq_exp α hy]
    exact exp_pos _

/-! ### Cobb–Douglas demand (MWG Example 3.D.1) -/

/-- The **Cobb–Douglas demand**: good `i` gets the share `αᵢ / ∑ⱼ αⱼ` of wealth,
`xᵢ = αᵢ w / ((∑ⱼ αⱼ) pᵢ)`. MWG Example 3.D.1 normalizes the exponents to sum
to one; raising `u` to the power `1/∑ⱼ αⱼ` is a strictly increasing transform,
so the demand is the same. -/
noncomputable def cdDemand (α p : ι → ℝ) (w : ℝ) : ι → ℝ := fun i => α i * w / ((∑ j, α j) * p i)

theorem cost_cdDemand {α p : ι → ℝ} (hα : ∀ i, 0 < α i) (hp : PositivePrices p) [Nonempty ι]
    (w : ℝ) : cost p (cdDemand α p w) = w := by
  have hA : 0 < ∑ j, α j := sum_pos (fun j _ => hα j) univ_nonempty
  unfold cost cdDemand
  have : ∀ i, p i * (α i * w / ((∑ j, α j) * p i)) = α i * w / ∑ j, α j := fun i => by
    field_simp [(hp i).ne', hA.ne']
  simp only [this, ← sum_div, ← sum_mul]
  field_simp [hA.ne']

/-- **Cobb–Douglas demand formula** (MWG Example 3.D.1). At prices `p ≫ 0` and
wealth `w > 0`, demand is exactly `{cdDemand α p w}`. -/
theorem demand_cobbDouglas [Nonempty ι] {α p : ι → ℝ} (hα : ∀ i, 0 < α i) (hp : PositivePrices p)
    {w : ℝ} (hw : 0 < w) : demand (prefOf (cobbDouglas α)) p w = {cdDemand α p w} := by
  have hA : 0 < ∑ j, α j := sum_pos (fun j _ => hα j) univ_nonempty
  have hxpos : PositivePrices (cdDemand α p w) := fun i => by
    unfold cdDemand; have := hα i; have := hp i; positivity
  have hmem : cdDemand α p w ∈ demand (prefOf (cobbDouglas α)) p w := by
    refine ⟨⟨fun i => (hxpos i).le, (cost_cdDemand hα hp w).le⟩, fun y hy => ?_⟩
    show cobbDouglas α y ≤ cobbDouglas α (cdDemand α p w)
    by_cases hb : ∃ i, y i = 0
    · exact ((interiorRegular_cobbDouglas hα).boundary y _ hy.1 hb hxpos).le
    push Not at hb
    have hypos : PositivePrices y := fun i => lt_of_le_of_ne (hy.1 i) (hb i).symm
    rw [cobbDouglas_eq_exp α hypos, cobbDouglas_eq_exp α hxpos, exp_le_exp]
    -- `log t ≤ t − 1` termwise.
    have key : ∀ i, α i * log (y i) - α i * log (cdDemand α p w i) ≤
        α i * (y i / cdDemand α p w i - 1) := fun i => by
      rw [← mul_sub, ← log_div (hypos i).ne' (hxpos i).ne']
      exact mul_le_mul_of_nonneg_left
        (log_le_sub_one_of_pos (div_pos (hypos i) (hxpos i))) (hα i).le
    have hterm : ∀ i, α i * (y i / cdDemand α p w i - 1) =
        (∑ j, α j) / w * (p i * y i) - α i := fun i => by
      unfold cdDemand
      field_simp [(hα i).ne', (hp i).ne', hw.ne', hA.ne']
    have hsum : ∑ i, (α i * log (y i) - α i * log (cdDemand α p w i)) ≤
        (∑ j, α j) / w * cost p y - ∑ j, α j := by
      calc _ ≤ ∑ i, α i * (y i / cdDemand α p w i - 1) := sum_le_sum fun i _ => key i
        _ = _ := by simp only [hterm, sum_sub_distrib, ← mul_sum, cost]
    have hc : (∑ j, α j) / w * cost p y ≤ ∑ j, α j := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hw]
      exact mul_le_mul_of_nonneg_left hy.2 hA.le
    unfold logCobbDouglas
    rw [sum_sub_distrib] at hsum
    linarith
  ext x
  refine ⟨fun hx => ?_, fun hx => by rw [hx]; exact hmem⟩
  exact (regularUtility_of_interiorRegular (interiorRegular_cobbDouglas hα)).unique p w hp hw
    hx hmem

namespace ExchangeEconomy

variable {α : Type*} [Fintype α]

/-- **Existence for Cobb–Douglas economies.** If every consumer has a
Cobb–Douglas utility with strictly positive exponents and the aggregate
endowment is strictly positive, a Walrasian equilibrium with `p ≫ 0` exists.
Individual endowments may be zero. -/
theorem exists_walrasianEquilibrium_cobbDouglas [Nonempty ι] (E : ExchangeEconomy α ι)
    {β : α → ι → ℝ} (hβ : ∀ a i, 0 < β a i) (hpref : ∀ a, E.pref a = prefOf (cobbDouglas (β a)))
    (hω : PositivePrices E.totalEndowment) :
    ∃ p x, PositivePrices p ∧ E.IsWalrasianEquilibrium p x :=
  E.exists_walrasianEquilibrium_of_interiorRegular hpref
    (fun a => interiorRegular_cobbDouglas (hβ a)) hω

end ExchangeEconomy

namespace GEExamples

/-- Witness: an asymmetric Cobb–Douglas economy. Consumer `0` has exponents
`(1/3, 2/3)` and owns `(1, 0)`; consumer `1` has exponents `(3, 1)` and owns
`(0, 1)`. Neither endowment is interior, so both consumers must trade. -/
noncomputable def cd2Economy : ExchangeEconomy (Fin 2) (Fin 2) where
  pref a := prefOf (cobbDouglas (if a = 0 then ![1 / 3, 2 / 3] else ![3, 1]))
  endow a := fun i => if a = i then 1 else 0
  endow_nonneg a i := by simp only [Pi.zero_apply]; split_ifs <;> norm_num

theorem cd2Economy_exists_equilibrium :
    ∃ p x, PositivePrices p ∧ cd2Economy.IsWalrasianEquilibrium p x := by
  refine cd2Economy.exists_walrasianEquilibrium_cobbDouglas
    (β := fun a => if a = 0 then ![1 / 3, 2 / 3] else ![3, 1]) (fun a i => ?_) (fun a => rfl) ?_
  · by_cases h : a = 0 <;> fin_cases i <;> simp [h]
  · intro i
    fin_cases i <;> simp [ExchangeEconomy.totalEndowment, cd2Economy]

/-- **Hand-computed equilibrium of `cd2Economy`** (check against the demand
formula, MWG Example 3.D.1): prices `(1, 8/9)`; consumer `0` gets `(1/3, 3/4)`
and consumer `1` gets `(2/3, 1/4)`. This is the unique equilibrium up to price
scaling: with `p₀ = 1`, clearing good `0` forces `1/3 + (3/4) p₁ = 1`. -/
theorem cd2Economy_equilibrium :
    cd2Economy.IsWalrasianEquilibrium ![1, 8 / 9] ![![1 / 3, 3 / 4], ![2 / 3, 1 / 4]] := by
  have hp : PositivePrices (![1, 8 / 9] : Fin 2 → ℝ) := fun i => by fin_cases i <;> norm_num
  have h0 : (![![1 / 3, 3 / 4], ![2 / 3, 1 / 4]] : Fin 2 → Fin 2 → ℝ) 0 ∈
      demand (cd2Economy.pref 0) ![1, 8 / 9] (cd2Economy.wealth ![1, 8 / 9] 0) := by
    have hα : ∀ i, 0 < (![1 / 3, 2 / 3] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> norm_num
    have hw : cd2Economy.wealth ![1, 8 / 9] 0 = 1 := by
      simp [ExchangeEconomy.wealth, cd2Economy, cost]
    have hpref : cd2Economy.pref 0 = prefOf (cobbDouglas ![1 / 3, 2 / 3]) := by simp [cd2Economy]
    rw [hpref, hw, demand_cobbDouglas hα hp one_pos, Set.mem_singleton_iff]
    funext i; fin_cases i <;> simp [cdDemand, Fin.sum_univ_two] <;> norm_num
  have h1 : (![![1 / 3, 3 / 4], ![2 / 3, 1 / 4]] : Fin 2 → Fin 2 → ℝ) 1 ∈
      demand (cd2Economy.pref 1) ![1, 8 / 9] (cd2Economy.wealth ![1, 8 / 9] 1) := by
    have hα : ∀ i, 0 < (![3, 1] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> norm_num
    have hw : cd2Economy.wealth ![1, 8 / 9] 1 = 8 / 9 := by
      simp [ExchangeEconomy.wealth, cd2Economy, cost]
    have hpref : cd2Economy.pref 1 = prefOf (cobbDouglas ![3, 1]) := by simp [cd2Economy]
    rw [hpref, hw, demand_cobbDouglas hα hp (by norm_num), Set.mem_singleton_iff]
    funext i; fin_cases i <;> simp [cdDemand, Fin.sum_univ_two] <;> norm_num
  refine ⟨fun a => ?_, ?_⟩
  · fin_cases a
    · exact h0
    · exact h1
  · funext i
    fin_cases i <;> simp [ExchangeEconomy.totalEndowment, cd2Economy, Fin.sum_univ_two] <;> norm_num

end GEExamples

end Econ
