/-
# Adverse selection with gains from trade: equilibria are inefficient (Akerlof; MWG 13.B)

MWG §13.B (Example 13.B.1 and Prop. 13.B.1); Akerlof (1970). As in `Information/Lemons`, car
quality `θ` has distribution `F` and buyers value a car of quality `θ` at `θ`, but a seller now
values her car at `r θ`, with `r` nondecreasing. Typically `r θ < θ`: every car should trade.
At price `p` exactly the sellers with `r θ ≤ p` offer their cars, and a **competitive
equilibrium with trade** is a price with a positive mass of cars offered and
`p = E[θ | r θ ≤ p]` (`IsLemonsEqR`).

* `lemonsEqR_price_le_mean`: the equilibrium price is at most the mean quality, because the
  cars on offer are the bottom of the quality distribution.
* `lemonsEqR_withheld`: hence every car whose seller values it above the mean quality,
  `r θ > E[θ]`, is withheld in **every** equilibrium with trade; if also `θ > r θ`, the gains
  from trading that car are lost (the inefficiency behind MWG Prop. 13.B.1). The condition
  `r θ > E[θ]` is sufficient, not necessary.
* Witness: qualities `1` and `2` with probability `1/2`, `r θ = 0.9 θ`: `p = 1` is an
  equilibrium in which the good cars (worth `2` to buyers and `1.8` to sellers) do not trade.

Not formalized: existence of an equilibrium in general, the no-trade equilibrium, and a
formal Pareto comparison with allocations that are not competitive equilibria.
-/
module

public import EconLean.Information.Lemons

@[expose] public section

namespace Econ

open Finset SimpleLottery

/-- Probability that a car is offered at price `p`: its seller's value is at most `p`. -/
noncomputable def offeredMassR (F : SimpleLottery) (r : ℝ → ℝ) (p : ℝ) : ℝ :=
  F.expect fun x => if r x ≤ p then 1 else 0

/-- `E[θ · 1{r θ ≤ p}]`, the total quality offered at price `p`. -/
noncomputable def offeredQualityR (F : SimpleLottery) (r : ℝ → ℝ) (p : ℝ) : ℝ :=
  F.expect fun x => if r x ≤ p then x else 0

/-- **Competitive equilibrium with trade** when sellers value quality `θ` at `r θ`. -/
def IsLemonsEqR (F : SimpleLottery) (r : ℝ → ℝ) (p : ℝ) : Prop :=
  0 < offeredMassR F r p ∧ offeredQualityR F r p = p * offeredMassR F r p

/-- **The equilibrium price is at most the mean quality**: with `r` nondecreasing, the cars on
offer are a lower set of qualities, so their average is at most the overall average. -/
theorem lemonsEqR_price_le_mean {F : SimpleLottery} {r : ℝ → ℝ} (hr : Monotone r) {p : ℝ}
    (h : IsLemonsEqR F r p) : p ≤ F.mean := by
  classical
  obtain ⟨hpos, heq⟩ := h
  set S := F.prob.support
  set L := S.filter fun x => r x ≤ p
  set H := S.filter fun x => ¬ r x ≤ p
  have hmL : offeredMassR F r p = ∑ x ∈ L, F.prob x := by
    simp only [offeredMassR, expect_eq_sum]
    rw [sum_filter]; exact sum_congr rfl fun x _ => by split_ifs <;> simp
  have hLne : L.Nonempty := by
    by_contra hL
    rw [not_nonempty_iff_eq_empty] at hL
    rw [hmL, hL, sum_empty] at hpos
    exact lt_irrefl _ hpos
  set c := L.max' hLne
  have hLc : ∀ x ∈ L, x ≤ c := fun x hx => le_max' L x hx
  have hHc : ∀ x ∈ H, c < x := fun x hx => by
    obtain ⟨hxS, hx⟩ := mem_filter.1 hx
    by_contra hle; push Not at hle
    exact hx ((hr hle).trans (mem_filter.1 (max'_mem L hLne)).2)
  -- split the sums over offered (`L`) and withheld (`H`) qualities
  have split : ∀ g : ℝ → ℝ, ∑ x ∈ S, F.prob x * g x =
      ∑ x ∈ L, F.prob x * g x + ∑ x ∈ H, F.prob x * g x := fun g =>
    (sum_filter_add_sum_filter_not S (fun x => r x ≤ p) _).symm
  have hQL : offeredQualityR F r p = ∑ x ∈ L, F.prob x * x := by
    simp only [offeredQualityR, expect_eq_sum]
    rw [sum_filter]; exact sum_congr rfl fun x _ => by split_ifs <;> simp
  have hone : ∑ x ∈ L, F.prob x + ∑ x ∈ H, F.prob x = 1 := by
    have := split (fun _ => 1); simp only [mul_one] at this; rw [← this]; exact F.sum_prob
  have hmean : F.mean = ∑ x ∈ L, F.prob x * x + ∑ x ∈ H, F.prob x * x := by
    have := split id; simp only [id] at this; rw [← this]; rfl
  set mL := ∑ x ∈ L, F.prob x
  set mH := ∑ x ∈ H, F.prob x
  set QL := ∑ x ∈ L, F.prob x * x
  set QH := ∑ x ∈ H, F.prob x * x
  have h1 : QL ≤ c * mL := by
    rw [mul_sum]; exact sum_le_sum fun x hx => by
      rw [mul_comm c]; exact mul_le_mul_of_nonneg_left (hLc x hx) (F.nonneg x)
  have h2 : c * mH ≤ QH := by
    rw [mul_sum]; exact sum_le_sum fun x hx => by
      rw [mul_comm c]; exact mul_le_mul_of_nonneg_left (hHc x hx).le (F.nonneg x)
  have hmH : 0 ≤ mH := sum_nonneg fun x _ => F.nonneg x
  rw [hmL] at hpos
  rw [hQL, hmL] at heq
  -- `E · mL − QL = QH mL − QL mH ≥ c mH mL − c mL mH = 0`
  have key : QL ≤ F.mean * mL := by
    rw [hmean]
    have : (QL + QH) * mL - QL = QH * mL - QL * mH := by
      have : QL = QL * (mL + mH) := by rw [hone, mul_one]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hpos.le, mul_le_mul_of_nonneg_right h1 hmH]
  rw [heq] at key
  exact le_of_mul_le_mul_right key hpos

/-- **Good cars are withheld** (cf. MWG Prop. 13.B.1): in every competitive equilibrium with
trade, a car whose seller values it above the mean quality is not offered. If also `r θ < θ`
and `θ` is in the support, the surplus `θ − r θ > 0` from trading that car is lost. -/
theorem lemonsEqR_withheld {F : SimpleLottery} {r : ℝ → ℝ} (hr : Monotone r) {p : ℝ}
    (h : IsLemonsEqR F r p) {θ : ℝ} (hθ : F.mean < r θ) : p < r θ :=
  (lemonsEqR_price_le_mean hr h).trans_lt hθ

/-! ### Witness -/

/-- Qualities `1` and `2`, each with probability `1/2`. -/
noncomputable def lemonsWitness : SimpleLottery :=
  twoPoint 1 2 (1 / 2) (by norm_num) (by norm_num)

example : IsLemonsEqR lemonsWitness (fun x => 9 / 10 * x) 1 ∧
    lemonsWitness.mean < 9 / 10 * 2 ∧ 9 / 10 * 2 < (2 : ℝ) := by
  refine ⟨⟨?_, ?_⟩, ?_, by norm_num⟩
  · simp only [offeredMassR, lemonsWitness, expect_twoPoint]; norm_num
  · simp only [offeredQualityR, offeredMassR, lemonsWitness, expect_twoPoint]; norm_num
  · simp only [mean, lemonsWitness, expect_twoPoint, id]; norm_num

end Econ
