/-
# Swap regret

References. A. Blum and Y. Mansour (2007), "From External to Internal
Regret", *JMLR* 8, §2 (swap regret); N. Cesa-Bianchi and G. Lugosi (2006),
*Prediction, Learning, and Games*, §4.4; S. Hart and A. Mas-Colell (2000).

The **swap regret** of a player for a *swap function* `φ : Sᵢ → Sᵢ` is the
gain it would have had by replacing every action `j` it played with `φ(j)`.
For a distribution `μ` over pure profiles (`swapGain`) it is
`Σ_s μ(s) (uᵢ(φ(sᵢ), s₋ᵢ) − uᵢ(s))`. Conditional (internal) regret is the
special case of a swap function that moves a single action.

**Results.**
* `swapGain_eq_sum`: the swap gain of `φ` is the sum over `j` of the
  obedience gains of `j → φ(j)` (so, informally, swap regret is at most `|Sᵢ|`
  times the largest conditional regret; not stated separately).
* `isCorrelatedEq_iff_swap`: `μ` is a correlated equilibrium iff no player
  has a profitable swap function (a folklore equivalence, used by Blum–Mansour).
* `swapRegret_eq`, `swapGain_condAvg_le`: under conditional regret matching on
  expected payoffs (`ConditionalRegret.lean`), the cumulative swap regret of
  every swap function equals `T` times its swap gain under the average play,
  which is at most `2B |Sᵢ|² / √T`; `eventually_swapGain_le`: so for every
  `ε > 0` all swap gains are eventually below `ε`, uniformly over swap
  functions.

Blum and Mansour's generic reduction (any external-regret algorithm run once
per action, combined through a stationary distribution, has `O(√(T |S| log |S|))`
swap regret) is not formalized; the bound here is for conditional regret
matching, whose rule is the same stationary-distribution step.
-/
module

public import EconLean.BoundedRationality.ConditionalRegret

@[expose] public section

noncomputable section

namespace Econ

namespace RegretMatching

open Function Finset Filter Topology NoRegret

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- **Swap gain** of player `i` from the swap function `φ` under `μ`. -/
def swapGain (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I) (φ : S i → S i) : ℝ :=
  ∑ s, μ s * (u i (update s i (φ (s i))) - u i s)

/-- The swap gain is the sum of the obedience gains `j → φ(j)`. -/
theorem swapGain_eq_sum (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I)
    (φ : S i → S i) : swapGain u μ i φ = ∑ j, obedienceGain u μ i j (φ j) := by
  simp only [obedienceGain]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_ite_eq]
  simp

theorem obedienceGain_self (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I) (j : S i) :
    obedienceGain u μ i j j = 0 := by
  simp only [obedienceGain]
  refine sum_eq_zero fun s _ => ?_
  split_ifs with h
  · rw [← h, update_eq_self, sub_self, mul_zero]
  · rfl

/-- **Correlated equilibrium = no profitable swap.** -/
theorem isCorrelatedEq_iff_swap (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) :
    IsCorrelatedEq u μ ↔ μ ∈ lotteries (∀ j, S j) ∧ ∀ i φ, swapGain u μ i φ ≤ 0 := by
  constructor
  · rintro ⟨hμ, h⟩
    exact ⟨hμ, fun i φ => by
      rw [swapGain_eq_sum]; exact sum_nonpos fun j _ => h i j (φ j)⟩
  · rintro ⟨hμ, h⟩
    refine ⟨hμ, fun i t t' => ?_⟩
    have := h i (fun x => if x = t then t' else x)
    rw [swapGain_eq_sum, ← add_sum_erase _ _ (mem_univ t), ite_eq_left rfl,
      sum_eq_zero (fun j hj => by
        rw [ite_eq_right (ne_of_mem_erase hj)]; exact obedienceGain_self u μ i j), add_zero] at this
    exact this

variable [∀ i, Nonempty (S i)]

/-- Cumulative swap regret of player `i` for `φ` under conditional regret
matching on expected payoffs. -/
def swapRegret (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (φ : S i → S i) : ℝ :=
  ∑ t ∈ range T, ∑ j, condPlay u t i j *
    (pureDev u (condPlay u t) i (φ j) - pureDev u (condPlay u t) i j)

theorem swapRegret_eq (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (φ : S i → S i) :
    swapRegret u T i φ = T * swapGain u (condAvg u T) i φ := by
  have h : ∀ T, swapRegret u T i φ = ∑ j, condRegrets u T i j (φ j) := by
    intro T
    induction T with
    | zero => simp [swapRegret, condRegrets]
    | succ T ih =>
      rw [swapRegret, sum_range_succ, ← swapRegret, ih, ← sum_add_distrib]
      rfl
  rw [h, swapGain_eq_sum, mul_sum]
  exact sum_congr rfl fun j _ => condRegrets_eq u T i j (φ j)

/-- **Swap regret bound** for conditional regret matching. -/
theorem swapGain_condAvg_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {T : ℕ} (hT : 0 < T) (i : I) (φ : S i → S i) :
    swapGain u (condAvg u T) i φ ≤ 2 * B * Fintype.card (S i) ^ 2 / Real.sqrt T := by
  rw [swapGain_eq_sum]
  calc ∑ j, obedienceGain u (condAvg u T) i j (φ j)
      ≤ ∑ _j : S i, 2 * B * Fintype.card (S i) / Real.sqrt T :=
        sum_le_sum fun j _ => obedienceGain_condAvg_le u hB hT i j (φ j)
    _ = 2 * B * Fintype.card (S i) ^ 2 / Real.sqrt T := by
        rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- **Vanishing swap regret**: for every `ε > 0`, eventually every swap gain
of every player under the average play is at most `ε`. -/
theorem eventually_swapGain_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ i (φ : S i → S i), swapGain u (condAvg u T) i φ ≤ ε := by
  have hlim : ∀ i : I, Tendsto (fun T : ℕ => 2 * B * Fintype.card (S i) ^ 2 / Real.sqrt T)
      atTop (𝓝 0) := fun i =>
    tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
  have hev : ∀ i : I, ∀ᶠ T : ℕ in atTop, 2 * B * Fintype.card (S i) ^ 2 / Real.sqrt T < ε :=
    fun i => (hlim i).eventually (gt_mem_nhds hε)
  filter_upwards [(eventually_all.2 hev).and (eventually_gt_atTop 0)] with T ⟨hT, hpos⟩
  exact fun i φ => (swapGain_condAvg_le u hB hpos i φ).trans (hT i).le

end RegretMatching

end Econ
