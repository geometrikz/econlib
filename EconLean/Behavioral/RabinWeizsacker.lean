/-
# Narrow bracketing and dominated choices (Rabin–Weizsäcker)

Reference. M. Rabin and G. Weizsäcker (2009), "Narrow Bracketing and
Dominated Choices", *AER* 99(4), §I (Proposition 1 and its converse for
CARA).

An expected-utility agent with utility `u` faces two concurrent decisions,
each between a finite lottery `zₖ` (probabilities `p`, outcomes `zₖ(i)`) and a
sure amount `sₖ`. A **narrow bracketer** decides each one in isolation:
lottery if `E u(zₖ) > u(sₖ)`, sure amount if `u(sₖ) > E u(zₖ)`.

`NarrowDominated u p` says that there are two such decisions in which the
second lottery is the first shifted by a constant `c`, the narrow bracketer
strictly picks the lottery in one decision and the sure amount in the other
(`p` is a probability vector),
and the resulting combination is **state-wise strictly dominated** by the
opposite combination (every outcome is lower by `δ > 0`;
`combined_dominated`), so every broad bracketer with strictly increasing
utility, whatever its risk attitude, prefers the opposite combination
(`broad_prefers`).

`WealthEffect u p` says that adding wealth `w` reverses a strict comparison
between a lottery with probabilities `p` and a sure amount: risk attitudes
depend on wealth.

**Results.**
* `narrowDominated_of_wealthEffect` (Rabin–Weizsäcker Proposition 1, in this
  form): if `u` is continuous and has a wealth effect,
  then a narrow bracketer makes a dominated combined choice.
* `cara_not_narrowDominated`, `caraLove_not_narrowDominated`,
  `linear_not_narrowDominated` (their converse): risk-averse CARA
  `−exp(−αx)`, risk-loving CARA `exp(βx)` (`α, β > 0`) and increasing linear
  utility never do (positive affine transforms are not stated separately).
* `kink_wealthEffect`, `kink_narrowDominated`: a utility with a kink at `0`
  (slope `1` on losses, `1/2` on gains) has a wealth effect for a fair coin,
  so narrow bracketing leads it to a dominated choice.

Rabin–Weizsäcker state the hypothesis as "not CARA". Here the hypothesis is
the wealth effect itself (a strict reversal, for the given probability
vector `p`), and the main theorem needs only continuity of `u`. For the fair
coin, `CARACharacterization.lean` shows that a continuous strictly
increasing utility without wealth effects is CARA or linear, which gives the
full "iff not CARA" statement (`rabinWeizsacker`).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

noncomputable section

namespace Econ

namespace Bracketing

open Finset Filter Topology

variable {n : ℕ}

/-- Expected utility of the lottery with probabilities `p` and outcomes `z`. -/
def EU (u : ℝ → ℝ) (p : Fin n → ℝ) (z : Fin n → ℝ) : ℝ := ∑ i, p i * u (z i)

/-- `p` is a probability vector. -/
def IsProb (p : Fin n → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- **Narrow bracketing leads to a dominated combination**: there are two
decisions (lottery `z₁` or sure `s₁`; lottery `z₂ = z₁ + c` or sure `s₂`) in
which the narrow choices combine to an outcome that is `δ` below the opposite
combination in every state. -/
def NarrowDominated (u : ℝ → ℝ) (p : Fin n → ℝ) : Prop :=
  IsProb p ∧ ∃ (z₁ : Fin n → ℝ) (s₁ s₂ c δ : ℝ), 0 < δ ∧
    ((u s₁ < EU u p z₁ ∧ EU u p (fun i => z₁ i + c) < u s₂ ∧ s₂ + δ = s₁ + c) ∨
     (EU u p z₁ < u s₁ ∧ u s₂ < EU u p (fun i => z₁ i + c) ∧ s₁ + c + δ = s₂))

/-- Wealth `w` reverses a strict comparison between the lottery `z` and the
sure amount `s`. -/
def WealthEffect (u : ℝ → ℝ) (p : Fin n → ℝ) : Prop :=
  ∃ (z : Fin n → ℝ) (s w : ℝ),
    (u s < EU u p z ∧ EU u p (fun i => z i + w) < u (s + w)) ∨
    (EU u p z < u s ∧ u (s + w) < EU u p (fun i => z i + w))

/-- In both cases the narrow combination is `δ` below the opposite one in
every state: lottery `z₁` plus sure `s₂` against sure `s₁` plus lottery
`z₁ + c` (first case), and sure `s₁` plus lottery `z₁ + c` against lottery
`z₁` plus sure `s₂` (second case). -/
theorem combined_dominated {z₁ : Fin n → ℝ} {s₁ s₂ c δ : ℝ} :
    (s₂ + δ = s₁ + c → ∀ i, z₁ i + s₂ + δ = s₁ + (z₁ i + c)) ∧
    (s₁ + c + δ = s₂ → ∀ i, s₁ + (z₁ i + c) + δ = z₁ i + s₂) :=
  ⟨fun h i => by linarith, fun h i => by linarith⟩

/-- Every broad bracketer with strictly increasing utility strictly prefers an
outcome that is higher by `δ > 0` in every state of positive probability. -/
theorem broad_prefers {v : ℝ → ℝ} (hv : StrictMono v) {p : Fin n → ℝ} (hp : IsProb p)
    (y : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) : EU v p y < EU v p (fun i => y i + δ) := by
  have hne : ∃ i, 0 < p i := by
    by_contra h
    push Not at h
    have : ∑ i, p i = 0 := sum_eq_zero fun i _ => le_antisymm (h i) (hp.1 i)
    rw [hp.2] at this; norm_num at this
  obtain ⟨i, hi⟩ := hne
  unfold EU
  refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hv (by linarith)).le (hp.1 j))
    ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hv (by linarith)) hi⟩

/-- **Rabin–Weizsäcker Proposition 1**: with a wealth effect, a narrow
bracketer makes a state-wise dominated combined choice. -/
theorem narrowDominated_of_wealthEffect {u : ℝ → ℝ} (hc : Continuous u) {p : Fin n → ℝ}
    (hp : IsProb p) (hw : WealthEffect u p) : NarrowDominated u p := by
  refine ⟨hp, ?_⟩
  obtain ⟨z, s, w, h⟩ := hw
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- lower the second sure amount a little: still preferred to the lottery
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), EU u p (fun i => z i + w) < u (s + w - δ) := by
      have : Tendsto (fun δ => u (s + w - δ)) (𝓝 0) (𝓝 (u (s + w))) := by
        have hc' : Continuous fun δ => u (s + w - δ) := by fun_prop
        simpa using hc'.tendsto 0
      exact this.eventually (lt_mem_nhds h2)
    obtain ⟨δ, hδ, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ ∧ δ ∈ Set.Ioi 0).exists
    exact ⟨z, s, s + w - δ, w, δ, hδ0, Or.inl ⟨h1, hδ, by ring⟩⟩
  · -- raise the second sure amount a little: the lottery is still preferred
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), u (s + w + δ) < EU u p (fun i => z i + w) := by
      have : Tendsto (fun δ => u (s + w + δ)) (𝓝 0) (𝓝 (u (s + w))) := by
        have hc' : Continuous fun δ => u (s + w + δ) := by fun_prop
        simpa using hc'.tendsto 0
      exact this.eventually (gt_mem_nhds h2)
    obtain ⟨δ, hδ, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ ∧ δ ∈ Set.Ioi 0).exists
    exact ⟨z, s, s + w + δ, w, δ, hδ0, Or.inr ⟨h1, hδ, by ring⟩⟩

/-! ### The converse: CARA and linear utility -/

/-- CARA utility with absolute risk aversion `α`. -/
def cara (α : ℝ) (x : ℝ) : ℝ := -Real.exp (-α * x)

theorem EU_cara_shift (α : ℝ) (p : Fin n → ℝ) (z : Fin n → ℝ) (c : ℝ) :
    EU (cara α) p (fun i => z i + c) = Real.exp (-α * c) * EU (cara α) p z := by
  simp only [EU, cara, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show -α * (z i + c) = -α * z i + -α * c by ring, Real.exp_add]; ring

theorem cara_shift (α x c : ℝ) : cara α (x + c) = Real.exp (-α * c) * cara α x := by
  simp only [cara]
  rw [show -α * (x + c) = -α * x + -α * c by ring, Real.exp_add]; ring

theorem cara_strictMono {α : ℝ} (hα : 0 < α) : StrictMono (cara α) := fun a b h => by
  simp only [cara, neg_lt_neg_iff]
  exact Real.exp_lt_exp.2 (by nlinarith)

/-- **CARA agents never make dominated choices by narrow bracketing.** -/
theorem cara_not_narrowDominated {α : ℝ} (hα : 0 < α) (p : Fin n → ℝ) :
    ¬ NarrowDominated (cara α) p := by
  rintro ⟨-, z₁, s₁, s₂, c, δ, hδ, h⟩
  have hmono := cara_strictMono hα
  have he := Real.exp_pos (-α * c)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [EU_cara_shift] at h2
    have : cara α (s₁ + c) < cara α s₂ := by
      rw [cara_shift]; nlinarith
    have := hmono.lt_iff_lt.1 this
    linarith
  · rw [EU_cara_shift] at h2
    have : cara α s₂ < cara α (s₁ + c) := by
      rw [cara_shift]; nlinarith
    have := hmono.lt_iff_lt.1 this
    linarith

/-- Risk-loving CARA utility `exp(βx)`. -/
def caraLove (β : ℝ) (x : ℝ) : ℝ := Real.exp (β * x)

theorem EU_caraLove_shift (β : ℝ) (p : Fin n → ℝ) (z : Fin n → ℝ) (c : ℝ) :
    EU (caraLove β) p (fun i => z i + c) = Real.exp (β * c) * EU (caraLove β) p z := by
  simp only [EU, caraLove, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show β * (z i + c) = β * z i + β * c by ring, Real.exp_add]; ring

/-- **Risk-loving CARA agents never make dominated choices by narrow
bracketing either.** -/
theorem caraLove_not_narrowDominated {β : ℝ} (hβ : 0 < β) (p : Fin n → ℝ) :
    ¬ NarrowDominated (caraLove β) p := by
  rintro ⟨-, z₁, s₁, s₂, c, δ, hδ, h⟩
  have hmono : StrictMono (caraLove β) := fun a b h =>
    Real.exp_lt_exp.2 (by nlinarith)
  have hs : ∀ x, caraLove β (x + c) = Real.exp (β * c) * caraLove β x := fun x => by
    simp only [caraLove]; rw [show β * (x + c) = β * x + β * c by ring, Real.exp_add]; ring
  have he := Real.exp_pos (β * c)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [EU_caraLove_shift] at h2
    have : caraLove β (s₁ + c) < caraLove β s₂ := by rw [hs]; nlinarith
    have := hmono.lt_iff_lt.1 this
    linarith
  · rw [EU_caraLove_shift] at h2
    have : caraLove β s₂ < caraLove β (s₁ + c) := by rw [hs]; nlinarith
    have := hmono.lt_iff_lt.1 this
    linarith

/-- **Risk-neutral agents never make dominated choices by narrow
bracketing** (linear utility with positive slope). -/
theorem linear_not_narrowDominated {a b : ℝ} (ha : 0 < a) {p : Fin n → ℝ} (hp : IsProb p) :
    ¬ NarrowDominated (fun x => a * x + b) p := by
  have hEU : ∀ z : Fin n → ℝ, ∀ c, EU (fun x => a * x + b) p (fun i => z i + c) =
      EU (fun x => a * x + b) p z + a * c := fun z c => by
    simp only [EU]
    rw [show a * c = ∑ i, p i * (a * c) by rw [← sum_mul, hp.2, one_mul], ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rintro ⟨-, z₁, s₁, s₂, c, δ, hδ, h⟩
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [hEU] at h2
    have : a * (s₁ + c) < a * s₂ := by linarith
    have := lt_of_mul_lt_mul_left this ha.le
    linarith
  · rw [hEU] at h2
    have : a * s₂ < a * (s₁ + c) := by linarith
    have := lt_of_mul_lt_mul_left this ha.le
    linarith

/-! ### Example: a kink at zero -/

/-- Slope `1` on losses, `1/2` on gains. -/
def kink (x : ℝ) : ℝ := min x (x / 2)

theorem kink_continuous : Continuous kink := by unfold kink; fun_prop

theorem kink_strictMono : StrictMono kink := fun a b h => by
  simp only [kink]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [min_eq_left (by linarith), min_eq_left (by linarith)]; exact h
  · rw [min_eq_left (by linarith), min_eq_right (by linarith)]; linarith
  · linarith
  · rw [min_eq_right (by linarith), min_eq_right (by linarith)]; linarith

/-- A fair coin. -/
def coin : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem coin_isProb : IsProb coin := ⟨fun i => by fin_cases i <;> simp [coin],
  by simp [coin, Fin.sum_univ_two]; norm_num⟩

/-- The kinked agent rejects `±1` against `−1/10` at zero wealth, but accepts
it against the same amount shifted by `10`. -/
theorem kink_wealthEffect : WealthEffect kink coin := by
  refine ⟨![-1, 1], -1 / 10, 10, Or.inr ⟨?_, ?_⟩⟩ <;>
    simp [EU, coin, kink, Fin.sum_univ_two] <;> norm_num

theorem kink_narrowDominated : NarrowDominated kink coin :=
  narrowDominated_of_wealthEffect kink_continuous coin_isProb kink_wealthEffect

end Bracketing

end Econ
