/-
# Salience and the Allais paradox

Reference. P. Bordalo, N. Gennaioli and A. Shleifer (2012), "Salience Theory
of Choice Under Risk", *QJE* 127(3), §IV (the Allais paradoxes).

Builds on `Salience.lean`. Payoffs are in millions; the numbers are the
classic common-consequence Allais lotteries:

* problem A: `L₁ = 1` for sure versus `L₂ = (5, 0.10; 1, 0.89; 0, 0.01)`;
* problem B: `L₁' = (1, 0.11; 0, 0.89)` versus `L₂' = (5, 0.10; 0, 0.90)`.

**Results.**
* `prefers_common_consequence`: in a correlated presentation (one state space
  for both problems), if the two problems differ only in a state `s₀` in
  which both lotteries of each problem pay the same (a common consequence),
  the salient thinker's choice is the same in both problems, for every `θ`
  and `δ`. Salience has no Allais paradox when the lotteries are presented
  as acts on a common state space.
* `allaisA_safe`: in problem A (whose only joint presentation is the
  three-state one) the salient thinker with `0 < θ < 2/3` and `δ < 1/40`
  strictly prefers the sure `L₁`. The most salient state is "`L₁` pays 1,
  `L₂` pays 0".
* `allaisB_risky`: in problem B with the lotteries independent (four joint
  states, `piB_product`), the same agent strictly prefers `L₂'`, for every
  `δ`. The most salient state is now "`L₁'` pays 0, `L₂'` pays 5".
  `allaisA_sum`, `allaisB_sum` give the distorted expected differences in
  closed form, from the salience rankings `ranks_A`, `ranks_Bi`.
* `allais_paradox`: hence for `0 < θ < 2/3` and `δ < 1/40` the salient
  thinker shows the Allais choice pattern (`L₁` over `L₂`, `L₂'` over `L₁'`),
  which no expected-utility maximizer shows (`eu_no_allais`: for every
  utility `u`, `L₁` beats `L₂` iff `L₁'` beats `L₂'`). `allaisA_eu`: the
  undistorted case `δ = 1` (risk-neutral expected value) picks `L₂` in A.
* `allaisB_correlated_iff`, `allaisB_correlated_iff'`: in the correlated
  presentation of B, weak preference in either direction (hence also strict
  choice) agrees with problem A for every `θ` and `δ`, so the paradox needs
  the lotteries to be independent. `marginals_B`: the joint presentations of
  B have the right marginals (`L₁'` pays 1 with probability `0.11`, `L₂'`
  pays 5 with probability `0.10`).

**Scope.** Only the common-consequence paradox with these numbers is treated;
BGS's general Proposition (conditions on `θ`, `δ` for arbitrary common
consequences) and the common-ratio effect are not formalized. Given
`θ < 2/3`, `δ < 1/40` is exact for problem A (`allaisA_sum`); the case
`θ ≥ 2/3` (where A picks `L₂` for `δ ∈ (0, 1]`) is not formalized. The
results hold for every real `δ` below the stated bounds, including `δ ≤ 0`
outside BGS's range `(0, 1]`.
-/
module

public import EconLean.Behavioral.Salience
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ.Salience

open Finset

/-- Rank as a sum of indicators. -/
theorem rank_eq_sum {ι : Type*} [Fintype ι] (σ : ι → ℝ) (s : ι) :
    rank σ s = ∑ t, if σ s < σ t then 1 else 0 := by
  classical
  unfold rank
  rw [card_filter]

theorem sigma_self (θ c : ℝ) : sigma θ c c = 0 := by simp [sigma]

/-- **Common consequences in a correlated presentation.** If problems `(x, y)`
and `(x', y')` differ only in a state `s₀` in which each problem's two
lotteries pay the same, the salient thinker chooses the same way in both. -/
theorem prefers_common_consequence {ι : Type*} [Fintype ι] [DecidableEq ι] (θ δ : ℝ)
    (π : ι → ℝ) {x y x' y' : ι → ℝ} (s₀ : ι)
    (hx : ∀ s, s ≠ s₀ → x s = x' s) (hy : ∀ s, s ≠ s₀ → y s = y' s)
    (h₀ : x s₀ = y s₀) (h₀' : x' s₀ = y' s₀) :
    Prefers θ δ π x y ↔ Prefers θ δ π x' y' := by
  have hsal : salience θ x y = salience θ x' y' := by
    funext s
    by_cases hs : s = s₀
    · subst hs; simp only [salience, h₀, h₀', sigma_self]
    · simp only [salience, hx s hs, hy s hs]
  have hf : factor θ δ x y = factor θ δ x' y' := by
    funext s; simp only [factor, hsal]
  unfold Prefers
  rw [hf]
  have : ∀ s, π s * factor θ δ x' y' s * (x s - y s) = π s * factor θ δ x' y' s * (x' s - y' s) := by
    intro s
    by_cases hs : s = s₀
    · subst hs; rw [h₀, h₀', sub_self, sub_self]
    · rw [hx s hs, hy s hs]
  simp only [this]

/-! ### The Allais lotteries -/

/-- Problem A on three states: `L₂` pays 5 (prob `0.10`), 1 (`0.89`), 0 (`0.01`). -/
noncomputable def piA : Fin 3 → ℝ := ![1 / 10, 89 / 100, 1 / 100]
def L1 : Fin 3 → ℝ := ![1, 1, 1]
def L2 : Fin 3 → ℝ := ![5, 1, 0]

/-- Problem B, correlated presentation: the common consequence `1` of state
`1` is replaced by `0`. -/
def L1c : Fin 3 → ℝ := ![1, 0, 1]
def L2c : Fin 3 → ℝ := ![5, 0, 0]

/-- Problem B with independent lotteries: joint states
`(L₁', L₂') = (1, 5), (1, 0), (0, 5), (0, 0)`. -/
noncomputable def piB : Fin 4 → ℝ := ![11 / 1000, 99 / 1000, 89 / 1000, 801 / 1000]
def L1i : Fin 4 → ℝ := ![1, 1, 0, 0]
def L2i : Fin 4 → ℝ := ![5, 0, 5, 0]

theorem piA_isFullProb : IsFullProb piA := by
  refine ⟨fun s => ?_, ?_⟩
  · fin_cases s <;> simp [piA]
  · simp [piA, Fin.sum_univ_three]; norm_num

theorem piB_isFullProb : IsFullProb piB := by
  refine ⟨fun s => ?_, ?_⟩
  · fin_cases s <;> simp [piB]
  · simp [piB, Fin.sum_univ_four]; norm_num

/-- `piB` is the product of the marginals `(0.11, 0.89)` and `(0.10, 0.90)`:
the lotteries of problem B are independent. -/
theorem piB_product : piB = ![11 / 100 * (1 / 10), 11 / 100 * (9 / 10),
    89 / 100 * (1 / 10), 89 / 100 * (9 / 10)] := by
  funext s; fin_cases s <;> simp [piB] <;> norm_num

theorem salience_A (θ : ℝ) :
    salience θ L1 L2 = ![4 / (6 + θ), 0, 1 / (1 + θ)] := by
  funext s
  fin_cases s <;> norm_num [salience, sigma, L1, L2]

theorem salience_Bi (θ : ℝ) :
    salience θ L1i L2i = ![4 / (6 + θ), 1 / (1 + θ), 5 / (5 + θ), 0] := by
  funext s
  fin_cases s <;> norm_num [salience, sigma, L1i, L2i]

theorem ranks_A {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) :
    rank (salience θ L1 L2) 0 = 1 ∧ rank (salience θ L1 L2) 1 = 2 ∧
      rank (salience θ L1 L2) 2 = 0 := by
  have ha : (0 : ℝ) < 4 / (6 + θ) := by positivity
  have hab : 4 / (6 + θ) < 1 / (1 + θ) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  have hb : (0 : ℝ) < 1 / (1 + θ) := by positivity
  rw [salience_A]
  generalize 4 / (6 + θ) = a at *
  generalize 1 / (1 + θ) = b at *
  simp [rank_eq_sum, Fin.sum_univ_three, ha, hab, hb, not_lt.2 hab.le, not_lt.2 ha.le,
    not_lt.2 hb.le]

theorem ranks_Bi {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) :
    rank (salience θ L1i L2i) 0 = 2 ∧ rank (salience θ L1i L2i) 1 = 1 ∧
      rank (salience θ L1i L2i) 2 = 0 ∧ rank (salience θ L1i L2i) 3 = 3 := by
  have ha : (0 : ℝ) < 4 / (6 + θ) := by positivity
  have hab : 4 / (6 + θ) < 1 / (1 + θ) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  have hbc : 1 / (1 + θ) < 5 / (5 + θ) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  have hb : (0 : ℝ) < 1 / (1 + θ) := by positivity
  have hc : (0 : ℝ) < 5 / (5 + θ) := by positivity
  have hac := hab.trans hbc
  rw [salience_Bi]
  generalize 4 / (6 + θ) = a at *
  generalize 1 / (1 + θ) = b at *
  generalize 5 / (5 + θ) = c at *
  simp [rank_eq_sum, Fin.sum_univ_four, ha, hab, hb, hbc, hc, hac, not_lt.2 hab.le,
    not_lt.2 ha.le, not_lt.2 hb.le, not_lt.2 hbc.le, not_lt.2 hc.le, not_lt.2 hac.le]

/-- Distorted expected difference `L₁ − L₂` in problem A. -/
theorem allaisA_sum {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (δ : ℝ) :
    ∑ s, piA s * factor θ δ L1 L2 s * (L1 s - L2 s) = 1 / 100 - 4 / 10 * δ := by
  obtain ⟨h0, h1, h2⟩ := ranks_A hθ0 hθ
  simp only [Fin.sum_univ_three, factor, h0, h1, h2]
  simp [piA, L1, L2]
  ring

/-- Distorted expected difference `L₁' − L₂'` in problem B (independent). -/
theorem allaisB_sum {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (δ : ℝ) :
    ∑ s, piB s * factor θ δ L1i L2i s * (L1i s - L2i s) =
      -(44 / 1000) * δ ^ 2 + 99 / 1000 * δ - 445 / 1000 := by
  obtain ⟨h0, h1, h2, h3⟩ := ranks_Bi hθ0 hθ
  simp only [Fin.sum_univ_four, factor, h0, h1, h2, h3]
  simp [piB, L1i, L2i]
  ring

/-- **Problem A**: a strong salience distortion makes the sure `L₁` strictly
preferred. -/
theorem allaisA_safe {θ δ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (hδ : δ < 1 / 40) :
    0 < ∑ s, piA s * factor θ δ L1 L2 s * (L1 s - L2 s) := by
  rw [allaisA_sum hθ0 hθ]; linarith

/-- **Problem B (independent lotteries)**: `L₂'` is strictly preferred, for
every `δ`. -/
theorem allaisB_risky {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (δ : ℝ) :
    ∑ s, piB s * factor θ δ L1i L2i s * (L1i s - L2i s) < 0 := by
  rw [allaisB_sum hθ0 hθ]; nlinarith [sq_nonneg (δ - 99 / 88)]

/-- **The Allais paradox under salience**: for `0 < θ < 2/3` and `δ < 1/40`,
the salient thinker strictly prefers `L₁` to `L₂` and `L₂'` to `L₁'`. -/
theorem allais_paradox {θ δ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (hδ : δ < 1 / 40) :
    0 < ∑ s, piA s * factor θ δ L1 L2 s * (L1 s - L2 s) ∧
      ∑ s, piB s * factor θ δ L1i L2i s * (L1i s - L2i s) < 0 :=
  ⟨allaisA_safe hθ0 hθ hδ, allaisB_risky hθ0 hθ δ⟩

/-- Without distortion (`δ = 1`, expected value) `L₂` is strictly preferred in
problem A. -/
theorem allaisA_eu (θ : ℝ) : ∑ s, piA s * factor θ 1 L1 L2 s * (L1 s - L2 s) < 0 := by
  simp only [factor, one_pow, mul_one, Fin.sum_univ_three]
  norm_num [piA, L1, L2]

/-- **No expected-utility maximizer shows the Allais pattern**: for any
utility `u`, `L₁` beats `L₂` iff `L₁'` beats `L₂'`. -/
theorem eu_no_allais (u : ℝ → ℝ) :
    (∑ s, piA s * u (L2 s) < ∑ s, piA s * u (L1 s)) ↔
      (∑ s, piB s * u (L2i s) < ∑ s, piB s * u (L1i s)) := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_four]
  simp [piA, piB, L1, L2, L1i, L2i]
  constructor <;> intro h <;> linarith

/-- **Correlated presentation of problem B**: the choice is the same as in
problem A, for every `θ` and `δ`. -/
theorem allaisB_correlated_iff (θ δ : ℝ) :
    Prefers θ δ piA L1c L2c ↔ Prefers θ δ piA L1 L2 :=
  prefers_common_consequence θ δ piA 1
    (fun s hs => by fin_cases s <;> simp_all [L1c, L1])
    (fun s hs => by fin_cases s <;> simp_all [L2c, L2])
    (by simp [L1c, L2c]) (by simp [L1, L2])

/-- The same for the reverse comparison, so strict choices also agree. -/
theorem allaisB_correlated_iff' (θ δ : ℝ) :
    Prefers θ δ piA L2c L1c ↔ Prefers θ δ piA L2 L1 :=
  prefers_common_consequence θ δ piA 1
    (fun s hs => by fin_cases s <;> simp_all [L2c, L2])
    (fun s hs => by fin_cases s <;> simp_all [L1c, L1])
    (by simp [L1c, L2c]) (by simp [L1, L2])

/-- Both joint presentations of problem B have the marginals of `L₁'`
(`1` w.p. `0.11`, else `0`) and `L₂'` (`5` w.p. `0.10`, else `0`). -/
theorem marginals_B :
    (∑ s, if L1i s = 1 then piB s else 0) = 11 / 100 ∧
    (∑ s, if L2i s = 5 then piB s else 0) = 1 / 10 ∧
    (∀ s, L1i s = 0 ∨ L1i s = 1) ∧ (∀ s, L2i s = 0 ∨ L2i s = 5) ∧
    (∑ s, if L1c s = 1 then piA s else 0) = 11 / 100 ∧
    (∑ s, if L2c s = 5 then piA s else 0) = 1 / 10 ∧
    (∀ s, L1c s = 0 ∨ L1c s = 1) ∧ (∀ s, L2c s = 0 ∨ L2c s = 5) := by
  refine ⟨?_, ?_, fun s => ?_, fun s => ?_, ?_, ?_, fun s => ?_, fun s => ?_⟩ <;>
    first
    | (fin_cases s <;> simp [L1i, L2i, L1c, L2c])
    | (norm_num [Fin.sum_univ_four, Fin.sum_univ_three, piA, piB, L1i, L2i, L1c, L2c])

end Econ.Salience
