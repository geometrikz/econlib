/-
# Salience and the common-ratio effect

Reference. P. Bordalo, N. Gennaioli and A. Shleifer (2012), "Salience Theory
of Choice Under Risk", *QJE* 127(3), §IV (the common-ratio effect);
D. Kahneman and A. Tversky (1979), "Prospect Theory", *Econometrica* 47(2)
(problems 3 and 4).

Builds on `Salience.lean` and `SalienceAllais.lean`. Payoffs are in
thousands; the numbers are Kahneman–Tversky's common-ratio problems:

* problem A: `L₁ = 3` for sure versus `L₂ = (4, 0.8; 0, 0.2)`;
* problem B: `L₁' = (3, 0.25; 0, 0.75)` versus `L₂' = (4, 0.2; 0, 0.8)`,
  obtained by scaling the winning probabilities of A by `1/4`.

The lotteries of each problem are independent (in A `L₁` is degenerate, so
there are two joint states; in B there are four).

**Results.**
Sign convention: as in `Salience.lean`, the distorted expected difference
`Σ_s π_s δ^{rank_s} (x s − y s)` is positive iff `x` is strictly preferred.

* `salience_CA`, `ranks_CA`: in problem A, for every `θ > 0`, the most
  salient state is "`L₁` pays 3, `L₂` pays 0". `crA_sum`, `crA_safe_iff`: the
  distorted expected difference is `0.6 − 0.8δ`, and the sure `L₁` is
  strictly preferred iff `δ < 3/4`.
* `salience_CB`, `ranks_CB`: in problem B, for every `θ > 0`, the most
  salient state is "`L₁'` pays 0, `L₂'` pays 4". `crB_sum`, `crB_risky`: the
  distorted expected difference is `−0.05δ² + 0.6δ − 0.6`, and `L₂'` is
  strictly preferred for every `δ ≤ 1`.
* `common_ratio`: hence for `θ > 0` and `δ < 3/4` the salient thinker shows
  the common-ratio pattern (`L₁` over `L₂`, `L₂'` over `L₁'`), which no
  expected-utility maximizer shows (`eu_no_common_ratio`).
  `common_ratio_prefers` restates it with the model's preference relation
  `Prefers` (weak preference one way, not the other) for BGS's range
  `0 < δ < 3/4`.
* `crA_eu`: without distortion (`δ = 1`, expected value) `L₂` is chosen in A.
* `crB_product`, `marginals_cr`: the joint distribution in B is the product
  of the marginals, which are those of `L₁'` and `L₂'`.

**Scope.** Only these numbers are treated. BGS's general analysis of the
common-ratio effect (arbitrary payoffs and scaling factor) and the
correlated presentation of the common-ratio problems are not formalized.
The results hold for every real `δ` below the stated bounds, including
`δ ≤ 0`, outside BGS's range `(0, 1]`.
-/
module

public import EconLean.Behavioral.SalienceAllais

@[expose] public section

namespace Econ.Salience

open Finset

/-- Problem A: joint states `(L₁, L₂) = (3, 4)` (prob `0.8`) and `(3, 0)` (`0.2`). -/
noncomputable def piCA : Fin 2 → ℝ := ![8 / 10, 2 / 10]
def C1 : Fin 2 → ℝ := ![3, 3]
def C2 : Fin 2 → ℝ := ![4, 0]

/-- Problem B with independent lotteries: joint states
`(L₁', L₂') = (3, 4), (3, 0), (0, 4), (0, 0)`. -/
noncomputable def piCB : Fin 4 → ℝ := ![5 / 100, 20 / 100, 15 / 100, 60 / 100]
def C1i : Fin 4 → ℝ := ![3, 3, 0, 0]
def C2i : Fin 4 → ℝ := ![4, 0, 4, 0]

theorem piCA_isFullProb : IsFullProb piCA := by
  refine ⟨fun s => ?_, ?_⟩
  · fin_cases s <;> simp [piCA]
  · norm_num [piCA, Fin.sum_univ_two]

theorem piCB_isFullProb : IsFullProb piCB := by
  refine ⟨fun s => ?_, ?_⟩
  · fin_cases s <;> simp [piCB]
  · norm_num [piCB, Fin.sum_univ_four]

/-- `piCB` is the product of the marginals `(0.25, 0.75)` and `(0.2, 0.8)`. -/
theorem crB_product : piCB = ![1 / 4 * (2 / 10), 1 / 4 * (8 / 10),
    3 / 4 * (2 / 10), 3 / 4 * (8 / 10)] := by
  funext s; fin_cases s <;> norm_num [piCB]

/-- The marginals of problem B are those of `L₁'` and `L₂'`, and problem A's
`L₂` pays 4 with probability `0.8`. -/
theorem marginals_cr :
    (∑ s, if C1i s = 3 then piCB s else 0) = 1 / 4 ∧
    (∑ s, if C2i s = 4 then piCB s else 0) = 2 / 10 ∧
    (∀ s, C1i s = 0 ∨ C1i s = 3) ∧ (∀ s, C2i s = 0 ∨ C2i s = 4) ∧
    (∑ s, if C2 s = 4 then piCA s else 0) = 8 / 10 ∧
    (∀ s, C1 s = 3) ∧ (∀ s, C2 s = 0 ∨ C2 s = 4) := by
  refine ⟨?_, ?_, fun s => ?_, fun s => ?_, ?_, fun s => ?_, fun s => ?_⟩ <;>
    first
    | (fin_cases s <;> simp [C1, C2, C1i, C2i])
    | (norm_num [Fin.sum_univ_four, Fin.sum_univ_two, piCA, piCB, C1, C2, C1i, C2i])

theorem salience_CA (θ : ℝ) : salience θ C1 C2 = ![1 / (7 + θ), 3 / (3 + θ)] := by
  funext s
  fin_cases s <;> norm_num [salience, sigma, C1, C2]

theorem salience_CB (θ : ℝ) :
    salience θ C1i C2i = ![1 / (7 + θ), 3 / (3 + θ), 4 / (4 + θ), 0] := by
  funext s
  fin_cases s <;> norm_num [salience, sigma, C1i, C2i]

theorem ranks_CA {θ : ℝ} (hθ0 : 0 < θ) :
    rank (salience θ C1 C2) 0 = 1 ∧ rank (salience θ C1 C2) 1 = 0 := by
  have hab : 1 / (7 + θ) < 3 / (3 + θ) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  rw [salience_CA]
  generalize 1 / (7 + θ) = a at *
  generalize 3 / (3 + θ) = b at *
  simp [rank_eq_sum, Fin.sum_univ_two, hab, hab.le]

theorem ranks_CB {θ : ℝ} (hθ0 : 0 < θ) :
    rank (salience θ C1i C2i) 0 = 2 ∧ rank (salience θ C1i C2i) 1 = 1 ∧
      rank (salience θ C1i C2i) 2 = 0 ∧ rank (salience θ C1i C2i) 3 = 3 := by
  have ha : (0 : ℝ) < 1 / (7 + θ) := by positivity
  have hab : 1 / (7 + θ) < 3 / (3 + θ) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  have hbc : 3 / (3 + θ) < 4 / (4 + θ) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  have hb : (0 : ℝ) < 3 / (3 + θ) := by positivity
  have hc : (0 : ℝ) < 4 / (4 + θ) := by positivity
  have hac := hab.trans hbc
  rw [salience_CB]
  generalize 1 / (7 + θ) = a at *
  generalize 3 / (3 + θ) = b at *
  generalize 4 / (4 + θ) = c at *
  simp [rank_eq_sum, Fin.sum_univ_four, ha, hab, hb, hbc, hc, hac, not_lt.2 hab.le,
    not_lt.2 ha.le, not_lt.2 hb.le, not_lt.2 hbc.le, not_lt.2 hc.le, not_lt.2 hac.le]

/-- Distorted expected difference `L₁ − L₂` in problem A. -/
theorem crA_sum {θ : ℝ} (hθ0 : 0 < θ) (δ : ℝ) :
    ∑ s, piCA s * factor θ δ C1 C2 s * (C1 s - C2 s) = 6 / 10 - 8 / 10 * δ := by
  obtain ⟨h0, h1⟩ := ranks_CA hθ0
  simp only [Fin.sum_univ_two, factor, h0, h1]
  norm_num [piCA, C1, C2]
  ring

/-- Distorted expected difference `L₁' − L₂'` in problem B. -/
theorem crB_sum {θ : ℝ} (hθ0 : 0 < θ) (δ : ℝ) :
    ∑ s, piCB s * factor θ δ C1i C2i s * (C1i s - C2i s) =
      -(5 / 100) * δ ^ 2 + 6 / 10 * δ - 6 / 10 := by
  obtain ⟨h0, h1, h2, h3⟩ := ranks_CB hθ0
  simp only [Fin.sum_univ_four, factor, h0, h1, h2, h3]
  norm_num [piCB, C1i, C2i]
  ring

/-- **Problem A**: the sure `L₁` is strictly preferred iff `δ < 3/4`. -/
theorem crA_safe_iff {θ : ℝ} (hθ0 : 0 < θ) (δ : ℝ) :
    0 < ∑ s, piCA s * factor θ δ C1 C2 s * (C1 s - C2 s) ↔ δ < 3 / 4 := by
  rw [crA_sum hθ0]; constructor <;> intro h <;> linarith

/-- **Problem B**: `L₂'` is strictly preferred for every `δ ≤ 1`. -/
theorem crB_risky {θ δ : ℝ} (hθ0 : 0 < θ) (hδ : δ ≤ 1) :
    ∑ s, piCB s * factor θ δ C1i C2i s * (C1i s - C2i s) < 0 := by
  rw [crB_sum hθ0]; nlinarith [sq_nonneg δ]

/-- **The common-ratio effect under salience.** -/
theorem common_ratio {θ δ : ℝ} (hθ0 : 0 < θ) (hδ : δ < 3 / 4) :
    0 < ∑ s, piCA s * factor θ δ C1 C2 s * (C1 s - C2 s) ∧
      ∑ s, piCB s * factor θ δ C1i C2i s * (C1i s - C2i s) < 0 :=
  ⟨(crA_safe_iff hθ0 δ).2 hδ, crB_risky hθ0 (by linarith)⟩

/-- Without distortion (`δ = 1`), `L₂` is strictly preferred in problem A. -/
theorem crA_eu (θ : ℝ) : ∑ s, piCA s * factor θ 1 C1 C2 s * (C1 s - C2 s) < 0 := by
  simp only [factor, one_pow, mul_one, Fin.sum_univ_two]
  norm_num [piCA, C1, C2]

/-- **No expected-utility maximizer shows the common-ratio pattern.** -/
theorem eu_no_common_ratio (u : ℝ → ℝ) :
    (∑ s, piCA s * u (C2 s) < ∑ s, piCA s * u (C1 s)) ↔
      (∑ s, piCB s * u (C2i s) < ∑ s, piCB s * u (C1i s)) := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four]
  norm_num [piCA, piCB, C1, C2, C1i, C2i]
  constructor <;> intro h <;> linarith

theorem sum_swap {ι : Type*} [Fintype ι] (θ δ : ℝ) (π x y : ι → ℝ) :
    ∑ s, π s * factor θ δ y x s * (y s - x s) = -∑ s, π s * factor θ δ x y s * (x s - y s) := by
  rw [factor_symm θ δ y x, ← sum_neg_distrib]
  exact sum_congr rfl fun s _ => by ring

/-- The common-ratio effect in terms of the preference relation `Prefers`:
`L₁ ≻ L₂` and `L₂' ≻ L₁'` (strictly). -/
theorem common_ratio_prefers {θ δ : ℝ} (hθ0 : 0 < θ) (_hδ0 : 0 < δ) (hδ : δ < 3 / 4) :
    (Prefers θ δ piCA C1 C2 ∧ ¬ Prefers θ δ piCA C2 C1) ∧
      (Prefers θ δ piCB C2i C1i ∧ ¬ Prefers θ δ piCB C1i C2i) := by
  obtain ⟨hA, hB⟩ := common_ratio hθ0 hδ
  unfold Prefers
  rw [sum_swap θ δ piCA C1 C2, sum_swap θ δ piCB C1i C2i]
  exact ⟨⟨hA.le, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end Econ.Salience
