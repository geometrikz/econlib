/-
# Poisson cognitive hierarchy

Reference. C. Camerer, T.-H. Ho and J.-K. Chong (2004), "A Cognitive Hierarchy
Model of Games", *QJE* 119(3), §II (Poisson frequencies, truncated-truth
beliefs and their properties).

In the cognitive hierarchy (CH) model a player of level `k` believes that the
others are distributed over the levels `0, …, k−1` in the true relative
proportions: its belief about level `h` is `f(h) / Σ_{g<k} f(g)` for `h < k`
and `0` otherwise (`chBelief`), where `f` is the true distribution of levels.
CHC take `f` Poisson with mean `τ` (`poissonFreq`, the average number of
thinking steps).

**Results.**
* `hasSum_poissonFreq`, `poissonFreq_pos`, `poissonFreq_succ`,
  `hasSum_mean_poissonFreq`: the Poisson frequencies are positive, sum to
  `1`, satisfy `f(k+1)/f(k) = τ/(k+1)`, and have mean `τ`.
* `sum_chBelief`, `chBelief_ratio`: level-`k` beliefs are a probability
  distribution over the lower levels that gets their relative proportions
  right.
* `hasSum_abs_chBelief_sub`, `l1_strictAnti`, `tendsto_l1_chBelief`
  (**higher levels are more accurate**, CHC §II): the `ℓ¹` distance
  `Σ_h |g_k(h) − f(h)|` between level-`k` beliefs and the truth (twice the
  total-variation distance) is exactly `2(1 − Σ_{g<k} f(g))`, which falls
  strictly with `k` and tends to `0`; and each belief converges
  (`tendsto_chBelief`). This holds for every positive distribution of levels,
  in particular the Poisson one (`poisson_hasSum_l1`, `poisson_tendsto_l1`).
* `poisson_chGuess_strictAnti`: in the `p`-beauty contest, Poisson CH
  guesses fall strictly with the level (`LevelK.lean`, which uses the
  large-population approximation in which a guess does not affect the
  average, and level `0` guessing `50`).

CHC's estimation of `τ` and their results on dominance-solvable games are
not formalized.
-/
module

public import EconLean.BoundedRationality.LevelK
public import Mathlib.Probability.Distributions.Poisson.Basic

@[expose] public section

noncomputable section

namespace Econ

namespace BoundedRationality

open Finset Filter Topology NNReal

/-- Poisson frequencies of the levels, with mean `τ`. -/
def poissonFreq (τ : ℝ≥0) (k : ℕ) : ℝ := Real.exp (-τ) * (τ : ℝ) ^ k / k.factorial

theorem poissonFreq_pos {τ : ℝ≥0} (hτ : 0 < τ) (k : ℕ) : 0 < poissonFreq τ k := by
  have : (0 : ℝ) < τ := by exact_mod_cast hτ
  unfold poissonFreq; positivity

theorem poissonFreq_nonneg (τ : ℝ≥0) (k : ℕ) : 0 ≤ poissonFreq τ k := by
  unfold poissonFreq; positivity

theorem hasSum_poissonFreq (τ : ℝ≥0) : HasSum (poissonFreq τ) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure τ

theorem poissonFreq_succ (τ : ℝ≥0) (k : ℕ) :
    poissonFreq τ (k + 1) = τ / (k + 1) * poissonFreq τ k := by
  unfold poissonFreq
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **The mean number of thinking steps is `τ`.** -/
theorem hasSum_mean_poissonFreq (τ : ℝ≥0) : HasSum (fun k : ℕ => k * poissonFreq τ k) τ := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, CharP.cast_eq_zero, zero_mul, sub_zero]
  have e : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * poissonFreq τ (k + 1) = τ * poissonFreq τ k := by
    intro k
    rw [poissonFreq_succ]
    push_cast
    field_simp
  simp only [e]
  simpa using (hasSum_poissonFreq τ).mul_left (τ : ℝ)

/-- Level-`k` beliefs: the true frequencies truncated to the lower levels and
renormalized. -/
def chBelief (f : ℕ → ℝ) (k h : ℕ) : ℝ := if h < k then f h / ∑ g ∈ range k, f g else 0

variable {f : ℕ → ℝ}

theorem sum_chBelief (hf : ∀ h, 0 < f h) {k : ℕ} (hk : 0 < k) :
    ∑ h ∈ range k, chBelief f k h = 1 := by
  have hF : 0 < ∑ g ∈ range k, f g := sum_pos (fun g _ => hf g) ⟨0, mem_range.2 hk⟩
  rw [sum_congr rfl fun h hh => (show chBelief f k h = f h / ∑ g ∈ range k, f g by
    simp [chBelief, mem_range.1 hh]), ← sum_div, div_self hF.ne']

/-- Level-`k` beliefs get the relative proportions of lower levels right. -/
theorem chBelief_ratio {k h h' : ℕ} (hh : h < k) (hh' : h' < k) :
    chBelief f k h * f h' = chBelief f k h' * f h := by
  simp only [chBelief, hh, hh', ite_true]; ring

/-- **`ℓ¹` distance (twice the total-variation distance) of level-`k` beliefs
from the truth.** -/
theorem hasSum_abs_chBelief_sub (hf : ∀ h, 0 < f h) (hsum : HasSum f 1) {k : ℕ} (hk : 0 < k) :
    HasSum (fun h => |chBelief f k h - f h|) (2 * (1 - ∑ g ∈ range k, f g)) := by
  set F := ∑ g ∈ range k, f g
  have hF : 0 < F := sum_pos (fun g _ => hf g) ⟨0, mem_range.2 hk⟩
  have hF1 : F ≤ 1 := sum_le_hasSum (range k) (fun g _ => (hf g).le) hsum
  have e : (fun h => |chBelief f k h - f h|) =
      (fun h => if h < k then f h * ((1 - F) / F) else 0) +
        (fun h => f h - if h < k then f h else 0) := by
    funext h
    simp only [chBelief, Pi.add_apply]
    split_ifs with hh
    · have : f h / F - f h = f h * ((1 - F) / F) := by field_simp
      rw [this, abs_of_nonneg (mul_nonneg (hf h).le (div_nonneg (by linarith) hF.le))]
      ring
    · simp [abs_of_nonneg (hf h).le]
  rw [e]
  have h1 : HasSum (fun h => if h < k then f h * ((1 - F) / F) else 0) (1 - F) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := range k)
      (f := fun h => if h < k then f h * ((1 - F) / F) else 0)
      (fun h hh => by rw [mem_range] at hh; simp [hh])
    convert this using 1
    rw [sum_congr rfl fun h hh => ite_eq_left_iff.2 (fun h' => absurd (mem_range.1 hh) h'),
      ← sum_mul]
    field_simp
    ring
  have h2 : HasSum (fun h => if h < k then f h else 0) F := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := range k)
      (f := fun h => if h < k then f h else 0)
      (fun h hh => by rw [mem_range] at hh; simp [hh])
    convert this using 1
    exact (sum_congr rfl fun h hh => ite_eq_left_iff.2 (fun h' => absurd (mem_range.1 hh) h')).symm
  convert h1.add (hsum.sub h2) using 1
  ring

/-- The `ℓ¹` distance of level-`k` beliefs from the truth falls strictly with
`k`. -/
theorem l1_strictAnti (hf : ∀ h, 0 < f h) :
    StrictAnti (fun k => 2 * (1 - ∑ g ∈ range k, f g)) := by
  refine strictAnti_nat_of_succ_lt fun k => ?_
  simp only [sum_range_succ]
  linarith [hf k]

/-- **Higher levels' beliefs converge to the truth in `ℓ¹`.** -/
theorem tendsto_l1_chBelief (hf : ∀ h, 0 < f h) (hsum : HasSum f 1) :
    Tendsto (fun k => ∑' h, |chBelief f k h - f h|) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k => 2 * (1 - ∑ g ∈ range k, f g)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsum.tendsto_sum_nat).const_mul 2
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact (hasSum_abs_chBelief_sub hf hsum hk).tsum_eq.symm

/-- **Each level-`k` belief converges to the truth as `k → ∞`.** -/
theorem tendsto_chBelief (hsum : HasSum f 1) (h : ℕ) :
    Tendsto (fun k => chBelief f k h) atTop (𝓝 (f h)) := by
  have hlim : Tendsto (fun k => f h / ∑ g ∈ range k, f g) atTop (𝓝 (f h / 1)) :=
    tendsto_const_nhds.div hsum.tendsto_sum_nat one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop h] with k hk
  simp [chBelief, hk]

/-- Non-vacuity (Poisson): the exact `ℓ¹` distance. -/
theorem poisson_hasSum_l1 {τ : ℝ≥0} (hτ : 0 < τ) {k : ℕ} (hk : 0 < k) :
    HasSum (fun h => |chBelief (poissonFreq τ) k h - poissonFreq τ h|)
      (2 * (1 - ∑ g ∈ range k, poissonFreq τ g)) :=
  hasSum_abs_chBelief_sub (poissonFreq_pos hτ) (hasSum_poissonFreq τ) hk

/-- Non-vacuity (Poisson): beliefs converge to the truth in `ℓ¹`. -/
theorem poisson_tendsto_l1 {τ : ℝ≥0} (hτ : 0 < τ) :
    Tendsto (fun k => ∑' h, |chBelief (poissonFreq τ) k h - poissonFreq τ h|) atTop (𝓝 0) :=
  tendsto_l1_chBelief (poissonFreq_pos hτ) (hasSum_poissonFreq τ)

/-- **Poisson CH guesses fall with the level** in the `p`-beauty contest. -/
theorem poisson_chGuess_strictAnti {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {τ : ℝ≥0} (hτ : 0 < τ) :
    StrictAnti (chGuess p (poissonFreq τ)) :=
  chGuess_strictAnti hp0 hp1 (poissonFreq_pos hτ)

end BoundedRationality

end Econ
