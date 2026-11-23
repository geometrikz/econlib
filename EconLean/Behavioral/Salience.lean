/-
# Salience theory of choice under risk (Bordalo–Gennaioli–Shleifer)

Reference. P. Bordalo, N. Gennaioli and A. Shleifer (2012), "Salience Theory
of Choice Under Risk", *QJE* 127(3).

**The model.** A choice between two lotteries `x` and `y` is described by a
finite state space `ι` with probabilities `π` and state-contingent payoffs
`x s`, `y s`. The *salience* of state `s` is `σ(x s, y s)` for the salience
function

    σ(a, b) = |a − b| / (|a| + |b| + θ),     θ > 0

(BGS eq. (3)). States are ranked by salience; a state with `k` strictly more
salient states gets decision weight proportional to `π_s δ^k` with
`δ ∈ (0, 1]` (BGS eq. (5)). The salient thinker prefers `x` to `y` iff the
distorted expected difference `Σ_s π_s δ^{k_s} (x s − y s)` is nonnegative;
dividing by the normalization `Σ_s π_s δ^{k_s}` gives the normalized
values `V(x) ≥ V(y)` (`prefers_iff_value`).

**What is formalized.**
* The BGS salience function satisfies *ordering*, *diminishing sensitivity*
  and *reflection/symmetry* (BGS Definition 1): `sigma_ordering`,
  `sigma_dimSens`, `sigma_symm`, `sigma_neg`. Ordering is proved for
  intervals of gains `0 ≤ a ≤ a' ≤ b' ≤ b` (losses follow by reflection);
  intervals straddling `0` are not covered.
* Ranks use competition ranking: tied states share the rank given by the
  number of strictly more salient states (immaterial with two states).
* With `δ = 1` the salient thinker is an expected-utility (risk-neutral)
  maximizer (`value_one`); salience never reverses state-wise dominance
  (`prefers_of_dominates`).
* **Long shots** (BGS Proposition 1, two-outcome case): a lottery paying `G`
  with probability `p` versus its expected value `pG` for sure. For
  `δ ∈ (0, 1)` the salient thinker strictly prefers the lottery iff
  `2p²G < θ(1 − 2p)` (`longShot_iff`): risk seeking for small-probability
  gains (`longShot_small_p`) and risk averse for large stakes.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Econ.Salience

open Finset

/-! ### The salience function -/

/-- The BGS salience function `σ(a, b) = |a − b| / (|a| + |b| + θ)`. -/
noncomputable def sigma (θ a b : ℝ) : ℝ := |a - b| / (|a| + |b| + θ)

theorem sigma_symm (θ a b : ℝ) : sigma θ a b = sigma θ b a := by
  unfold sigma; rw [abs_sub_comm, add_comm |a|]

/-- Reflection: salience depends only on magnitudes. -/
theorem sigma_neg (θ a b : ℝ) : sigma θ (-a) (-b) = sigma θ a b := by
  unfold sigma; rw [abs_neg, abs_neg, ← abs_neg (a - b)]; ring_nf

/-- **Ordering** (BGS Definition 1(a)), for nonnegative payoffs: if the
interval `[a', b']` is contained in `[a, b]` and differs from it, it is
strictly less salient. -/
theorem sigma_ordering {θ a a' b' b : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (h1 : a ≤ a')
    (h2 : a' ≤ b') (h3 : b' ≤ b) (hne : a ≠ a' ∨ b' ≠ b) :
    sigma θ a' b' < sigma θ a b := by
  unfold sigma
  rw [abs_sub_comm a', abs_sub_comm a, abs_of_nonneg (sub_nonneg.2 h2),
    abs_of_nonneg (by linarith : 0 ≤ b - a), abs_of_nonneg ha,
    abs_of_nonneg (by linarith : 0 ≤ b), abs_of_nonneg (by linarith : 0 ≤ a'),
    abs_of_nonneg (by linarith : 0 ≤ b'), div_lt_div_iff₀ (by linarith) (by linarith)]
  rcases hne with h | h
  · have : a < a' := lt_of_le_of_ne h1 h
    nlinarith
  · have : b' < b := lt_of_le_of_ne h3 h
    nlinarith

/-- **Diminishing sensitivity** (BGS Definition 1(b)): adding the same
positive amount to both nonnegative payoffs lowers salience (unless they are
equal, when salience is `0` throughout). -/
theorem sigma_dimSens {θ a b ε : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε)
    (hab : a ≠ b) : sigma θ (a + ε) (b + ε) < sigma θ a b := by
  unfold sigma
  rw [show a + ε - (b + ε) = a - b by ring, abs_of_nonneg (by linarith : 0 ≤ a + ε),
    abs_of_nonneg (by linarith : 0 ≤ b + ε), abs_of_nonneg ha, abs_of_nonneg hb]
  have hpos : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
  exact div_lt_div_of_pos_left hpos (by linarith) (by linarith)

/-! ### Salient choice -/

variable {ι : Type*} [Fintype ι]

/-- Salience rank of state `s`: the number of strictly more salient states. -/
noncomputable def rank (σ : ι → ℝ) (s : ι) : ℕ := by
  classical exact (univ.filter fun t => σ s < σ t).card

/-- Salience of each state in the comparison of `x` with `y`. -/
noncomputable def salience (θ : ℝ) (x y : ι → ℝ) (s : ι) : ℝ := sigma θ (x s) (y s)

/-- Undistorted-to-distorted factor `δ ^ rank`. -/
noncomputable def factor (θ δ : ℝ) (x y : ι → ℝ) (s : ι) : ℝ := δ ^ rank (salience θ x y) s

/-- Normalized decision weight of state `s` (BGS eq. (5)). -/
noncomputable def weight (θ δ : ℝ) (π : ι → ℝ) (x y : ι → ℝ) (s : ι) : ℝ :=
  π s * factor θ δ x y s / ∑ r, π r * factor θ δ x y r

/-- Salient value of `x` in the comparison with `y`. -/
noncomputable def value (θ δ : ℝ) (π : ι → ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ s, weight θ δ π x y s * x s

/-- The salient thinker weakly prefers `x` to `y`. -/
def Prefers (θ δ : ℝ) (π : ι → ℝ) (x y : ι → ℝ) : Prop :=
  0 ≤ ∑ s, π s * factor θ δ x y s * (x s - y s)

/-- A probability vector with full support. -/
def IsFullProb (π : ι → ℝ) : Prop := (∀ s, 0 < π s) ∧ ∑ s, π s = 1

theorem factor_symm (θ δ : ℝ) (x y : ι → ℝ) : factor θ δ x y = factor θ δ y x := by
  funext s; unfold factor; congr 2; funext t; exact sigma_symm θ (x t) (y t)

theorem factor_pos {θ δ : ℝ} (hδ : 0 < δ) (x y : ι → ℝ) (s : ι) : 0 < factor θ δ x y s :=
  pow_pos hδ _

theorem norm_pos [Nonempty ι] {θ δ : ℝ} (hδ : 0 < δ) {π : ι → ℝ} (hπ : IsFullProb π)
    (x y : ι → ℝ) : 0 < ∑ r, π r * factor θ δ x y r :=
  sum_pos (fun r _ => mul_pos (hπ.1 r) (factor_pos hδ x y r)) univ_nonempty

/-- Preference is comparison of normalized salient values (the weights are
the same for both lotteries, since salience is symmetric). -/
theorem prefers_iff_value [Nonempty ι] {θ δ : ℝ} (hδ : 0 < δ) {π : ι → ℝ}
    (hπ : IsFullProb π) (x y : ι → ℝ) :
    Prefers θ δ π x y ↔ value θ δ π y x ≤ value θ δ π x y := by
  have hN := norm_pos (θ := θ) hδ hπ x y
  have key : value θ δ π x y - value θ δ π y x =
      (∑ s, π s * factor θ δ x y s * (x s - y s)) / ∑ r, π r * factor θ δ x y r := by
    unfold value weight
    rw [factor_symm θ δ y x, ← sum_sub_distrib, sum_div]
    exact sum_congr rfl fun s _ => by ring
  unfold Prefers
  rw [← sub_nonneg (a := value θ δ π x y) (b := value θ δ π y x), key]
  exact ⟨fun h => div_nonneg h hN.le, fun h => (div_nonneg_iff.1 h).elim (fun h => h.1)
    fun h => absurd h.2 (not_le.2 hN)⟩

/-- **No distortion**: with `δ = 1` the salient value is the expected value. -/
theorem value_one {θ : ℝ} {π : ι → ℝ} (hπ : IsFullProb π) (x y : ι → ℝ) :
    value θ 1 π x y = ∑ s, π s * x s := by
  simp [value, weight, factor, hπ.2]

/-- **Dominance survives salience**: if `x` pays at least `y` in every state
and strictly more in one, the salient thinker strictly prefers `x`. -/
theorem prefers_of_dominates {θ δ : ℝ} (hδ : 0 < δ) {π : ι → ℝ} (hπ : IsFullProb π)
    {x y : ι → ℝ} (hle : ∀ s, y s ≤ x s) {s₀ : ι} (hlt : y s₀ < x s₀) :
    0 < ∑ s, π s * factor θ δ x y s * (x s - y s) :=
  sum_pos' (fun s _ => mul_nonneg (mul_pos (hπ.1 s) (factor_pos hδ x y s)).le
    (sub_nonneg.2 (hle s))) ⟨s₀, mem_univ _,
      mul_pos (mul_pos (hπ.1 s₀) (factor_pos hδ x y s₀)) (sub_pos.2 hlt)⟩

/-! ### Long shots -/

/-- Two states: "win" (`0`) with probability `p` and "lose" (`1`). -/
def probs (p : ℝ) : Fin 2 → ℝ := ![p, 1 - p]

/-- The long-shot lottery: `G` if win, `0` otherwise. -/
def longShot (G : ℝ) : Fin 2 → ℝ := ![G, 0]

/-- Its expected value for sure. -/
def sure (p G : ℝ) : Fin 2 → ℝ := ![p * G, p * G]

/-- Salience of the win state exceeds salience of the lose state iff
`2p²G < θ(1 − 2p)`. -/
theorem win_more_salient_iff {θ p G : ℝ} (hθ : 0 < θ) (hp0 : 0 < p) (hp1 : p < 1)
    (hG : 0 < G) :
    salience θ (longShot G) (sure p G) 1 < salience θ (longShot G) (sure p G) 0 ↔
      2 * p ^ 2 * G < θ * (1 - 2 * p) := by
  simp only [salience, longShot, sure, sigma, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hpG : 0 < p * G := mul_pos hp0 hG
  rw [abs_of_nonneg (by nlinarith : 0 ≤ G - p * G), zero_sub, abs_neg, abs_zero,
    abs_of_pos hpG, abs_of_pos hG, div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith [mul_pos hpG hG, mul_pos hp0 hθ]

/-- Distorted expected difference in the long-shot problem, by salience
ranking. -/
theorem longShot_sum {θ δ p G : ℝ} :
    ∑ s, probs p s * factor θ δ (longShot G) (sure p G) s * (longShot G s - sure p G s) =
      p * (1 - p) * G * (factor θ δ (longShot G) (sure p G) 0 -
        factor θ δ (longShot G) (sure p G) 1) := by
  simp [Fin.sum_univ_two, probs, longShot, sure]
  ring

/-- With two states, rank counts the strictly more salient state. -/
theorem rank_fin2 (σ : Fin 2 → ℝ) (s : Fin 2) :
    rank σ s = (if σ s < σ 0 then 1 else 0) + (if σ s < σ 1 then 1 else 0) := by
  unfold rank
  rw [card_filter, Fin.sum_univ_two]

/-- **Long shots** (BGS Proposition 1). For `δ < 1` (BGS take `δ ∈ (0, 1)`), the salient thinker
strictly prefers a lottery paying `G` with probability `p` to its expected
value `pG` for sure iff `2p²G < θ(1 − 2p)`, i.e. iff the winning state is
the more salient one. -/
theorem longShot_iff {θ δ p G : ℝ} (hθ : 0 < θ) (hδ1 : δ < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hG : 0 < G) :
    0 < ∑ s, probs p s * factor θ δ (longShot G) (sure p G) s * (longShot G s - sure p G s) ↔
      2 * p ^ 2 * G < θ * (1 - 2 * p) := by
  rw [longShot_sum, ← win_more_salient_iff hθ hp0 hp1 hG]
  have hc : 0 < p * (1 - p) * G := mul_pos (mul_pos hp0 (by linarith)) hG
  simp only [factor]
  generalize salience θ (longShot G) (sure p G) = σ
  rcases lt_trichotomy (σ 1) (σ 0) with h | h | h
  · simp only [rank_fin2, lt_irrefl, h, not_lt.2 h.le, ite_true, ite_false]
    norm_num
    exact mul_pos hc (by linarith)
  · simp only [rank_fin2, lt_irrefl, h, sub_self, mul_zero]
  · simp only [rank_fin2, lt_irrefl, h, not_lt.2 h.le, ite_true, ite_false]
    norm_num
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)

/-- **Risk seeking for long shots.** For any stake `G > 0` and `θ > 0`, every
sufficiently unlikely gain is strictly preferred to its expected value. -/
theorem longShot_small_p {θ δ G : ℝ} (hθ : 0 < θ) (hδ1 : δ < 1) (hG : 0 < G) :
    ∃ p₀ > 0, ∀ p, 0 < p → p < p₀ →
      0 < ∑ s, probs p s * factor θ δ (longShot G) (sure p G) s *
        (longShot G s - sure p G s) := by
  refine ⟨min (1 / 4) (θ / G), lt_min (by norm_num) (div_pos hθ hG), fun p hp0 hp => ?_⟩
  have h4 : p < 1 / 4 := lt_of_lt_of_le hp (min_le_left _ _)
  have hθG : p * G < θ := by
    have := lt_of_lt_of_le hp (min_le_right _ _)
    rwa [lt_div_iff₀ hG] at this
  rw [longShot_iff hθ hδ1 hp0 (by linarith) hG]
  nlinarith

/-- **Risk aversion for large stakes.** For fixed `p ∈ (0, 1)` and `θ`, if the
stake is large (`θ(1 − 2p) ≤ 2p²G`), the sure expected value is weakly
preferred. -/
theorem longShot_large_G {θ δ p G : ℝ} (hθ : 0 < θ) (hδ1 : δ < 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hG : 0 < G) (hlarge : θ * (1 - 2 * p) ≤ 2 * p ^ 2 * G) :
    ∑ s, probs p s * factor θ δ (longShot G) (sure p G) s * (longShot G s - sure p G s) ≤ 0 :=
  not_lt.1 fun h => absurd ((longShot_iff hθ hδ1 hp0 hp1 hG).1 h) (not_lt.2 hlarge)

end Econ.Salience
