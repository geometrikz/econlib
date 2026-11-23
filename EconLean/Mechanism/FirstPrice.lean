/-
# The first-price auction with independent uniform values

Vickrey (1961); Krishna, *Auction Theory*, §2.3; MWG §23.D (independent private values). One
object, `n = m + 1` bidders (`m ≥ 1` rivals) with values drawn independently and uniformly
from `[0, 1]`. The highest bid wins and pays its bid.

Main results:
* `firstPrice_winProb`: if every rival bids `β(x) = m x / (m + 1)`, a bid `b` beats all of
  them with probability `(max 0 (min ((m+1) b / m) 1))^m`. This is computed from the product
  of the uniform laws (`Measure.pi`), not assumed.
* `firstPrice_equilibrium`: `β` is a symmetric Bayes–Nash equilibrium: for every value
  `v ∈ [0, 1]` and every bid `b ∈ ℝ`, the expected payoff `(v − b) · P(win | b)` is at most
  that of bidding `β(v)`. Bidders shade their bids by the factor `(n−1)/n`.
* `firstPrice_revenue`: the seller's expected revenue is `(n − 1)/(n + 1)`, the expected
  second-highest value, as revenue equivalence predicts.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

open MeasureTheory Set

/-- The law of the `m` rivals' values: independent uniform on `[0, 1]`. -/
noncomputable def rivalsLaw (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => volume.restrict (Icc (0 : ℝ) 1)

/-- The candidate equilibrium bid with `m` rivals. -/
noncomputable def fpBid (m : ℕ) (x : ℝ) : ℝ := m / (m + 1) * x

/-- Probability that bid `b` beats every rival bidding `fpBid`. -/
noncomputable def fpWinProb (m : ℕ) (b : ℝ) : ℝ :=
  (rivalsLaw m {w | ∀ j, fpBid m (w j) < b}).toReal

/-- Expected payoff of a bidder with value `v` who bids `b`. -/
noncomputable def fpPayoff (m : ℕ) (v b : ℝ) : ℝ := (v - b) * fpWinProb m b

lemma volume_Iio_inter_Icc (a : ℝ) :
    volume (Iio a ∩ Icc (0 : ℝ) 1) = ENNReal.ofReal (max 0 (min a 1)) := by
  rcases le_or_gt a 0 with ha | ha
  · have : Iio a ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩; linarith
    rw [this, measure_empty, max_eq_left (le_trans (min_le_left _ _) ha), ENNReal.ofReal_zero]
  rcases le_or_gt a 1 with ha1 | ha1
  · have : Iio a ∩ Icc (0 : ℝ) 1 = Ico 0 a := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Ico, min_eq_left ha1, max_eq_right ha.le, sub_zero]
  · have : Iio a ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2⟩
    rw [this, Real.volume_Icc, min_eq_right ha1.le, max_eq_right zero_le_one, sub_zero]

/-- **Winning probability against equilibrium rivals.** -/
theorem firstPrice_winProb {m : ℕ} (hm : 0 < m) (b : ℝ) :
    fpWinProb m b = (max 0 (min ((m + 1) * b / m) 1)) ^ m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hset : {w : Fin m → ℝ | ∀ j, fpBid m (w j) < b} =
      Set.pi univ fun _ => Iio ((m + 1) * b / m) := by
    ext w
    simp only [mem_ofPred_eq, mem_pi, mem_univ, true_imp_iff, mem_Iio, fpBid]
    refine forall_congr' fun j => ?_
    rw [lt_div_iff₀ hm', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  simp only [fpWinProb, rivalsLaw, hset]
  rw [Measure.pi_pi]
  simp only [Measure.restrict_apply measurableSet_Iio, volume_Iio_inter_Icc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (le_max_left _ _)]

/-- Tangent-line inequality for `xⁿ` on `[0, ∞)`. -/
lemma pow_tangent_le {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v) (n : ℕ) :
    z ^ (n + 1) + (n + 1) * z ^ n * (v - z) ≤ v ^ (n + 1) := by
  rcases hz.eq_or_lt with rfl | hz
  · rcases n with _ | n
    · simp
    · simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, mul_zero, zero_mul, add_zero]
      positivity
  · have hb := one_add_mul_le_pow (a := v / z - 1) (by
      have : 0 ≤ v / z := div_nonneg hv hz.le
      linarith) (n + 1)
    rw [add_sub_cancel, div_pow] at hb
    rw [le_div_iff₀ (by positivity)] at hb
    have e : z ^ (n + 1) + (n + 1) * z ^ n * (v - z) =
        (1 + ((n + 1 : ℕ) : ℝ) * (v / z - 1)) * z ^ (n + 1) := by
      push_cast
      field_simp
      ring
    rw [e]
    exact hb

/-- **The symmetric equilibrium of the first-price auction.** Against rivals bidding
`m x / (m + 1)`, a bidder with value `v ∈ [0, 1]` maximizes expected payoff by bidding
`m v / (m + 1)`. -/
theorem firstPrice_equilibrium {m : ℕ} (hm : 0 < m) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (b : ℝ) : fpPayoff m v b ≤ fpPayoff m v (fpBid m v) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  obtain ⟨hv0, hv1⟩ := hv
  -- Payoff from the equilibrium bid: `v^{m+1} / (m+1)`.
  have hstar : fpPayoff m v (fpBid m v) = v ^ (m + 1) / (m + 1) := by
    rw [fpPayoff, firstPrice_winProb hm]
    have : (m + 1) * fpBid m v / m = v := by simp only [fpBid]; field_simp
    rw [this, min_eq_left hv1, max_eq_right hv0, fpBid]
    field_simp
    ring
  rw [hstar, fpPayoff, firstPrice_winProb hm]
  set z := max 0 (min ((m + 1) * b / m) 1) with hz
  have hz0 : 0 ≤ z := le_max_left _ _
  have hz1 : z ≤ 1 := max_le zero_le_one (min_le_right _ _)
  -- The tangent inequality at `z`.
  have ht := pow_tangent_le hz0 hv0 m
  rcases le_or_gt ((m + 1) * b / m) 0 with hb0 | hb0
  · -- Non-positive bids never win.
    have : z = 0 := by rw [hz]; exact max_eq_left (le_trans (min_le_left _ _) hb0)
    rw [this, zero_pow hm.ne', mul_zero]
    positivity
  rcases le_or_gt ((m + 1) * b / m) 1 with hb1 | hb1
  · -- Interior bids: `b = m z / (m+1)`.
    have hzb : z = (m + 1) * b / m := by rw [hz, min_eq_left hb1, max_eq_right hb0.le]
    have hb : b = m * z / (m + 1) := by rw [hzb]; field_simp
    rw [hb, le_div_iff₀ (by positivity)]
    have e : (v - m * z / (m + 1)) * z ^ m * (m + 1) =
        z ^ (m + 1) + (m + 1) * z ^ m * (v - z) := by field_simp; ring
    rw [e]
    exact ht
  · -- Bids winning for sure: `b ≥ m/(m+1)`.
    have hz' : z = 1 := by rw [hz, min_eq_right hb1.le, max_eq_right zero_le_one]
    rw [hz'] at ht ⊢
    rw [one_pow, mul_one, le_div_iff₀ (by positivity)]
    have hbm : m / (m + 1) ≤ b := by
      rw [div_le_iff₀ (by positivity)]
      rw [lt_div_iff₀ hm'] at hb1
      linarith
    have : m / (m + 1) * (m + 1) = (m : ℝ) := by field_simp
    simp only [one_pow, mul_one] at ht
    nlinarith

/-- **Expected revenue** of the first-price auction: each of the `m + 1` bidders pays
`β(v) · P(win | β(v))` at value `v`, which integrates to `(n − 1)/(n + 1)` with `n = m + 1`. -/
theorem firstPrice_revenue {m : ℕ} (hm : 0 < m) :
    (m + 1) * ∫ v in (0 : ℝ)..1, fpBid m v * fpWinProb m (fpBid m v) = m / (m + 2) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h : ∀ v ∈ uIcc (0 : ℝ) 1, fpBid m v * fpWinProb m (fpBid m v) =
      m / (m + 1) * v ^ (m + 1) := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    rw [firstPrice_winProb hm]
    have : (m + 1) * fpBid m v / m = v := by simp only [fpBid]; field_simp
    rw [this, min_eq_left hv.2, max_eq_right hv.1, fpBid]
    ring
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  push_cast
  ring

end Econ
