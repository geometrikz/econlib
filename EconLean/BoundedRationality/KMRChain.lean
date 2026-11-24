/-
# The KMR chain: risk-dominant selection in the full chain

References. M. Kandori, G. Mailath and R. Rob (1993), "Learning, Mutation, and
Long Run Equilibria in Games", *Econometrica* 61(1); K. Binmore,
L. Samuelson and R. Vaughan (1995), "Musical Chairs: Modeling Noisy
Evolution", *GEB* 11 (one revision per period); W. H. Sandholm (2010),
*Population Games and Evolutionary Dynamics*, ch. 11–12 (birth–death chains,
detailed balance, stochastic stability).

**Birth–death chains** (`BirthDeath`). On the states `0, …, N`, the chain moves
from `z` up to `z + 1` with probability `up z` (if `z < N`), down to `z − 1`
with probability `down z` (if `z > 0`), and otherwise stays (`P`, `stay`).
Its rows sum to one (`sum_P`) and its entries are nonnegative when the rates
are (`P_nonneg`). `IsStationaryDist μ` says that `μ` is a probability vector on
`{0, …, N}` (values of `μ` beyond `N` play no role) with `μ P = μ`. The
existence and uniqueness results are algebraic and do not assume
`up z + down z ≤ 1`; under it (and nonnegative rates) `P` is stochastic.
* `pi_isStationaryDist`: with positive down-rates, the vector
  `π z ∝ ∏_{k<z} up k / down (k+1)` (`w`, `pi`) is stationary (detailed balance,
  `pi_detailedBalance`);
* `eq_pi`: it is the **only** stationary distribution (the cut-flow
  identity, `flux_balance`).

**The KMR chain** (`Coord.kup`, `Coord.kdown`). `N` players play the
coordination game `G` of `StochasticStability.lean` against the field. Each
period one player, drawn uniformly, revises: with probability `1 − ε` it
picks a best reply to the current share of `A` (ties to `A`), and with
probability `ε` it picks `A` or `B` with equal chances. So a revising player
picks `A` with probability `1 − ε/2` if `A` is a best reply and `ε/2`
otherwise (`rA`), and the number of `A` players is a birth–death chain. As in
`StochasticStability.lean`, payoffs are against the population share
*including* the reviser (`z/N`); KMR's matching with others only, share
`(z − 1)/(N − 1)` or `z/(N − 1)`, moves the thresholds by `O(1)` players.
* `kmr_isStationaryDist`: for `0 < ε ≤ 1` the chain has a (unique, by
  `eq_pi`) stationary distribution.
* `kmr_selects_riskDominant` (**KMR, full chain**): if `A` is risk dominant,
  then in every large enough population, the stationary probability of the
  all-`A` state tends to `1` as `ε → 0`, and that of every other state to `0`
  (`kmr_tendsto_zero`). The proof bounds `π z / π N` by `C ε` for `z < N`:
  every step down from the `A` basin costs a factor `ε` and every step up the
  `B` basin gains `1/ε`, and the `A` basin is the larger one.
* `stagHunt_kmr`: in the stag hunt (`p* = 1/4`; there `A` is the safe hare
  action and `B` the payoff-dominant stag), all-`A` is selected.

This is the one-revision (birth–death) version of the KMR dynamics (as in
Binmore–Samuelson–Vaughan and Sandholm), not KMR's own chain; KMR's
simultaneous-revision "Darwinian" chain is in `KMRDarwin.lean`. Only selection of `A`
when `A` is risk dominant is stated (the case of `B` is symmetric).
-/
module

public import EconLean.BoundedRationality.StochasticStability
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

noncomputable section

namespace Econ

namespace StochasticStability

open Finset Filter Topology

namespace BirthDeath

/-- Probability of staying at `z`. -/
def stay (up down : ℕ → ℝ) (N z : ℕ) : ℝ :=
  1 - (if z < N then up z else 0) - (if 0 < z then down z else 0)

/-- The transition probability from `z` to `z'` of the birth–death chain on
`{0, …, N}`. -/
def P (up down : ℕ → ℝ) (N z z' : ℕ) : ℝ :=
  (if z + 1 = z' then up z else 0) + (if z = z' + 1 then down z else 0) +
    (if z = z' then stay up down N z else 0)

/-- A stationary distribution of the chain on `{0, …, N}`. -/
def IsStationaryDist (up down : ℕ → ℝ) (N : ℕ) (μ : ℕ → ℝ) : Prop :=
  (∀ z ≤ N, 0 ≤ μ z) ∧ ∑ z ∈ range (N + 1), μ z = 1 ∧
    ∀ z' ≤ N, ∑ z ∈ range (N + 1), μ z * P up down N z z' = μ z'

/-- Unnormalized stationary weights `∏_{k<z} up k / down (k+1)`. -/
def w (up down : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | z + 1 => w up down z * (up z / down (z + 1))

/-- The candidate stationary distribution. -/
def pi (up down : ℕ → ℝ) (N z : ℕ) : ℝ := w up down z / ∑ k ∈ range (N + 1), w up down k

variable {up down : ℕ → ℝ} {N : ℕ}

/-- Rows of `P` sum to one. -/
theorem sum_P {z : ℕ} (hz : z ≤ N) : ∑ z' ∈ range (N + 1), P up down N z z' = 1 := by
  simp only [P, sum_add_distrib, sum_ite_eq, mem_range, stay]
  rcases z with _ | j
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · simp [hN]
  · have h1 : ¬ j + 1 = 0 := by omega
    simp only [Nat.add_right_cancel_iff, sum_ite_eq, mem_range]
    by_cases hj : j + 1 < N
    · simp [hj, show j < N + 1 by omega, show j + 1 < N + 1 by omega,
        show j + 1 + 1 < N + 1 by omega]
    · have : j + 1 = N := by omega
      subst this
      simp [show j < j + 1 + 1 by omega]

theorem P_nonneg (hup : ∀ z ≤ N, 0 ≤ up z) (hdown : ∀ z ≤ N, 0 ≤ down z)
    (hsum : ∀ z ≤ N, up z + down z ≤ 1) {z : ℕ} (hz : z ≤ N) (z' : ℕ) :
    0 ≤ P up down N z z' := by
  have h1 := hup z hz
  have h2 := hdown z hz
  have h3 := hsum z hz
  have hs : 0 ≤ stay up down N z := by
    unfold stay; split_ifs <;> linarith
  unfold P
  split_ifs <;> linarith

/-- The balance equation at `z'` in local form. -/
theorem sum_mul_P (μ : ℕ → ℝ) {z' : ℕ} (hz' : z' ≤ N) :
    ∑ z ∈ range (N + 1), μ z * P up down N z z' =
      (if 0 < z' then μ (z' - 1) * up (z' - 1) else 0) +
        (if z' < N then μ (z' + 1) * down (z' + 1) else 0) + μ z' * stay up down N z' := by
  simp only [P, mul_add, mul_ite, mul_zero, sum_add_distrib, sum_ite_eq', mem_range]
  rcases z' with _ | j
  · simp
  · have e : ∀ z, (z + 1 = j + 1) ↔ z = j := fun z => by omega
    simp only [e, sum_ite_eq', mem_range, show j < N + 1 by omega,
      show j + 1 < N + 1 by omega, ite_true]
    simp

/-- Detailed balance for the weights. -/
theorem w_succ_mul {z : ℕ} (hd : down (z + 1) ≠ 0) :
    w up down (z + 1) * down (z + 1) = w up down z * up z := by
  simp only [w]; field_simp

theorem w_pos (hup : ∀ z < N, 0 < up z) (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z) :
    ∀ z ≤ N, 0 < w up down z := by
  intro z
  induction z with
  | zero => intro; simp [w]
  | succ k ih =>
    intro hk
    simp only [w]
    exact mul_pos (ih (by omega)) (div_pos (hup k (by omega)) (hdown _ (by omega) hk))

theorem w_nonneg (hup : ∀ z < N, 0 ≤ up z) (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z) :
    ∀ z ≤ N, 0 ≤ w up down z := by
  intro z
  induction z with
  | zero => intro; simp [w]
  | succ k ih =>
    intro hk
    simp only [w]
    exact mul_nonneg (ih (by omega)) (div_nonneg (hup k (by omega)) (hdown _ (by omega) hk).le)

theorem sum_w_pos (hup : ∀ z < N, 0 ≤ up z) (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z) :
    0 < ∑ k ∈ range (N + 1), w up down k := by
  rw [sum_range_succ']
  have : 0 ≤ ∑ k ∈ range N, w up down (k + 1) :=
    sum_nonneg fun k hk => w_nonneg hup hdown _ (by rw [mem_range] at hk; omega)
  rw [show w up down 0 = 1 from rfl]; linarith

/-- **Detailed balance**: `π z · up z = π (z+1) · down (z+1)`. -/
theorem pi_detailedBalance {z : ℕ} (hd : down (z + 1) ≠ 0) :
    pi up down N z * up z = pi up down N (z + 1) * down (z + 1) := by
  simp only [pi, div_mul_eq_mul_div, w_succ_mul hd]

/-- **Existence**: `π` is a stationary distribution. -/
theorem pi_isStationaryDist (hup : ∀ z < N, 0 ≤ up z)
    (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z) : IsStationaryDist up down N (pi up down N) := by
  have hZ := sum_w_pos hup hdown
  refine ⟨fun z hz => div_nonneg (w_nonneg hup hdown z hz) hZ.le, ?_, fun z' hz' => ?_⟩
  · simp only [pi, div_eq_mul_inv, ← sum_mul]; exact mul_inv_cancel₀ hZ.ne'
  rw [sum_mul_P _ hz']
  have hA : 0 < z' → pi up down N (z' - 1) * up (z' - 1) = pi up down N z' * down z' := by
    intro h
    obtain ⟨j, rfl⟩ : ∃ j, z' = j + 1 := ⟨z' - 1, by omega⟩
    simpa using pi_detailedBalance (N := N) (hdown (j + 1) h hz').ne'
  have hB : z' < N → pi up down N (z' + 1) * down (z' + 1) = pi up down N z' * up z' :=
    fun h => (pi_detailedBalance (hdown (z' + 1) (by omega) (by omega)).ne').symm
  unfold stay
  by_cases h1 : 0 < z' <;> by_cases h2 : z' < N <;>
    simp only [h1, h2, ite_true, ite_false, hA, hB] <;> ring

/-- **Cut-flow identity**: in a stationary distribution, the flow across the
cut between `z` and `z + 1` balances. -/
theorem flux_balance {μ : ℕ → ℝ} (hμ : IsStationaryDist up down N μ) :
    ∀ z < N, μ (z + 1) * down (z + 1) = μ z * up z := by
  intro z
  induction z with
  | zero =>
    intro hN
    have h := hμ.2.2 0 (by omega)
    rw [sum_mul_P _ (by omega)] at h
    simp only [lt_irrefl, ite_false, hN, ite_true, stay, zero_add] at h
    linarith
  | succ k ih =>
    intro hk
    have h := hμ.2.2 (k + 1) (by omega)
    rw [sum_mul_P _ (by omega)] at h
    have ih' := ih (by omega)
    simp only [Nat.succ_pos, ite_true, hk, stay, Nat.add_sub_cancel] at h
    linarith

/-- **Uniqueness**: every stationary distribution is `π`. -/
theorem eq_pi (hup : ∀ z < N, 0 ≤ up z) (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z)
    {μ : ℕ → ℝ} (hμ : IsStationaryDist up down N μ) : ∀ z ≤ N, μ z = pi up down N z := by
  have hfl := flux_balance hμ
  have hw : ∀ z ≤ N, μ z = μ 0 * w up down z := by
    intro z
    induction z with
    | zero => intro; simp [w]
    | succ k ih =>
      intro hk
      have hd := (hdown (k + 1) (by omega) hk).ne'
      have := hfl k (by omega)
      rw [ih (by omega)] at this
      simp only [w]
      field_simp
      linarith
  have hZ := sum_w_pos hup hdown
  have h0 : μ 0 = 1 / ∑ k ∈ range (N + 1), w up down k := by
    have h1 := hμ.2.1
    rw [sum_congr rfl fun z hz => hw z (by rw [mem_range] at hz; omega), ← mul_sum] at h1
    field_simp; linarith
  intro z hz
  rw [hw z hz, h0, pi]; ring

/-- Product formula for the weights. -/
theorem w_eq_prod {z : ℕ} : ∀ n, z ≤ n →
    w up down n = w up down z * ∏ k ∈ Ico z n, (up k / down (k + 1)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hzn ih =>
    rw [prod_Ico_succ_top hzn, ← mul_assoc, ← ih]; rfl

/-- `w z = w N · ∏_{z ≤ k < N} down (k+1) / up k`. -/
theorem w_eq_mul_prod (hup : ∀ z < N, 0 < up z) (hdown : ∀ z, 0 < z → z ≤ N → 0 < down z)
    {z : ℕ} (hz : z ≤ N) :
    w up down z = w up down N * ∏ k ∈ Ico z N, (down (k + 1) / up k) := by
  rw [w_eq_prod N hz, mul_assoc, ← prod_mul_distrib, prod_eq_one, mul_one]
  intro k hk
  rw [mem_Ico] at hk
  have h1 := (hup k (by omega)).ne'
  have h2 := (hdown (k + 1) (by omega) (by omega)).ne'
  field_simp

end BirthDeath

/-! ### The KMR chain -/

namespace Coord

variable (G : Coord)

/-- Probability that a revising player picks `A` when `z` of `N` play `A`. -/
def rA (N : ℕ) (ε : ℝ) (z : ℕ) : ℝ := if G.pstar ≤ (z : ℝ) / N then 1 - ε / 2 else ε / 2

/-- Probability that the number of `A` players rises from `z`. -/
def kup (N : ℕ) (ε : ℝ) (z : ℕ) : ℝ := ((N : ℝ) - z) / N * G.rA N ε z

/-- Probability that the number of `A` players falls from `z`. -/
def kdown (N : ℕ) (ε : ℝ) (z : ℕ) : ℝ := (z : ℝ) / N * (1 - G.rA N ε z)

theorem pstar_le_iff {N : ℕ} (hN : 0 < N) (z : ℕ) :
    G.pstar ≤ (z : ℝ) / N ↔ G.resistB N ≤ z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [resistB, Nat.ceil_le, le_div_iff₀ hN', mul_comm]

theorem rA_eq {N : ℕ} (hN : 0 < N) (ε : ℝ) (z : ℕ) :
    G.rA N ε z = if G.resistB N ≤ z then 1 - ε / 2 else ε / 2 := by
  simp only [rA, G.pstar_le_iff hN]

theorem kup_pos {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℕ} (hz : z < N) :
    0 < G.kup N ε z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hz)
  have hz' : (z : ℝ) < N := by exact_mod_cast hz
  have : 0 < G.rA N ε z := by unfold rA; split_ifs <;> linarith
  unfold kup; exact mul_pos (div_pos (by linarith) hN') this

theorem kdown_pos {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℕ} (hz : 0 < z)
    (hzN : z ≤ N) : 0 < G.kdown N ε z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hz hzN)
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  have : 0 < 1 - G.rA N ε z := by unfold rA; split_ifs <;> linarith
  unfold kdown; exact mul_pos (div_pos hz' hN') this

/-- The KMR transition probabilities are nonnegative (rows sum to one by
`BirthDeath.sum_P`). -/
theorem kmr_P_nonneg {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℕ} (hz : z ≤ N)
    (z' : ℕ) : 0 ≤ BirthDeath.P (G.kup N ε) (G.kdown N ε) N z z' := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : z = 0 := by omega
    subst this
    simp [BirthDeath.P, BirthDeath.stay, kup]; split_ifs <;> norm_num
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : ∀ k, 0 ≤ G.rA N ε k ∧ G.rA N ε k ≤ 1 := fun k => by
    unfold rA; split_ifs <;> constructor <;> linarith
  refine BirthDeath.P_nonneg (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) hz z'
  · have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    exact mul_nonneg (div_nonneg (by linarith) hN'.le) (hr k).1
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN'.le) (by linarith [(hr k).2])
  · have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    unfold kup kdown
    have e : ((N : ℝ) - k) / N * G.rA N ε k + k / N * (1 - G.rA N ε k) =
        1 - (k / N * G.rA N ε k + ((N : ℝ) - k) / N * (1 - G.rA N ε k)) := by
      field_simp; ring
    rw [e]
    have := mul_nonneg (div_nonneg (Nat.cast_nonneg k) hN'.le) (hr k).1
    have := mul_nonneg (div_nonneg (sub_nonneg.2 hk') hN'.le) (by linarith [(hr k).2] :
      0 ≤ 1 - G.rA N ε k)
    linarith

/-- **Existence** of the stationary distribution of the KMR chain. -/
theorem kmr_isStationaryDist {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    BirthDeath.IsStationaryDist (G.kup N ε) (G.kdown N ε) N
      (BirthDeath.pi (G.kup N ε) (G.kdown N ε) N) :=
  BirthDeath.pi_isStationaryDist (fun _ hz => (G.kup_pos hε hε1 hz).le)
    (fun _ hz hzN => G.kdown_pos hε hε1 hz hzN)

/-- Exponent of `ε` in the ratio `π k / π (k+1)`. -/
def expo (m k : ℕ) : ℤ := if m ≤ k then 1 else if k + 1 < m then -1 else 0

/-- One-step bound on the revision probabilities. -/
theorem one_sub_rA_le {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : ℕ) :
    1 - G.rA N ε (k + 1) ≤ 2 * ε ^ expo (G.resistB N) k * G.rA N ε k := by
  rw [G.rA_eq hN, G.rA_eq hN, expo]
  by_cases h1 : G.resistB N ≤ k
  · simp only [h1, show G.resistB N ≤ k + 1 by omega, ite_true, zpow_one]
    nlinarith
  · by_cases h2 : k + 1 < G.resistB N
    · simp only [h1, h2, show ¬ G.resistB N ≤ k + 1 by omega, ite_false, ite_true,
        zpow_neg_one]
      field_simp
      linarith
    · simp only [h1, h2, show G.resistB N ≤ k + 1 by omega, ite_false, ite_true, zpow_zero]
      linarith

theorem kdown_le {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ} (hk : k < N) :
    G.kdown N ε (k + 1) ≤ 2 * N * ε ^ expo (G.resistB N) k * G.kup N ε k := by
  have hN : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk1 : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hb := G.one_sub_rA_le hN hε hε1 k
  have hr : 0 ≤ G.rA N ε k := by unfold rA; split_ifs <;> linarith
  have hp : 0 ≤ ε ^ expo (G.resistB N) k := (zpow_pos hε _).le
  unfold kdown kup
  push_cast
  have hc : ((k : ℝ) + 1) / N ≤ N * (((N : ℝ) - k) / N) := by
    rw [mul_div_assoc', le_div_iff₀ hN', div_mul_cancel₀ _ hN'.ne']
    nlinarith
  calc ((k : ℝ) + 1) / N * (1 - G.rA N ε (k + 1))
      ≤ ((k : ℝ) + 1) / N * (2 * ε ^ expo (G.resistB N) k * G.rA N ε k) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ N * (((N : ℝ) - k) / N) * (2 * ε ^ expo (G.resistB N) k * G.rA N ε k) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem prod_zpow_eq {ε : ℝ} (hε : ε ≠ 0) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ k ∈ s, ε ^ f k = ε ^ ∑ k ∈ s, f k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, zpow_add₀ hε]

/-- The `A` basin outweighs the `B` basin: along any path from `z < N` up to
`N`, the exponents sum to at least `1`. -/
theorem one_le_sum_expo {m N z : ℕ} (hm : 2 * m < N) (hz : z < N) :
    1 ≤ ∑ k ∈ Ico z N, expo m k := by
  have hge : ∀ k, -1 ≤ expo m k := fun k => by unfold expo; split_ifs <;> norm_num
  by_cases hmz : m ≤ z
  · rw [sum_congr rfl fun k hk => (show expo m k = 1 by
      rw [mem_Ico] at hk; simp [expo, show m ≤ k by omega])]
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    omega
  · rw [← sum_Ico_consecutive _ (show z ≤ m by omega) (show m ≤ N by omega)]
    have h1 : -((m - z : ℕ) : ℤ) ≤ ∑ k ∈ Ico z m, expo m k := by
      have := sum_le_sum (s := Ico z m) fun k _ => hge k
      simpa using this
    have h2 : ∑ k ∈ Ico m N, expo m k = ((N - m : ℕ) : ℤ) := by
      rw [sum_congr rfl fun k hk => (show expo m k = 1 by
        rw [mem_Ico] at hk; simp [expo, hk.1])]
      simp
    omega

/-- **Ratio bound**: `π z ≤ C ε π N` for `z < N`. -/
theorem w_le {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 2 * G.resistB N < N) {z : ℕ}
    (hz : z < N) :
    BirthDeath.w (G.kup N ε) (G.kdown N ε) z ≤
      (2 * N) ^ N * ε * BirthDeath.w (G.kup N ε) (G.kdown N ε) N := by
  have hup : ∀ k < N, 0 < G.kup N ε k := fun k hk => G.kup_pos hε hε1 hk
  have hdown : ∀ k, 0 < k → k ≤ N → 0 < G.kdown N ε k := fun k hk hkN =>
    G.kdown_pos hε hε1 hk hkN
  have hwN := BirthDeath.w_pos hup hdown N le_rfl
  rw [BirthDeath.w_eq_mul_prod hup hdown hz.le, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hwN.le
  have hN1 : (1 : ℝ) ≤ 2 * N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  calc ∏ k ∈ Ico z N, G.kdown N ε (k + 1) / G.kup N ε k
      ≤ ∏ k ∈ Ico z N, (2 * N * ε ^ expo (G.resistB N) k) := by
        refine prod_le_prod₀ (fun k hk => ?_) (fun k hk => ?_)
        · rw [mem_Ico] at hk
          exact div_nonneg (hdown _ (by omega) (by omega)).le (hup k hk.2).le
        · rw [mem_Ico] at hk
          rw [div_le_iff₀ (hup k hk.2)]
          exact G.kdown_le hε hε1 hk.2
    _ = (2 * N) ^ (N - z) * ε ^ ∑ k ∈ Ico z N, expo (G.resistB N) k := by
        rw [prod_mul_distrib, prod_const, Nat.card_Ico, prod_zpow_eq hε.ne']
    _ ≤ (2 * N) ^ N * ε := by
        refine mul_le_mul (pow_le_pow_right₀ hN1 (Nat.sub_le _ _)) ?_ (zpow_pos hε _).le
          (by positivity)
        calc ε ^ ∑ k ∈ Ico z N, expo (G.resistB N) k ≤ ε ^ (1 : ℤ) :=
              zpow_le_zpow_right_of_le_one₀ hε hε1 (one_le_sum_expo hm hz)
          _ = ε := zpow_one ε

/-- Lower bound on the stationary probability of the all-`A` state. -/
theorem pi_N_ge {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 2 * G.resistB N < N) :
    1 / (1 + N * ((2 * N) ^ N * ε)) ≤ BirthDeath.pi (G.kup N ε) (G.kdown N ε) N N := by
  have hup : ∀ k < N, 0 < G.kup N ε k := fun k hk => G.kup_pos hε hε1 hk
  have hdown : ∀ k, 0 < k → k ≤ N → 0 < G.kdown N ε k := fun k hk hkN =>
    G.kdown_pos hε hε1 hk hkN
  set W := BirthDeath.w (G.kup N ε) (G.kdown N ε)
  have hwN : 0 < W N := BirthDeath.w_pos hup hdown N le_rfl
  have hsum : ∑ k ∈ range N, W k ≤ N * ((2 * N) ^ N * ε) * W N := by
    calc ∑ k ∈ range N, W k ≤ ∑ _k ∈ range N, (2 * N) ^ N * ε * W N :=
          sum_le_sum fun k hk => G.w_le hε hε1 hm (mem_range.1 hk)
      _ = _ := by simp; ring
  have hK : 0 ≤ (N : ℝ) * ((2 * N) ^ N * ε) := by positivity
  unfold BirthDeath.pi
  rw [sum_range_succ, div_le_div_iff₀ (by positivity) (by
    have := BirthDeath.sum_w_pos (fun k hk => (hup k hk).le) hdown (N := N)
    rwa [sum_range_succ] at this)]
  nlinarith

/-- **KMR selection of the risk-dominant convention (full one-revision
chain).** If `A` is risk dominant, then for every large enough population and
every choice of stationary distributions `μ ε` of the KMR chain, the
probability of the all-`A` state tends to `1` as `ε → 0⁺`. -/
theorem kmr_selects_riskDominant (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → ℕ → ℝ,
      (∀ ε, 0 < ε → ε ≤ 1 → BirthDeath.IsStationaryDist (G.kup N ε) (G.kdown N ε) N (μ ε)) →
      Tendsto (fun ε => μ ε N) (𝓝[>] 0) (𝓝 1) := by
  rw [riskDominant_iff] at h
  have hgap : 0 < 1 - 2 * G.pstar := by linarith
  filter_upwards [eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / (1 - 2 * G.pstar))] with N hN hNb
  intro μ hμ
  -- the basin condition `2 m < N`
  have hm : 2 * G.resistB N < N := by
    have hc : (G.resistB N : ℝ) < N * G.pstar + 1 :=
      Nat.ceil_lt_add_one (by have := G.pstar_pos; positivity)
    have : 2 ≤ (N : ℝ) * (1 - 2 * G.pstar) := by rwa [div_le_iff₀ hgap] at hNb
    have : (2 * G.resistB N : ℝ) < N := by linarith
    exact_mod_cast this
  set K : ℝ := N * (2 * N) ^ N
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 :=
    by filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds one_pos)]
        with ε h1 h2 using ⟨h1, h2⟩
  have hlow : Tendsto (fun ε : ℝ => 1 / (1 + K * ε)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ε : ℝ => 1 / (1 + K * ε)) (𝓝 0) (𝓝 (1 / (1 + K * 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id))
        (by simp)
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with ε ⟨hε, hε1⟩
    have hup : ∀ z < N, 0 ≤ G.kup N ε z := fun z hz => (G.kup_pos hε hε1 hz).le
    have hdown : ∀ z, 0 < z → z ≤ N → 0 < G.kdown N ε z := fun z hz hzN =>
      G.kdown_pos hε hε1 hz hzN
    rw [BirthDeath.eq_pi hup hdown (hμ ε hε hε1) N le_rfl]
    have := G.pi_N_ge hε hε1 hm
    have e : (N : ℝ) * ((2 * N) ^ N * ε) = K * ε := by ring
    rwa [e] at this
  · filter_upwards [hev] with ε ⟨hε, hε1⟩
    have hs := (hμ ε hε hε1).2.1
    rw [sum_range_succ] at hs
    have : 0 ≤ ∑ z ∈ range N, μ ε z :=
      sum_nonneg fun z hz => (hμ ε hε hε1).1 z (by rw [mem_range] at hz; omega)
    linarith

/-- Every other state's stationary probability tends to `0`. -/
theorem kmr_tendsto_zero (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → ℕ → ℝ,
      (∀ ε, 0 < ε → ε ≤ 1 → BirthDeath.IsStationaryDist (G.kup N ε) (G.kdown N ε) N (μ ε)) →
      ∀ z < N, Tendsto (fun ε => μ ε z) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [G.kmr_selects_riskDominant h] with N hN μ hμ z hz
  have h1 : Tendsto (fun ε => 1 - μ ε N) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hN μ hμ)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 :=
    by filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds one_pos)]
        with ε h1 h2 using ⟨h1, h2⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [hev] with ε ⟨hε, hε1⟩
    exact (hμ ε hε hε1).1 z hz.le
  · filter_upwards [hev] with ε ⟨hε, hε1⟩
    have hs := (hμ ε hε hε1).2.1
    rw [sum_range_succ] at hs
    have : μ ε z ≤ ∑ k ∈ range N, μ ε k :=
      single_le_sum (fun k hk => (hμ ε hε hε1).1 k (by rw [mem_range] at hk; omega))
        (mem_range.2 hz)
    linarith

end Coord

/-- Non-vacuity: in the stag hunt, the KMR chain selects the all-`A` (safe,
hare) convention in every large enough population, although all-`B` (stag)
is payoff dominant. -/
theorem stagHunt_kmr : ∀ᶠ N : ℕ in atTop,
    Tendsto (fun ε => BirthDeath.pi (stagHunt.kup N ε) (stagHunt.kdown N ε) N N)
      (𝓝[>] 0) (𝓝 1) := by
  filter_upwards [stagHunt.kmr_selects_riskDominant stagHunt_riskDominant] with N hN
  exact hN _ fun ε hε hε1 => stagHunt.kmr_isStationaryDist hε hε1

end StochasticStability

end Econ
