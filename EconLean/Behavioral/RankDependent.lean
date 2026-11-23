/-
# Rank-dependent utility and prospect theory

References.
* J. Quiggin (1982), "A Theory of Anticipated Utility", *JEBO* 3(4):
  rank-dependent utility (RDU).
* D. Kahneman and A. Tversky (1979), "Prospect Theory", *Econometrica* 47(2):
  original prospect theory (OPT), value `Σ π(pᵢ) v(xᵢ)`.
* A. Tversky and D. Kahneman (1992), "Advances in Prospect Theory: Cumulative
  Representation of Uncertainty", *JRU* 5(4): cumulative prospect theory (CPT).
* MWG §6.D (first-order stochastic dominance).

**The setting.** Outcomes lie on a fixed finite grid `x₀ < x₁ < … < xₙ`; we
only ever need the index `k ∈ {0, …, n}` and the (vN–M / value) utility of
each grid point `u k`, which is weakly increasing in `k` when "more is better".
A lottery is a probability vector `p` on `{0, …, n}`. Working on a common grid
loses no generality for comparing finitely many simple lotteries: take the
union of their supports. (Overlap note: the uncertainty thread builds vN–M
lotteries; ours is a deliberately minimal ranked-grid version, kept in its own
namespace `Econ.RankDependent`.)

The **decumulative** distribution is `G p k = Prob(outcome ≥ xₖ)`;
`G p 0 = 1` and `G p (n+1) = 0`. `p` **first-order stochastically dominates**
`q` when `G p k ≥ G q k` for all `k` (MWG Def. 6.D.1, in decumulative form).

**RDU (Quiggin).** With a probability weighting function `w : [0,1] → [0,1]`,
`w 0 = 0`, `w 1 = 1`, increasing, outcome `k` gets decision weight
`πₖ = w(G p k) - w(G p (k+1))` (the weight of "at least this good" minus the
weight of "strictly better"), and `RDU(p) = Σₖ πₖ u k`. With `w = id`, RDU is
expected utility. RDU respects FOSD (`rdu_mono`), strictly so when `w` and `u`
are strictly increasing (`rdu_strictMono`).

**OPT (Kahneman–Tversky 1979)** weights each probability separately,
`Σ π(pₖ) v k`. Whenever `π` is strictly subadditive somewhere (as KT's
overweighting of small probabilities makes it), OPT violates FOSD
(`opt_violates_fosd`). This defect motivated both RDU and CPT.

**CPT (Tversky–Kahneman 1992)**: outcomes are gains or losses relative to a
reference grid point `r` with `v r = 0`; gains are weighted rank-dependently
from the best outcome with `w⁺`, losses from the worst with `w⁻`. In layer
(Choquet) form

    CPT(p) = Σ_{k=r+1}^{n} w⁺(G p k)(v k - v (k-1))
           - Σ_{k=0}^{r-1} w⁻(F p k)(v (k+1) - v k),

where `F p k = Prob(outcome ≤ xₖ)`. CPT respects FOSD (`cpt_mono`), reduces to
expected value of `v` without weighting (`cpt_id`), and with loss aversion
`v(-x) < -v(x)` rejects every fair 50–50 gamble (`cpt_rejects_fair_coin`),
in particular for the TK (1992) power value function (`tkValue`).
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Econ

namespace RankDependent

open Finset

/-- A simple lottery on the grid `{0, …, n}`: `p k` is the probability of
outcome `k`, and `p k = 0` off the grid. Convention: the index order *is* the
ranking of outcomes (worst `0`, best `n`), so the utility/value functions used
with RDU, OPT and CPT below should be monotone on the grid. -/
structure Lottery (n : ℕ) where
  /-- probability of grid point `k` -/
  p : ℕ → ℝ
  /-- probabilities are nonnegative -/
  nonneg : ∀ k, 0 ≤ p k
  /-- and sum to one over the grid -/
  sum_eq_one : ∑ k ∈ range (n + 1), p k = 1
  /-- no probability off the grid (so a lottery is determined by its grid values) -/
  eq_zero_of_lt : ∀ k, n < k → p k = 0

variable {n : ℕ}

/-- Decumulative distribution: `G p k = Prob(outcome index ≥ k)`. -/
def G (p : Lottery n) (k : ℕ) : ℝ := ∑ j ∈ Ico k (n + 1), p.p j

/-- Cumulative distribution: `F p k = Prob(outcome index ≤ k)`. -/
def F (p : Lottery n) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), p.p j

theorem G_zero (p : Lottery n) : G p 0 = 1 := by
  rw [G, ← p.sum_eq_one, range_eq_Ico]

theorem G_of_lt (p : Lottery n) {k : ℕ} (hk : n < k) : G p k = 0 := by
  simp [G, Ico_eq_empty_of_le (by omega : n + 1 ≤ k)]

theorem G_succ (p : Lottery n) {k : ℕ} (hk : k ≤ n) : G p k = p.p k + G p (k + 1) := by
  unfold G
  rw [← Finset.sum_eq_sum_Ico_succ_bot (by omega)]

theorem G_nonneg (p : Lottery n) (k : ℕ) : 0 ≤ G p k :=
  sum_nonneg fun j _ => p.nonneg j

theorem G_le_one (p : Lottery n) (k : ℕ) : G p k ≤ 1 := by
  rw [← p.sum_eq_one]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj; simp only [mem_Ico, mem_range] at hj ⊢; omega
  · intro j _ _; exact p.nonneg j

/-- `F p k = 1 - G p (k+1)` for grid points. -/
theorem F_eq (p : Lottery n) {k : ℕ} (hk : k ≤ n) : F p k = 1 - G p (k + 1) := by
  rw [F, G, ← p.sum_eq_one, ← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ n + 1)]
  ring

/-- Expected utility of `u` under `p`. -/
def eu (u : ℕ → ℝ) (p : Lottery n) : ℝ := ∑ k ∈ range (n + 1), p.p k * u k

/-- `p` first-order stochastically dominates `q`: for every threshold, `p` puts
at least as much probability on outcomes at or above it. -/
def FOSD (p q : Lottery n) : Prop := ∀ k, G q k ≤ G p k

/-- `u` is weakly increasing on the grid. -/
def MonotoneOnGrid (n : ℕ) (u : ℕ → ℝ) : Prop := ∀ k, k < n → u k ≤ u (k + 1)

/-! ### Summation by parts (the "layer" form of an expectation) -/

/-- Abel summation for any weights `W` and utilities `u`. -/
theorem abel (W u : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range (m + 1), (W k - W (k + 1)) * u k =
      W 0 * u 0 + ∑ k ∈ range m, W (k + 1) * (u (k + 1) - u k) - W (m + 1) * u m := by
  induction m with
  | zero => rw [sum_range_one, sum_range_zero]; ring
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- The **layer form** of expected utility:
`E u = u 0 + Σ_{k<n} Prob(≥ k+1) (u (k+1) - u k)`. -/
theorem eu_eq_layer (u : ℕ → ℝ) (p : Lottery n) :
    eu u p = u 0 + ∑ k ∈ range n, G p (k + 1) * (u (k + 1) - u k) := by
  have h := abel (G p) u n
  have hdiff : ∀ k ∈ range (n + 1), (G p k - G p (k + 1)) * u k = p.p k * u k := by
    intro k hk
    rw [G_succ p (by simpa [Nat.lt_succ_iff] using hk)]
    ring
  rw [sum_congr rfl hdiff, G_zero, G_of_lt p (Nat.lt_succ_self n)] at h
  rw [eu, h]
  ring

/-! ### First-order stochastic dominance (MWG Prop. 6.D.1, finite grid) -/

/-- **MWG Proposition 6.D.1.** `p` FOSD `q` iff every weakly increasing `u`
gives `p` at least the expected utility of `q`. -/
theorem fosd_iff_eu (p q : Lottery n) :
    FOSD p q ↔ ∀ u : ℕ → ℝ, MonotoneOnGrid n u → eu u q ≤ eu u p := by
  constructor
  · intro h u hu
    rw [eu_eq_layer, eu_eq_layer]
    gcongr with k hk
    · exact sub_nonneg.2 (hu k (mem_range.1 hk))
    · exact h (k + 1)
  · intro h k
    by_cases hk : k ≤ n
    · -- Test function: the indicator of `{j ≥ k}`; its expectation is `G · k`.
      have key : ∀ r : Lottery n, eu (fun j => if k ≤ j then 1 else 0) r = G r k := by
        intro r
        unfold eu G
        rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ n + 1)]
        rw [sum_eq_zero (fun j hj => by simp only [mem_Ico] at hj; simp [show ¬ k ≤ j by omega])]
        simp only [zero_add]
        exact sum_congr rfl fun j hj => by simp only [mem_Ico] at hj; simp [hj.1]
      have := h (fun j => if k ≤ j then 1 else 0) (fun j _ => by dsimp only; split_ifs <;> first | omega | norm_num)
      rwa [key, key] at this
    · rw [G_of_lt q (by omega), G_of_lt p (by omega)]

/-! ### Rank-dependent utility (Quiggin 1982) -/

/-- Quiggin's decision weight of outcome `k`: `w(Prob ≥ k) - w(Prob > k)`. -/
def decisionWeight (w : ℝ → ℝ) (p : Lottery n) (k : ℕ) : ℝ := w (G p k) - w (G p (k + 1))

/-- Rank-dependent utility `Σₖ πₖ u k`. -/
def rdu (w : ℝ → ℝ) (u : ℕ → ℝ) (p : Lottery n) : ℝ :=
  ∑ k ∈ range (n + 1), decisionWeight w p k * u k

/-- Layer (Choquet) form of RDU, for weighting functions normalised by
`w 0 = 0` and `w 1 = 1`. -/
theorem rdu_eq_layer {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) (u : ℕ → ℝ) (p : Lottery n) :
    rdu w u p = u 0 + ∑ k ∈ range n, w (G p (k + 1)) * (u (k + 1) - u k) := by
  have h := abel (fun k => w (G p k)) u n
  rw [rdu]
  simp only [decisionWeight]
  rw [h, G_zero, G_of_lt p (Nat.lt_succ_self n), hw0, hw1]
  ring

/-- Decision weights of an increasing, normalised `w` are nonnegative and sum
to one: RDU is an expectation under a distorted probability vector. -/
theorem decisionWeight_nonneg {w : ℝ → ℝ} (hw : Monotone w) (p : Lottery n) {k : ℕ}
    (hk : k ≤ n) : 0 ≤ decisionWeight w p k := by
  unfold decisionWeight
  rw [sub_nonneg, G_succ p hk]
  exact hw (le_add_of_nonneg_left (p.nonneg k))

theorem sum_decisionWeight {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) (p : Lottery n) :
    ∑ k ∈ range (n + 1), decisionWeight w p k = 1 := by
  have := rdu_eq_layer hw0 hw1 (fun _ => 1) p
  simpa [rdu] using this

/-- **Without probability weighting RDU is expected utility.** -/
theorem rdu_id (u : ℕ → ℝ) (p : Lottery n) : rdu id u p = eu u p := by
  rw [rdu_eq_layer rfl rfl, eu_eq_layer]
  rfl

/-- **Quiggin: RDU respects first-order stochastic dominance.** If `w` is
increasing and `u` is increasing on the grid, `p` FOSD `q` implies
`RDU(q) ≤ RDU(p)`. -/
theorem rdu_mono {w : ℝ → ℝ} (hw : Monotone w) (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    {u : ℕ → ℝ} (hu : MonotoneOnGrid n u) {p q : Lottery n} (h : FOSD p q) :
    rdu w u q ≤ rdu w u p := by
  rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1]
  gcongr with k hk
  · exact sub_nonneg.2 (hu k (mem_range.1 hk))
  · exact hw (h (k + 1))

/-- **Strict version.** If moreover `w` and `u` are strictly increasing and the
dominance is strict at some threshold, RDU strictly prefers `p`. -/
theorem rdu_strictMono {w : ℝ → ℝ} (hw : StrictMono w) (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    {u : ℕ → ℝ} (hu : ∀ k, k < n → u k < u (k + 1)) {p q : Lottery n} (h : FOSD p q)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hk₀n : k₀ ≤ n) (hstrict : G q k₀ < G p k₀) :
    rdu w u q < rdu w u p := by
  rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1, add_lt_add_iff_left]
  apply sum_lt_sum
  · intro k hk
    exact mul_le_mul_of_nonneg_right (hw.monotone (h (k + 1)))
      (sub_nonneg.2 (hu k (mem_range.1 hk)).le)
  · refine ⟨k₀ - 1, mem_range.2 (by omega), ?_⟩
    have e : k₀ - 1 + 1 = k₀ := by omega
    rw [e]
    exact mul_lt_mul_of_pos_right (hw hstrict) (sub_pos.2 (by simpa [e] using hu (k₀ - 1) (by omega)))

/-! ### Original prospect theory violates FOSD (Kahneman–Tversky 1979) -/

/-- Original prospect theory value: each probability is weighted separately. -/
def opt (π : ℝ → ℝ) (v : ℕ → ℝ) (p : Lottery n) : ℝ := ∑ k ∈ range (n + 1), π (p.p k) * v k

/-- **OPT violates FOSD.** Let `π 0 = 0` and suppose `π` is strictly
subadditive at some `a, b > 0` with `a + b ≤ 1` (e.g. small probabilities are
overweighted). Then on a four-point grid there are a strictly increasing value
function `v` and lotteries `p` FOSD `q` with `OPT(q) > OPT(p)`: splitting the
probability of the best outcome into two slightly worse outcomes raises the
OPT value. -/
theorem opt_violates_fosd {π : ℝ → ℝ} (hπ0 : π 0 = 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b ≤ 1) (hsub : π (a + b) < π a + π b) :
    ∃ (v : ℕ → ℝ) (p q : Lottery 3), (∀ k, k < 3 → v k < v (k + 1)) ∧
      FOSD p q ∧ opt π v p < opt π v q := by
  set D := π a + π b - π (a + b) with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  set M := |π b| + 2 * |π (a + b)| + 1 with hM
  have hMpos : 0 < M := by positivity
  set ε := D / (2 * M) with hε
  have hεpos : 0 < ε := by positivity
  -- value function: v 0 = 0, v 1 = 1, v 2 = 1 + ε, v 3 = 1 + 2ε
  let v : ℕ → ℝ := fun k => if k = 0 then 0 else 1 + (k - 1 : ℝ) * ε
  -- p: mass a+b on the best outcome 3; q: mass a on 1 and b on 2; rest on 0.
  let p : Lottery 3 :=
    { p := fun k => if k = 0 then 1 - (a + b) else if k = 3 then a + b else 0
      nonneg := fun k => by split_ifs <;> linarith
      sum_eq_one := by simp [sum_range_succ]
      eq_zero_of_lt := fun k hk => by simp [show k ≠ 0 by omega, show k ≠ 3 by omega] }
  let q : Lottery 3 :=
    { p := fun k => if k = 0 then 1 - (a + b) else if k = 1 then a else if k = 2 then b else 0
      nonneg := fun k => by split_ifs <;> linarith
      sum_eq_one := by simp [sum_range_succ]; ring
      eq_zero_of_lt := fun k hk => by
        simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega] }
  refine ⟨v, p, q, ?_, ?_, ?_⟩
  · intro k hk
    interval_cases k <;> simp [v] <;> linarith
  · intro k
    simp only [G, p, q]
    rcases Nat.lt_or_ge 3 k with hk | hk
    · simp [Ico_eq_empty_of_le (by omega : 3 + 1 ≤ k)]
    · interval_cases k <;> simp [sum_Ico_succ_top, Finset.sum_range_succ] <;> linarith
  · simp only [opt, p, q, v, sum_range_succ, sum_range_zero]
    norm_num
    rw [hπ0]
    -- OPT(q) - OPT(p) = D + ε (π b - 2 π(a+b)) ≥ D - ε M > 0
    have h1 : -(ε * M) ≤ ε * (π b - 2 * π (a + b)) := by
      rw [neg_le, ← mul_neg]
      apply mul_le_mul_of_nonneg_left _ hεpos.le
      have := neg_abs_le (π b); have := le_abs_self (π (a + b)); rw [hM]; linarith
    have h2 : ε * M = D / 2 := by rw [hε]; field_simp
    nlinarith

/-! ### Cumulative prospect theory (Tversky–Kahneman 1992) -/

/-- CPT value in layer form, with reference grid point `r` (the reference
point must be a grid point; the formula builds in the normalizations
`v r = 0` and `w±(0) = 0`, i.e. it equals TK's CPT for `v - v r` when
`w±(0) = 0`): gains above `r` weighted by `wp` from the top, losses below `r`
weighted by `wm` from the bottom. -/
def cpt (wp wm : ℝ → ℝ) (v : ℕ → ℝ) (r : ℕ) (p : Lottery n) : ℝ :=
  (∑ k ∈ Ico (r + 1) (n + 1), wp (G p k) * (v k - v (k - 1))) -
    ∑ k ∈ range r, wm (F p k) * (v (k + 1) - v k)

/-- **CPT respects FOSD** (for increasing weighting functions and value). -/
theorem cpt_mono {wp wm : ℝ → ℝ} (hwp : Monotone wp) (hwm : Monotone wm) {v : ℕ → ℝ}
    (hv : MonotoneOnGrid n v) {r : ℕ} (hr : r ≤ n) {p q : Lottery n} (h : FOSD p q) :
    cpt wp wm v r q ≤ cpt wp wm v r p := by
  unfold cpt
  apply sub_le_sub
  · apply sum_le_sum
    intro k hk
    simp only [mem_Ico] at hk
    have := hv (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    exact mul_le_mul_of_nonneg_right (hwp (h k)) (sub_nonneg.2 this)
  · apply sum_le_sum
    intro k hk
    have hk' := mem_range.1 hk
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.2 (hv k (by omega)))
    apply hwm
    rw [F_eq p (by omega), F_eq q (by omega)]
    linarith [h (k + 1)]

/-- **Without probability weighting, CPT is the expected value of `v`** (when
the reference point `r` has value `0`). -/
theorem cpt_id {v : ℕ → ℝ} {r : ℕ} (hr : r ≤ n) (hvr : v r = 0) (p : Lottery n) :
    cpt id id v r p = eu v p := by
  rw [eu_eq_layer, cpt]
  simp only [id]
  -- gains: reindex `k ↦ k + 1`
  have hg : ∑ k ∈ Ico (r + 1) (n + 1), G p k * (v k - v (k - 1)) =
      ∑ k ∈ Ico r n, G p (k + 1) * (v (k + 1) - v k) := by
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    apply sum_congr (by congr 1; omega)
    intro k _
    rw [show r + 1 + k - 1 = r + k by omega, show r + 1 + k = r + k + 1 by omega]
  -- losses: `F = 1 - G(k+1)` and telescoping
  have hl : ∑ k ∈ range r, F p k * (v (k + 1) - v k) =
      (v r - v 0) - ∑ k ∈ range r, G p (k + 1) * (v (k + 1) - v k) := by
    have : ∀ k ∈ range r, F p k * (v (k + 1) - v k) =
        (v (k + 1) - v k) - G p (k + 1) * (v (k + 1) - v k) := by
      intro k hk
      rw [F_eq p (by have := mem_range.1 hk; omega)]
      ring
    rw [sum_congr rfl this, sum_sub_distrib, sum_range_sub (fun k => v k)]
  rw [hg, hl, hvr, ← sum_range_add_sum_Ico _ hr]
  ring

/-- **CPT without losses is RDU**: with the reference point at the worst grid
point (`r = 0`, `v 0 = 0`), CPT with gain weighting `wp` is Quiggin's RDU. -/
theorem cpt_zero_eq_rdu {wp : ℝ → ℝ} (hw0 : wp 0 = 0) (hw1 : wp 1 = 1) (wm : ℝ → ℝ)
    {v : ℕ → ℝ} (hv0 : v 0 = 0) (p : Lottery n) :
    cpt wp wm v 0 p = rdu wp v p := by
  rw [rdu_eq_layer hw0 hw1, cpt, hv0, range_zero, sum_empty, sub_zero,
    sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [zero_add]
  refine sum_congr rfl fun k _ => ?_
  rw [show 1 + k - 1 = k by omega, add_comm 1 k]

/-- The status quo (all mass on the reference point `r`) has CPT value `0`. -/
theorem cpt_statusQuo {wp wm : ℝ → ℝ} (hwp : wp 0 = 0) (hwm : wm 0 = 0) (v : ℕ → ℝ) {r : ℕ}
    (hr : r ≤ n) (p : Lottery n) (hp : ∀ k, k ≤ n → k ≠ r → p.p k = 0) :
    cpt wp wm v r p = 0 := by
  unfold cpt
  rw [sum_eq_zero, sum_eq_zero]
  · simp
  · intro k hk
    have hk' := mem_range.1 hk
    rw [F, sum_eq_zero fun j hj => hp j (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega), hwm, zero_mul]
  · intro k hk
    simp only [mem_Ico] at hk
    rw [G, sum_eq_zero fun j hj => hp j (by simp only [mem_Ico] at hj; omega)
      (by simp only [mem_Ico] at hj; omega), hwp, zero_mul]

/-- The fair 50–50 gamble on the grid `{loss, 0, gain}` (`n = 2`, `r = 1`). -/
noncomputable def fairCoin : Lottery 2 where
  p := fun k => if k = 0 ∨ k = 2 then 1 / 2 else 0
  nonneg := fun k => by split_ifs <;> norm_num
  sum_eq_one := by simp [sum_range_succ]; norm_num
  eq_zero_of_lt := fun k hk => by simp; omega

/-- **Loss aversion makes CPT reject fair gambles.** Grid point `0` is the loss,
`1` the reference (`v 1 = 0`), `2` the gain. If the loss hurts more than the
gain helps (`v 0 + v 2 < 0`, with `v 2 ≥ 0`) and `0 < w⁺(1/2) ≤ w⁻(1/2)`, the
fair coin is worth strictly less than the status quo (`CPT = 0`). -/
theorem cpt_rejects_fair_coin {wp wm : ℝ → ℝ} {v : ℕ → ℝ} (hv1 : v 1 = 0) (hv2 : 0 ≤ v 2)
    (hloss : v 0 + v 2 < 0) (hw : 0 < wp (1 / 2)) (hww : wp (1 / 2) ≤ wm (1 / 2)) :
    cpt wp wm v 1 fairCoin < 0 := by
  simp only [cpt, G, F, fairCoin, sum_range_succ, sum_range_zero, hv1]
  norm_num
  nlinarith

/-- The Tversky–Kahneman (1992) value function: `x^α` for gains,
`-λ (-x)^β` for losses (TK estimate `α = β = 0.88`, `λ = 2.25`). -/
noncomputable def tkValue (α β lam : ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ α else -lam * (-x) ^ β

/-- With `α = β` and `λ > 1`, the TK value function is loss averse:
`v(-x) < -v(x)` for every `x > 0`. -/
theorem tkValue_lossAverse {α lam : ℝ} (hlam : 1 < lam) {x : ℝ} (hx : 0 < x) :
    tkValue α α lam (-x) < -tkValue α α lam x := by
  unfold tkValue
  rw [ite_eq_right (by linarith), ite_eq_left hx.le, neg_neg]
  have := Real.rpow_pos_of_pos hx α
  nlinarith

/-- **TK (1992) agents reject every fair 50–50 gamble `±x`.** The grid is
`{-x, 0, x}` (point `k` is the outcome `(k - 1) x`) and the reference point is
`0`. Assumes `α > 0`, `λ > 1`, `0 < w⁺(1/2) ≤ w⁻(1/2)`. -/
theorem tk_rejects_fair_coin {α lam : ℝ} (hα : 0 < α) (hlam : 1 < lam) {x : ℝ} (hx : 0 < x)
    {wp wm : ℝ → ℝ} (hw : 0 < wp (1 / 2)) (hww : wp (1 / 2) ≤ wm (1 / 2)) :
    cpt wp wm (fun k => tkValue α α lam (((k : ℝ) - 1) * x)) 1 fairCoin < 0 := by
  apply cpt_rejects_fair_coin _ _ _ hw hww
  · simp [tkValue, Real.zero_rpow hα.ne']
  · simp only [tkValue]; norm_num; rw [ite_eq_left hx.le]; exact (Real.rpow_pos_of_pos hx α).le
  · have := tkValue_lossAverse (α := α) hlam hx
    simp only [Nat.cast_zero, Nat.cast_ofNat, zero_sub, neg_one_mul]
    norm_num
    linarith

end RankDependent

end Econ
