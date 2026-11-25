/-
# Reputation: the Fudenberg–Levine bound

Fudenberg and Levine (1989), "Reputation and equilibrium selection in games with a patient
player", Econometrica; Mailath–Samuelson (2006), Ch. 15; Kreps–Wilson (1982), Milgrom–Roberts
(1982). A long-run player faces a sequence of short-run players. With prior probability
`μ₀ > 0` she is a **commitment type** who always plays the action `a*`; otherwise she is
normal. Actions are observed.

Fix any strategy of the normal type and consider the history along which `a*` is played in
every period (what a normal type gets by mimicking the commitment type). Let `q t` be the
probability that the normal type plays `a*` in period `t` on this history. The short-run
player's (correct) probability of `a*` is `p t = μ t + (1 − μ t) q t`, and after observing
`a*` Bayes' rule gives `μ (t+1) = μ t / p t` (`reputationPosterior`).

* `bounded_surprises` (the Fudenberg–Levine counting lemma): the number of periods in which
  `p t ≤ π` (for `π < 1`) is at most `log μ₀ / log π`, whatever the normal type's strategy.
* `discounted_ge_of_bad_card`: a payoff stream that is at least `v` except in at most `K`
  periods, where it is at least `m ≤ v`, has discounted average at least
  `δ^K v + (1 − δ^K) m`.
* `reputation_bound`: hence if the short-run player's best responses give the long-run player
  at least `v` whenever `p t > π`, then by mimicking `a*` the normal type gets at least
  `δ^K v + (1 − δ^K) m` with `K = ⌊log μ₀ / log π⌋`, a bound independent of the equilibrium.
* `reputation_limit`: as `δ → 1` this tends to `v`, uniformly in the normal type's strategy and
  the short-run responses: by mimicking, a patient long-run player secures (almost) her
  Stackelberg payoff for `a*`, and with equilibrium optimality so does her equilibrium payoff.

The game itself (strategies, equilibrium, the short-run best-response correspondence) is not
modelled: the theorem is stated for the probabilities and payoffs along the mimicking path, with
the short-run best-response property as a hypothesis: `π` must be chosen, for the given stage
game, so that every best response to a belief putting more than `π` on `a*` is a best response
to `a*`. Equilibrium optimality (equilibrium payoff ≥ mimicking payoff) is assumed. Imperfect monitoring (Fudenberg–Levine
1992) and mixed commitment types are not formalized.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace Econ

open Finset Filter Topology

/-- The posterior probability of the commitment type after `t` observations of `a*`, when the
normal type plays `a*` with probabilities `q`. -/
noncomputable def reputationPosterior (μ₀ : ℝ) (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => μ₀
  | t + 1 => reputationPosterior μ₀ q t /
      (reputationPosterior μ₀ q t + (1 - reputationPosterior μ₀ q t) * q t)

/-- The short-run player's probability that `a*` is played in period `t`. -/
noncomputable def predictA (μ₀ : ℝ) (q : ℕ → ℝ) (t : ℕ) : ℝ :=
  reputationPosterior μ₀ q t + (1 - reputationPosterior μ₀ q t) * q t

variable {μ₀ : ℝ} {q : ℕ → ℝ}

lemma posterior_mem (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (t : ℕ) :
    0 < reputationPosterior μ₀ q t ∧ reputationPosterior μ₀ q t ≤ 1 := by
  induction t with
  | zero => exact ⟨hμ₀, hμ₁⟩
  | succ t ih =>
    obtain ⟨h0, h1⟩ := ih
    have hp : reputationPosterior μ₀ q t ≤
        reputationPosterior μ₀ q t + (1 - reputationPosterior μ₀ q t) * q t := by
      nlinarith [(hq t).1]
    have hpos : 0 < reputationPosterior μ₀ q t + (1 - reputationPosterior μ₀ q t) * q t := by
      linarith
    simp only [reputationPosterior]
    exact ⟨div_pos h0 hpos, (div_le_one hpos).2 hp⟩

lemma predictA_pos (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (t : ℕ) :
    0 < predictA μ₀ q t := by
  obtain ⟨h0, h1⟩ := posterior_mem hμ₀ hμ₁ hq t
  unfold predictA; nlinarith [(hq t).1]

/-- `μ T = μ₀ / ∏_{t<T} p t`. -/
lemma posterior_mul_prod (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (T : ℕ) :
    reputationPosterior μ₀ q T * ∏ t ∈ range T, predictA μ₀ q t = μ₀ := by
  induction T with
  | zero => simp [reputationPosterior]
  | succ T ih =>
    have key : reputationPosterior μ₀ q (T + 1) * predictA μ₀ q T =
        reputationPosterior μ₀ q T := by
      have hp := predictA_pos hμ₀ hμ₁ hq T
      unfold predictA at hp ⊢
      simp only [reputationPosterior]
      field_simp
    rw [prod_range_succ, mul_comm (∏ t ∈ range T, predictA μ₀ q t), ← mul_assoc, key, ih]

/-- **Bounded surprises** (Fudenberg–Levine 1989): among the first `T` periods, at most
`log μ₀ / log π` have `p t ≤ π`, for any `0 < π < 1`. -/
theorem bounded_surprises (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) (T : ℕ) :
    (((range T).filter fun t => predictA μ₀ q t ≤ π).card : ℝ) ≤ Real.log μ₀ / Real.log π := by
  set B := (range T).filter fun t => predictA μ₀ q t ≤ π
  have hp1 : ∀ t, predictA μ₀ q t ≤ 1 := fun t => by
    obtain ⟨h0, h1⟩ := posterior_mem hμ₀ hμ₁ hq t
    unfold predictA; nlinarith [(hq t).2]
  -- `μ₀ ≤ ∏ p t ≤ π ^ |B|`
  have hprod : μ₀ ≤ ∏ t ∈ range T, predictA μ₀ q t := by
    have h := posterior_mul_prod hμ₀ hμ₁ hq T
    have h1 := (posterior_mem hμ₀ hμ₁ hq T).2
    have hP : 0 ≤ ∏ t ∈ range T, predictA μ₀ q t :=
      prod_nonneg fun t _ => (predictA_pos hμ₀ hμ₁ hq t).le
    nlinarith
  have hB : ∏ t ∈ range T, predictA μ₀ q t ≤ π ^ B.card := by
    rw [← prod_filter_mul_prod_filter_not (range T) (fun t => predictA μ₀ q t ≤ π)]
    have h1 : ∏ t ∈ B, predictA μ₀ q t ≤ π ^ B.card := by
      rw [← prod_const]
      exact prod_le_prod₀ (fun t _ => (predictA_pos hμ₀ hμ₁ hq t).le)
        (fun t ht => (mem_filter.1 ht).2)
    have h2 : ∏ t ∈ (range T).filter (fun t => ¬ predictA μ₀ q t ≤ π), predictA μ₀ q t ≤ 1 :=
      prod_le_one₀ (fun t _ => (predictA_pos hμ₀ hμ₁ hq t).le) fun t _ => hp1 t
    have h0 : 0 ≤ ∏ t ∈ B, predictA μ₀ q t := prod_nonneg fun t _ => (predictA_pos hμ₀ hμ₁ hq t).le
    calc (∏ t ∈ B, predictA μ₀ q t) *
          ∏ t ∈ (range T).filter (fun t => ¬ predictA μ₀ q t ≤ π), predictA μ₀ q t
        ≤ (∏ t ∈ B, predictA μ₀ q t) * 1 := mul_le_mul_of_nonneg_left h2 h0
      _ ≤ π ^ B.card := by rw [mul_one]; exact h1
  have hle : μ₀ ≤ π ^ B.card := hprod.trans hB
  have hlog := Real.log_le_log hμ₀ hle
  rw [Real.log_pow] at hlog
  have hlogπ : Real.log π < 0 := Real.log_neg hπ0 hπ1
  rw [le_div_iff_of_neg hlogπ]
  linarith

/-- A finite set of `K` dates carries at most the discount weight of the first `K` dates. -/
lemma sum_pow_le_sum_range {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (B : Finset ℕ) :
    ∑ t ∈ B, δ ^ t ≤ ∑ t ∈ range B.card, δ ^ t := by
  induction B using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    rw [sum_insert (fun h => lt_irrefl a (hlt a h)), card_insert_of_notMem
      (fun h => lt_irrefl a (hlt a h)), sum_range_succ, add_comm]
    refine add_le_add ih (pow_le_pow_of_le_one hδ0 hδ1 ?_)
    -- all `s.card` elements of `s` are below `a`, so `s.card ≤ a`
    have : s ⊆ range a := fun x hx => mem_range.2 (hlt x hx)
    simpa using card_le_card this

/-- **Discounted payoff with few bad periods**: if `u t ≥ v` outside a finite set of at most
`K` dates and `u t ≥ m` always, with `m ≤ v` and `u` bounded above, then
`(1 − δ) Σ δ^t u t ≥ δ^K v + (1 − δ^K) m`. -/
theorem discounted_ge_of_bad_card {u : ℕ → ℝ} {v m Mx δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hm : ∀ t, m ≤ u t) (hMx : ∀ t, u t ≤ Mx) (hmv : m ≤ v) {B : Finset ℕ} {K : ℕ}
    (hBK : B.card ≤ K) (hgood : ∀ t, t ∉ B → v ≤ u t) :
    δ ^ K * v + (1 - δ ^ K) * m ≤ (1 - δ) * ∑' t, δ ^ t * u t := by
  have hgeo : Summable fun t : ℕ => δ ^ t := summable_geometric_of_lt_one hδ0 hδ1
  -- lower envelope `l t = v − (v − m) 1[t ∈ B]`
  set l : ℕ → ℝ := fun t => v - (v - m) * (if t ∈ B then 1 else 0)
  have hl : ∀ t, l t ≤ u t := fun t => by
    simp only [l]; split_ifs with h
    · linarith [hm t]
    · linarith [hgood t h]
  have hsu : Summable fun t => δ ^ t * u t := by
    refine Summable.of_norm_bounded (g := fun t => δ ^ t * max |m| |Mx|) (hgeo.mul_right _) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hδ0 t)
    rcases le_total 0 (u t) with h | h
    · rw [abs_of_nonneg h]; exact (hMx t).trans ((le_abs_self _).trans (le_max_right _ _))
    · rw [abs_of_nonpos h]; have := hm t
      exact (neg_le_neg this).trans ((neg_le_abs m).trans (le_max_left _ _))
  have hsl : Summable fun t => δ ^ t * l t := by
    simp only [l, mul_sub]
    exact (hgeo.mul_right v).sub (summable_of_ne_finset_zero (s := B) fun t ht => by simp [ht])
  have hcmp : ∑' t, δ ^ t * l t ≤ ∑' t, δ ^ t * u t :=
    hsl.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (hl t) (pow_nonneg hδ0 t)) hsu
  have hval : ∑' t, δ ^ t * l t = v / (1 - δ) - (v - m) * ∑ t ∈ B, δ ^ t := by
    simp only [l, mul_sub]
    rw [(hgeo.mul_right v).tsum_sub (summable_of_ne_finset_zero (s := B) fun t ht => by simp [ht]),
      tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1,
      tsum_eq_sum (s := B) (fun t ht => by simp [ht]), mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl fun t ht => by simp [ht]; ring
  have hB : ∑ t ∈ B, δ ^ t ≤ ∑ t ∈ range K, δ ^ t :=
    (sum_pow_le_sum_range hδ0 hδ1.le B).trans
      (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hBK) fun t _ _ => pow_nonneg hδ0 t)
  have hgK : (1 - δ) * ∑ t ∈ range K, δ ^ t = 1 - δ ^ K := by
    rw [mul_comm, geom_sum_mul_neg]
  have h1 : 0 < 1 - δ := by linarith
  have hvm : 0 ≤ v - m := by linarith
  calc δ ^ K * v + (1 - δ ^ K) * m = v - (v - m) * ((1 - δ) * ∑ t ∈ range K, δ ^ t) := by
        rw [hgK]; ring
    _ ≤ v - (v - m) * ((1 - δ) * ∑ t ∈ B, δ ^ t) := by
        have := mul_le_mul_of_nonneg_left hB h1.le
        nlinarith
    _ = (1 - δ) * ∑' t, δ ^ t * l t := by rw [hval]; field_simp
    _ ≤ (1 - δ) * ∑' t, δ ^ t * u t := mul_le_mul_of_nonneg_left hcmp h1.le

/-- The set of dates with `p t ≤ π` is finite, with at most `⌊log μ₀ / log π⌋` elements. -/
lemma surprises_finite (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) :
    ∃ B : Finset ℕ, B.card ≤ ⌊Real.log μ₀ / Real.log π⌋₊ ∧ ∀ t, predictA μ₀ q t ≤ π → t ∈ B := by
  set K := ⌊Real.log μ₀ / Real.log π⌋₊
  have hcard : ∀ T, ((range T).filter fun t => predictA μ₀ q t ≤ π).card ≤ K := fun T =>
    Nat.le_floor (bounded_surprises hμ₀ hμ₁ hq hπ0 hπ1 T)
  -- the filters of initial segments are increasing and bounded, hence eventually constant
  by_contra hne
  push Not at hne
  have grow : ∀ n, ∃ T, n ≤ ((range T).filter fun t => predictA μ₀ q t ≤ π).card := by
    intro n
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨T, hT⟩ := ih
      obtain ⟨t, ht, htB⟩ := hne ((range T).filter fun t => predictA μ₀ q t ≤ π) (hcard T)
      have htT : T ≤ t := by
        by_contra h; push Not at h; exact htB (mem_filter.2 ⟨mem_range.2 h, ht⟩)
      refine ⟨t + 1, ?_⟩
      have hsub : insert t ((range T).filter fun t => predictA μ₀ q t ≤ π) ⊆
          (range (t + 1)).filter fun t => predictA μ₀ q t ≤ π := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_self _), ht⟩
        · obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
          exact mem_filter.2 ⟨mem_range.2 (by have := mem_range.1 hx1; omega), hx2⟩
      have := card_le_card hsub
      rw [card_insert_of_notMem htB] at this
      omega
  obtain ⟨T, hT⟩ := grow (K + 1)
  have := hcard T
  omega

/-- **The Fudenberg–Levine reputation bound**: if, whenever the short-run player assigns
probability more than `π` to `a*`, her best response gives the long-run player at least `v`
(the Stackelberg payoff of `a*`; choose `π` so that every best response to a belief above `π`
is a best response to `a*`), then the normal type's payoff from always playing `a*` is at least
`δ^K v + (1 − δ^K) m`, where `K = ⌊log μ₀ / log π⌋` and `m` is her lowest stage payoff. Combined
with equilibrium optimality (not modelled here), this bounds her equilibrium payoff from below. -/
theorem reputation_bound (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) {u : ℕ → ℝ} {v m Mx δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hm : ∀ t, m ≤ u t) (hMx : ∀ t, u t ≤ Mx) (hmv : m ≤ v)
    (hbr : ∀ t, π < predictA μ₀ q t → v ≤ u t) :
    δ ^ ⌊Real.log μ₀ / Real.log π⌋₊ * v + (1 - δ ^ ⌊Real.log μ₀ / Real.log π⌋₊) * m ≤
      (1 - δ) * ∑' t, δ ^ t * u t := by
  obtain ⟨B, hBK, hB⟩ := surprises_finite hμ₀ hμ₁ hq hπ0 hπ1
  refine discounted_ge_of_bad_card hδ0 hδ1 hm hMx hmv hBK fun t ht => hbr t ?_
  by_contra h; push Not at h; exact ht (hB t h)

/-- **Patient long-run player** (Fudenberg–Levine 1989): the bound tends to `v` as `δ → 1`,
**uniformly** over the normal type's strategy `q` and the short-run players' responses `u`. The
threshold `δ₀` depends only on `μ₀`, `π`, `v`, `m` and `ε`, so it holds for every strategy of
the normal type and every short-run response path at every discount factor above `δ₀`, even
though equilibria change with `δ`. It bounds the payoff from mimicking `a*`; combined with
equilibrium optimality (assumed, not modelled) it bounds the equilibrium payoffs of a given
stage game. -/
theorem reputation_limit (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1)
    {v m : ℝ} (hmv : m ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ < 1, ∀ δ, δ₀ ≤ δ → δ < 1 → ∀ (q' u : ℕ → ℝ) (Mx : ℝ), (∀ t, 0 ≤ q' t ∧ q' t ≤ 1) →
      (∀ t, m ≤ u t) → (∀ t, u t ≤ Mx) → (∀ t, π < predictA μ₀ q' t → v ≤ u t) →
      v - ε ≤ (1 - δ) * ∑' t, δ ^ t * u t := by
  set K := ⌊Real.log μ₀ / Real.log π⌋₊
  -- `δ ^ K → 1` as `δ → 1`
  have hcont : Tendsto (fun δ : ℝ => δ ^ K * v + (1 - δ ^ K) * m) (𝓝 1) (𝓝 v) := by
    have : Continuous fun δ : ℝ => δ ^ K * v + (1 - δ ^ K) * m := by fun_prop
    simpa using this.tendsto 1
  obtain ⟨η, hη, hηc⟩ := Metric.tendsto_nhds_nhds.1 hcont ε hε
  refine ⟨max 0 (1 - η / 2), max_lt (by norm_num) (by linarith),
    fun δ hδ hδ1 q' u Mx hq hm hMx hbr => ?_⟩
  have hδ0 : 0 ≤ δ := (le_max_left _ _).trans hδ
  have hd : dist δ 1 < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right 0 (1 - η / 2)]
  have h1 := hηc hd
  rw [Real.dist_eq, abs_lt] at h1
  have h2 := reputation_bound hμ₀ hμ₁ hq hπ0 hπ1 hδ0 hδ1 hm hMx hmv hbr
  linarith [h1.1]

/-- Witness: a normal type that never plays `a*` (`q = 0`) and prior `μ₀ = 1/2`: one
observation of `a*` reveals the commitment type, so `p t = 1` from period `1` on. -/
example : predictA (1 / 2) (fun _ => 0) 0 = 1 / 2 ∧ predictA (1 / 2) (fun _ => 0) 1 = 1 := by
  simp [predictA, reputationPosterior]

end Econ
