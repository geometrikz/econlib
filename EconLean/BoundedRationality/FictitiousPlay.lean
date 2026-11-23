/-
# Fictitious play

References. G. W. Brown (1951), "Iterative Solution of Games by Fictitious
Play"; J. Robinson (1951), "An Iterative Method of Solving a Game", *Annals of
Math.* 54; D. Fudenberg and D. K. Levine (1998), *The Theory of Learning in
Games*, ch. 2 (the proposition that limits of empirical frequencies are
Nash equilibria).

In a finite normal-form game, a **fictitious-play path** is a sequence of pure
profiles `h 0, h 1, …` in which, at every date `T ≥ 1`, each player best
responds to the empirical frequencies of the others' past play
(`freq h T`, `IsFP`). This is Brown's version without prior weights (date `0`
is free); beliefs are the product of the others' marginal frequencies
(independent beliefs), the standard reading with two players.

**Results.**
* `isMixedNash_of_tendsto` (Fudenberg–Levine ch. 2): if the empirical
  frequencies converge, the limit is a mixed Nash equilibrium. An action that
  does strictly worse than another against the limit is eventually never
  played, so its frequency vanishes (`freq_eq_zero_of_worse_at_limit`).
* `isFP_const`, `tendsto_freq_const`: if `s` is a pure Nash equilibrium,
  always playing `s` is a fictitious-play path, whose frequencies converge to
  `s` (non-vacuity).

Convergence of the frequencies themselves (Robinson's theorem for zero-sum
games, Miyasawa's for 2×2 games) is not formalized.
-/
module

public import EconLean.Games.Mixed
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

@[expose] public section

noncomputable section

namespace Econ

namespace FictitiousPlay

open Function Finset Filter Topology

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Empirical frequency of `i`'s action `a` in periods `0, …, T−1`. -/
def freq (h : ℕ → ∀ j, S j) (T : ℕ) : ∀ i, S i → ℝ :=
  fun i a => (((range T).filter fun k => h k i = a).card : ℝ) / T

/-- A fictitious-play path: from date `1` on, every player's action is a best
reply to the empirical frequencies of the others' past play. -/
def IsFP (u : I → (∀ j, S j) → ℝ) (h : ℕ → ∀ j, S j) : Prop :=
  ∀ T, 0 < T → ∀ i (a : S i), pureDev u (freq h T) i a ≤ pureDev u (freq h T) i (h T i)

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] in
theorem freq_nonneg (h : ℕ → ∀ j, S j) (T : ℕ) (i : I) (a : S i) : 0 ≤ freq h T i a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype I] [DecidableEq I] in
theorem sum_freq (h : ℕ → ∀ j, S j) {T : ℕ} (hT : 0 < T) (i : I) :
    ∑ a, freq h T i a = 1 := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [freq, ← sum_div]
  rw [div_eq_one_iff_eq hT']
  have := card_eq_sum_card_fiberwise (f := fun k => h k i) (s := range T) (t := univ)
    (fun _ _ => mem_univ _)
  rw [card_range] at this
  exact_mod_cast this.symm

omit [Fintype I] [DecidableEq I] in
theorem freq_isMixedProfile (h : ℕ → ∀ j, S j) {T : ℕ} (hT : 0 < T) :
    IsMixedProfile (freq h T) :=
  fun i => ⟨freq_nonneg h T i, sum_freq h hT i⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] in
/-- An action not played from date `T₀` on has frequency at most `T₀/T`. -/
theorem freq_le {h : ℕ → ∀ j, S j} {i : I} {b : S i} {T0 : ℕ} (hb : ∀ T, T0 ≤ T → h T i ≠ b)
    (T : ℕ) : freq h T i b ≤ T0 / T := by
  unfold freq
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  apply div_le_div_of_nonneg_right _ hT'.le
  have : (range T).filter (fun k => h k i = b) ⊆ range T0 := by
    intro k hk
    rw [mem_filter, mem_range] at hk
    rw [mem_range]
    by_contra hge
    exact hb k (not_lt.1 hge) hk.2
  exact_mod_cast (card_le_card this).trans (card_range T0).le

/-- **Actions worse at the limit vanish**: if, against the limit of the empirical
frequencies, `b` does strictly worse for `i` than some `t`, then the limit
frequency of `b` is zero. -/
theorem freq_eq_zero_of_worse_at_limit {u : I → (∀ j, S j) → ℝ} {h : ℕ → ∀ j, S j}
    (hfp : IsFP u h) {σ : ∀ i, S i → ℝ} (hσ : Tendsto (freq h) atTop (𝓝 σ)) {i : I}
    {b t : S i} (hbt : pureDev u σ i b < pureDev u σ i t) : σ i b = 0 := by
  -- eventually `b` is not a best reply, so it is not played
  have hc := ((continuous_pureDev u i t).sub (continuous_pureDev u i b)).tendsto σ
  have hev : ∀ᶠ T in atTop, 0 < pureDev u (freq h T) i t - pureDev u (freq h T) i b :=
    (hc.comp hσ).eventually (lt_mem_nhds (sub_pos.2 hbt))
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  have hnot : ∀ T, T0 ≤ T → h T i ≠ b := fun T hT hb => by
    have h1 := hfp T (hT0 T hT).2 i t
    rw [hb] at h1
    linarith [(hT0 T hT).1]
  have hlim : Tendsto (fun T : ℕ => freq h T i b) atTop (𝓝 (σ i b)) :=
    ((continuous_apply b).tendsto _).comp (((continuous_apply i).tendsto _).comp hσ)
  have hzero : Tendsto (fun T : ℕ => (T0 : ℝ) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine le_antisymm (le_of_tendsto_of_tendsto hlim hzero (Eventually.of_forall
    fun T => freq_le hnot T)) (ge_of_tendsto hlim (Eventually.of_forall
      fun T => freq_nonneg h T i b))

/-- **Limits of fictitious play are Nash equilibria** (Fudenberg–Levine,
ch. 2). -/
theorem isMixedNash_of_tendsto {u : I → (∀ j, S j) → ℝ} {h : ℕ → ∀ j, S j} (hfp : IsFP u h)
    {σ : ∀ i, S i → ℝ} (hσ : Tendsto (freq h) atTop (𝓝 σ)) : IsMixedNash u σ := by
  have hcoord : ∀ i a, Tendsto (fun T => freq h T i a) atTop (𝓝 (σ i a)) := fun i a =>
    ((continuous_apply a).tendsto _).comp (((continuous_apply i).tendsto _).comp hσ)
  have hmix : IsMixedProfile σ := fun i => by
    refine ⟨fun a => ge_of_tendsto (hcoord i a) (Eventually.of_forall
      fun T => freq_nonneg h T i a), ?_⟩
    have hs : Tendsto (fun T => ∑ a, freq h T i a) atTop (𝓝 (∑ a, σ i a)) :=
      tendsto_finsetSum _ fun a _ => hcoord i a
    exact tendsto_nhds_unique hs (tendsto_const_nhds.congr'
      ((eventually_gt_atTop 0).mono fun T hT => (sum_freq h hT i).symm))
  rw [isMixedNash_iff_pure hmix]
  intro i t
  rw [mixedPayoff_eq_sum_pureDev]
  calc pureDev u σ i t = ∑ b, σ i b * pureDev u σ i t := by
        rw [← sum_mul, (hmix i).2, one_mul]
    _ ≤ ∑ b, σ i b * pureDev u σ i b := sum_le_sum fun b _ => by
        by_cases hb : pureDev u σ i b < pureDev u σ i t
        · rw [freq_eq_zero_of_worse_at_limit hfp hσ hb]; simp
        · exact mul_le_mul_of_nonneg_left (not_lt.1 hb) ((hmix i).1 b)

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] in
theorem freq_const (s : ∀ j, S j) {T : ℕ} (hT : 0 < T) :
    freq (fun _ => s) T = pureProfile s := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  funext i a
  simp only [freq, pureProfile, degenerate]
  by_cases h : s i = a
  · simp [h, hT']
  · simp [h]

/-- Non-vacuity: always playing a pure Nash equilibrium is a fictitious-play
path. -/
theorem isFP_const {u : I → (∀ j, S j) → ℝ} {s : ∀ j, S j} (hs : IsNash u s) :
    IsFP u fun _ => s := by
  intro T hT i a
  rw [freq_const s hT]
  show pureDev u (pureProfile s) i a ≤ pureDev u (pureProfile s) i (s i)
  simp only [pureDev, update_pureProfile, mixedPayoff_pureProfile, update_eq_self]
  exact hs i a

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] in
theorem tendsto_freq_const (s : ∀ j, S j) :
    Tendsto (freq fun _ => s) atTop (𝓝 (pureProfile s)) :=
  tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun _ hT => (freq_const s hT).symm)

end FictitiousPlay

end Econ
