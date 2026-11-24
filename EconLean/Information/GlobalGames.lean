/-
# Global games: uniqueness by iterated dominance (Morris–Shin 2003, §2)

The global-games approach originates with Carlsson and van Damme (1993), who prove a limit
result (vanishing noise, proper prior, general 2×2 games). This file formalizes the
diffuse-prior two-player investment example of Morris and Shin (2003), "Global games: theory
and applications", §2. Two players each decide whether to
**invest**. The fundamental is `θ`. Investing pays `θ` if the other player invests and `θ − 1`
if she does not; not investing pays `0`. With complete information the game has multiple
equilibria for `θ ∈ [0, 1]`.

Each player observes a noisy private signal `x` of `θ`. We take the posterior beliefs as
primitives, as is standard under a diffuse (improper uniform) prior: a player with signal `x`
expects `θ` to be `x`, and believes the other player's signal is distributed as `μ x`, a
probability measure whose distribution function is `t ↦ G ((t − x) / ε)`. Here `ε > 0` is the
noise scale, and `G` is the distribution function of the scaled difference of the two noise
terms: it is nondecreasing, continuous at `0`, and `G 0 = 1/2` (the difference is symmetric
and has no atom at `0`). A strategy is the measurable set `A` of signals at which the player
invests; the expected gain from investing, at signal `x` against the strategy `B`, is
`x − 1 + μ x (B)`.

**Iterated interim strict dominance** (`survives`): `survives μ 0` is the set of all
strategies; a strategy survives round `n + 1` if it survived round `n` and, at every signal,
its action is not strictly dominated against every surviving strategy of the opponent
(investing is strictly dominated at `x` if the gain is negative against all of them, not
investing if the gain is positive against all of them).

Main results:
* `threshold_survives`: the threshold strategy "invest iff `x > 1/2`" survives every round.
* `globalGame_invest`, `globalGame_noInvest`: every signal `x > 1/2` is eventually invested at
  by every surviving strategy, and every `x < 1/2` eventually never.
* `globalGame_unique`: hence the strategies surviving all rounds invest for `x > 1/2` and not
  for `x < 1/2`: the game is dominance solvable, with the **Laplacian threshold** `1/2`, for
  every noise scale `ε > 0` (because the prior is diffuse).

Not formalized: the derivation of these posteriors from a prior and a noise distribution, and
common-prior consistency of the two players' beliefs (not needed here); proper priors and the
vanishing-noise limit (Carlsson–van Damme); general payoffs, many actions, and more than two
players or a continuum of players (Frankel–Morris–Pauzner 2003; Morris–Shin 1998). The field
`cont` and the upper bound `G ≤ 1` in `bdd` are implied by the others but kept for convenience;
the lower bound `0 ≤ G` is needed. The beliefs `μ` about the other's signal are a free primitive:
they are not tied to a posterior over `θ` (whose mean `x` is hard-coded in `investGain`).
`uniformNoise_spec` is a consistency check: uniform beliefs about the other's signal arise from
perfectly anti-correlated noise, not from i.i.d. noise.
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Algebra.Order.Group

@[expose] public section

namespace Econ

open MeasureTheory Set

/-- Expected gain from investing at signal `x` when the other player invests on `B`:
`E[θ | x] − 1 + P(other invests | x)`, with `E[θ | x] = x` (diffuse prior). -/
noncomputable def investGain (μ : ℝ → Measure ℝ) (x : ℝ) (B : Set ℝ) : ℝ :=
  x - 1 + (μ x B).toReal

/-- Strategies surviving `n` rounds of iterated interim strict dominance. -/
def survives (μ : ℝ → Measure ℝ) : ℕ → Set (Set ℝ)
  | 0 => {B | MeasurableSet B}
  | n + 1 => {A | A ∈ survives μ n ∧ ∀ x,
      (x ∈ A → ∃ B ∈ survives μ n, 0 ≤ investGain μ x B) ∧
      (x ∉ A → ∃ B ∈ survives μ n, investGain μ x B ≤ 0)}

lemma survives_measurable {μ : ℝ → Measure ℝ} : ∀ n, ∀ A ∈ survives μ n, MeasurableSet A
  | 0, _, hA => hA
  | n + 1, A, hA => survives_measurable n A hA.1

/-- The standing assumptions on beliefs. -/
structure GlobalBeliefs (μ : ℝ → Measure ℝ) (G : ℝ → ℝ) (ε : ℝ) : Prop where
  prob : ∀ x, IsProbabilityMeasure (μ x)
  eps_pos : 0 < ε
  mono : Monotone G
  cont : ContinuousAt G 0
  half : G 0 = 1 / 2
  bdd : ∀ t, 0 ≤ G t ∧ G t ≤ 1
  Iic : ∀ x t, μ x (Iic t) = ENNReal.ofReal (G ((t - x) / ε))
  Iio : ∀ x t, μ x (Iio t) = ENNReal.ofReal (G ((t - x) / ε))

namespace GlobalBeliefs

variable {μ : ℝ → Measure ℝ} {G : ℝ → ℝ} {ε : ℝ} (hb : GlobalBeliefs μ G ε)
include hb

lemma prob_Ioi (x t : ℝ) : (μ x (Ioi t)).toReal = 1 - G ((t - x) / ε) := by
  have := hb.prob x
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hb.Iic,
    ENNReal.toReal_sub_of_le (by rw [ENNReal.ofReal_le_one]; exact (hb.bdd _).2) ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (hb.bdd _).1, ENNReal.toReal_one]

lemma prob_Ici (x t : ℝ) : (μ x (Ici t)).toReal = 1 - G ((t - x) / ε) := by
  have := hb.prob x
  rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, hb.Iio,
    ENNReal.toReal_sub_of_le (by rw [ENNReal.ofReal_le_one]; exact (hb.bdd _).2) ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (hb.bdd _).1, ENNReal.toReal_one]

lemma toReal_mono' (x : ℝ) {s t : Set ℝ} (h : s ⊆ t) : (μ x s).toReal ≤ (μ x t).toReal := by
  have := hb.prob x
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

lemma toReal_le_one (x : ℝ) (s : Set ℝ) : (μ x s).toReal ≤ 1 := by
  have := hb.prob x
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- If every surviving strategy invests above `U`, then a signal `x` with
`G ((U − x)/ε) < x` is invested at by every strategy surviving one more round. -/
lemma upper_step {n : ℕ} {U x : ℝ} (hU : ∀ B ∈ survives μ n, Ioi U ⊆ B)
    (hx : G ((U - x) / ε) < x) : ∀ A ∈ survives μ (n + 1), x ∈ A := by
  intro A hA
  by_contra hxA
  obtain ⟨B, hB, hg⟩ := (hA.2 x).2 hxA
  have h1 := hb.toReal_mono' x (hU B hB)
  rw [hb.prob_Ioi] at h1
  unfold investGain at hg
  linarith

/-- If no surviving strategy invests below `L`, then a signal `x` with `x < G ((L − x)/ε)` is
invested at by no strategy surviving one more round. -/
lemma lower_step {n : ℕ} {L x : ℝ} (hL : ∀ B ∈ survives μ n, B ⊆ Ici L)
    (hx : x < G ((L - x) / ε)) : ∀ A ∈ survives μ (n + 1), x ∉ A := by
  intro A hA hxA
  obtain ⟨B, hB, hg⟩ := (hA.2 x).1 hxA
  have h1 := hb.toReal_mono' x (hL B hB)
  rw [hb.prob_Ici] at h1
  unfold investGain at hg
  linarith

/-- **The Laplacian threshold strategy survives** every round of iterated dominance. -/
theorem threshold_survives : ∀ n, Ioi (1 / 2 : ℝ) ∈ survives μ n
  | 0 => by show MeasurableSet (Ioi (1 / 2 : ℝ)); exact measurableSet_Ioi
  | n + 1 => by
    refine ⟨threshold_survives n, fun x => ⟨fun hx => ⟨_, threshold_survives n, ?_⟩,
      fun hx => ⟨_, threshold_survives n, ?_⟩⟩⟩
    · -- at `x > 1/2` the other player invests with probability `1 − G((1/2 − x)/ε) ≥ 1/2`
      unfold investGain
      rw [hb.prob_Ioi]
      have : G ((1 / 2 - x) / ε) ≤ G 0 :=
        hb.mono (div_nonpos_of_nonpos_of_nonneg (by simp only [mem_Ioi] at hx; linarith)
          hb.eps_pos.le)
      rw [hb.half] at this
      simp only [mem_Ioi] at hx
      linarith
    · unfold investGain
      rw [hb.prob_Ioi]
      have : G 0 ≤ G ((1 / 2 - x) / ε) :=
        hb.mono (div_nonneg (by simp only [mem_Ioi, not_lt] at hx; linarith) hb.eps_pos.le)
      rw [hb.half] at this
      simp only [mem_Ioi, not_lt] at hx
      linarith

omit hb in
lemma survives_succ_subset (n : ℕ) : survives μ (n + 1) ⊆ survives μ n := fun _ hA => hA.1

/-- **Signals above `1/2` are eventually always invested at.** -/
theorem globalGame_invest {x : ℝ} (hx : 1 / 2 < x) :
    ∃ n, ∀ A ∈ survives μ n, x ∈ A := by
  set T := {U : ℝ | ∃ n, ∀ B ∈ survives μ n, Ioi U ⊆ B}
  -- investing is dominant above `1`
  have h1 : (1 : ℝ) ∈ T := ⟨1, fun B hB y hy => by
    by_contra hyB
    obtain ⟨C, _, hg⟩ := (hB.2 y).2 hyB
    have := ENNReal.toReal_nonneg (a := μ y C)
    unfold investGain at hg
    simp only [mem_Ioi] at hy
    linarith⟩
  -- every element of `T` is at least `1/2`, since the threshold strategy survives
  have hlow : ∀ U ∈ T, 1 / 2 ≤ U := by
    rintro U ⟨n, hn⟩
    by_contra hlt
    push Not at hlt
    have := hn _ (hb.threshold_survives n) (show (U + 1 / 2) / 2 ∈ Ioi U by
      simp only [mem_Ioi]; linarith)
    simp only [mem_Ioi] at this
    linarith
  have hne : T.Nonempty := ⟨1, h1⟩
  have hbdd : BddBelow T := ⟨1 / 2, hlow⟩
  -- `T` is closed upwards
  have hup : ∀ U ∈ T, ∀ V, U ≤ V → V ∈ T := by
    rintro U ⟨n, hn⟩ V hUV
    exact ⟨n, fun B hB => (Ioi_subset_Ioi hUV).trans (hn B hB)⟩
  set U₀ := sInf T
  have hU₀ : U₀ ≤ 1 / 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (1 / 2 + U₀) / 2 := ⟨_, rfl⟩
    have hm : G 0 < m := by rw [hb.half]; linarith
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hb.cont (m - G 0) (by linarith)
    have hε := hb.eps_pos
    obtain ⟨U, hUT, hUlt⟩ := exists_lt_of_csInf_lt hne (show U₀ < U₀ + ε * δ / 2 by
      have := mul_pos hε hδ; linarith)
    obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = max ((m + U₀) / 2) (U₀ - ε * δ / 2) := ⟨_, rfl⟩
    have hy1 : y < U₀ := hydef ▸ max_lt (by linarith) (by have := mul_pos hε hδ; linarith)
    have hy2 : m < y := hydef ▸ lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hy3 : U₀ - ε * δ / 2 ≤ y := hydef ▸ le_max_right _ _
    have hUge : U₀ ≤ U := csInf_le hbdd hUT
    obtain ⟨n, hn⟩ := hUT
    have hstep : ∀ z, y ≤ z → G ((U - z) / ε) < z := by
      intro z hz
      have ht : |(U - y) / ε - 0| < δ := by
        rw [sub_zero, abs_lt]
        constructor
        · have : 0 ≤ (U - y) / ε := div_nonneg (by linarith) hε.le
          linarith
        · rw [div_lt_iff₀ hε]
          nlinarith
      have hG := hδG ht
      rw [Real.dist_eq, abs_lt] at hG
      have hmono : G ((U - z) / ε) ≤ G ((U - y) / ε) :=
        hb.mono (div_le_div_of_nonneg_right (by linarith) hε.le)
      linarith [hG.2]
    have hyT : y ∈ T := ⟨n + 1, fun A hA z hz =>
      hb.upper_step hn (hstep z (le_of_lt (mem_Ioi.1 hz))) A hA⟩
    have := csInf_le hbdd hyT
    linarith
  obtain ⟨U, ⟨n, hn⟩, hUx⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt hU₀ hx)
  exact ⟨n, fun A hA => hn A hA hUx⟩

/-- **Signals below `1/2` are eventually never invested at.** -/
theorem globalGame_noInvest {x : ℝ} (hx : x < 1 / 2) :
    ∃ n, ∀ A ∈ survives μ n, x ∉ A := by
  set T := {L : ℝ | ∃ n, ∀ B ∈ survives μ n, B ⊆ Ici L}
  -- not investing is dominant below `0`
  have h0 : (0 : ℝ) ∈ T := ⟨1, fun B hB y hy => by
    by_contra hlt
    simp only [mem_Ici, not_le] at hlt
    obtain ⟨C, _, hg⟩ := (hB.2 y).1 hy
    have := hb.toReal_le_one y C
    unfold investGain at hg
    linarith⟩
  have hup : ∀ L ∈ T, L ≤ 1 / 2 := by
    rintro L ⟨n, hn⟩
    by_contra hlt
    push Not at hlt
    have := hn _ (hb.threshold_survives n) (show (L + 1 / 2) / 2 ∈ Ioi (1 / 2 : ℝ) by
      simp only [mem_Ioi]; linarith)
    simp only [mem_Ici] at this
    linarith
  have hne : T.Nonempty := ⟨0, h0⟩
  have hbdd : BddAbove T := ⟨1 / 2, hup⟩
  set L₀ := sSup T
  have hL₀ : 1 / 2 ≤ L₀ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (L₀ + 1 / 2) / 2 := ⟨_, rfl⟩
    have hm : m < G 0 := by rw [hb.half]; linarith
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hb.cont (G 0 - m) (by linarith)
    have hε := hb.eps_pos
    obtain ⟨L, hLT, hLgt⟩ := exists_lt_of_lt_csSup hne (show L₀ - ε * δ / 2 < L₀ by
      have := mul_pos hε hδ; linarith)
    obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = min ((m + L₀) / 2) (L₀ + ε * δ / 2) := ⟨_, rfl⟩
    have hy1 : L₀ < y := hydef ▸ lt_min (by linarith) (by have := mul_pos hε hδ; linarith)
    have hy2 : y < m := hydef ▸ lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hy3 : y ≤ L₀ + ε * δ / 2 := hydef ▸ min_le_right _ _
    have hLle : L ≤ L₀ := le_csSup hbdd hLT
    obtain ⟨n, hn⟩ := hLT
    have hstep : ∀ z, z ≤ y → z < G ((L - z) / ε) := by
      intro z hz
      have ht : |(L - y) / ε - 0| < δ := by
        rw [sub_zero, abs_lt]
        constructor
        · rw [lt_div_iff₀ hε]
          nlinarith
        · have : (L - y) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
          linarith
      have hG := hδG ht
      rw [Real.dist_eq, abs_lt] at hG
      have hmono : G ((L - y) / ε) ≤ G ((L - z) / ε) :=
        hb.mono (div_le_div_of_nonneg_right (by linarith) hε.le)
      linarith [hG.1]
    have hyT : y ∈ T := ⟨n + 1, fun A hA z hzA => by
      by_contra hz
      simp only [mem_Ici, not_le] at hz
      exact hb.lower_step hn (hstep z hz.le) A hA hzA⟩
    have := le_csSup hbdd hyT
    linarith
  obtain ⟨L, ⟨n, hn⟩, hLx⟩ := exists_lt_of_lt_csSup hne (lt_of_lt_of_le hx hL₀)
  exact ⟨n, fun A hA hxA => absurd (hn A hA hxA) (by simp only [mem_Ici, not_le]; exact hLx)⟩

/-- **Uniqueness by iterated dominance** (Morris–Shin 2003, §2): a strategy
surviving every round invests at every signal above `1/2` and at no signal below `1/2`, and the
threshold strategy does survive every round. -/
theorem globalGame_unique :
    (∀ n, Ioi (1 / 2 : ℝ) ∈ survives μ n) ∧
      ∀ A, (∀ n, A ∈ survives μ n) → Ioi (1 / 2 : ℝ) ⊆ A ∧ A ⊆ Ici (1 / 2) := by
  refine ⟨hb.threshold_survives, fun A hA => ⟨fun x hx => ?_, fun x hxA => ?_⟩⟩
  · obtain ⟨n, hn⟩ := hb.globalGame_invest hx
    exact hn A (hA n)
  · by_contra hlt
    simp only [mem_Ici, not_le] at hlt
    obtain ⟨n, hn⟩ := hb.globalGame_noInvest hlt
    exact hn A (hA n) hxA

end GlobalBeliefs

/-- Witness beliefs: the other player's signal is uniform on `[x − 1, x + 1]` (a consistency
check; it arises from perfectly anti-correlated noise). -/
noncomputable def uniformBelief (x : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / 2) • volume.restrict (Icc (x - 1) (x + 1))

/-- The corresponding distribution function: uniform on `[−1, 1]`. -/
noncomputable def uniformG (t : ℝ) : ℝ := max 0 (min 1 ((t + 1) / 2))

lemma ofReal_clamp (c : ℝ) : ENNReal.ofReal (min 1 c) = ENNReal.ofReal (max 0 (min 1 c)) := by
  rcases le_total 0 (min 1 c) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

lemma uniformBelief_Iic (x t : ℝ) :
    uniformBelief x (Iic t) = ENNReal.ofReal (uniformG ((t - x) / 1)) := by
  simp only [uniformBelief, FunLike.coe_smul, Pi.smul_apply, Measure.restrict_apply measurableSet_Iic,
    smul_eq_mul, div_one, uniformG]
  have hset : Iic t ∩ Icc (x - 1) (x + 1) = Icc (x - 1) (min (x + 1) t) := by
    ext y; simp only [mem_inter_iff, mem_Icc, mem_Iic, le_min_iff]; tauto
  rw [hset, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num), ← ofReal_clamp]
  congr 1
  rcases le_total (x + 1) t with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]; ring
  · rw [min_eq_right h, min_eq_right (by linarith)]; ring

lemma uniformBelief_Iio (x t : ℝ) :
    uniformBelief x (Iio t) = ENNReal.ofReal (uniformG ((t - x) / 1)) := by
  rw [← uniformBelief_Iic]
  simp only [uniformBelief, FunLike.coe_smul, Pi.smul_apply, Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iio]
  congr 1
  refine le_antisymm (measure_mono (inter_subset_inter_left _ Iio_subset_Iic_self)) ?_
  calc volume (Iic t ∩ Icc (x - 1) (x + 1)) ≤ volume (Iio t ∩ Icc (x - 1) (x + 1) ∪ {t}) := by
        refine measure_mono fun y hy => ?_
        rcases eq_or_lt_of_le (mem_Iic.1 hy.1) with h | h
        · exact Or.inr h
        · exact Or.inl ⟨h, hy.2⟩
    _ ≤ volume (Iio t ∩ Icc (x - 1) (x + 1)) + volume ({t} : Set ℝ) := measure_union_le _ _
    _ = volume (Iio t ∩ Icc (x - 1) (x + 1)) := by rw [Real.volume_singleton, add_zero]

/-- **The hypotheses are consistent**: uniform beliefs satisfy `GlobalBeliefs` with `ε = 1`. -/
theorem uniformNoise_spec : GlobalBeliefs uniformBelief uniformG 1 where
  prob x := ⟨by
    simp only [uniformBelief, FunLike.coe_smul, Pi.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num⟩
  eps_pos := one_pos
  mono a b hab := max_le_max le_rfl (min_le_min le_rfl (by linarith))
  cont := by unfold uniformG; fun_prop
  half := by norm_num [uniformG]
  bdd t := ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  Iic := uniformBelief_Iic
  Iio := uniformBelief_Iio

/-- With uniform beliefs, iterated dominance selects the threshold `1/2`. -/
example : ∀ A, (∀ n, A ∈ survives uniformBelief n) → Ioi (1 / 2 : ℝ) ⊆ A ∧ A ⊆ Ici (1 / 2) :=
  uniformNoise_spec.globalGame_unique.2

end Econ
