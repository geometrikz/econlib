/-
# First- and second-order stochastic dominance

MWG §6.D (Defs. 6.D.1–6.D.2, Props. 6.D.1–6.D.2), for simple money
lotteries.

**First-order stochastic dominance.** `F` FOSD `G` if every decision maker
with nondecreasing `u` weakly prefers `F`: `E_G[u] ≤ E_F[u]`.
**Prop. 6.D.1**: `F` FOSD `G` ⟺ `F(t) ≤ G(t)` for every `t` (the CDF of
`F` lies everywhere below that of `G`).

**Second-order stochastic dominance.** For `F, G` with the same mean, `F`
SOSD `G` if every risk averter (nondecreasing concave `u`) weakly prefers
`F`. **Prop. 6.D.2** relates this to *mean-preserving spreads*: if `G` is
obtained from `F` by replacing each outcome `x` with a lottery of mean `x`,
then `F` SOSD `G`; and SOSD implies the integrated-CDF condition
`∫_{-∞}^t G ≥ ∫_{-∞}^t F` for all `t`.

**Proof of 6.D.1 (⟸).** MWG integrate by parts. For finite supports we
instead induct on the number of distinct values `u` takes on the joint
support: peel off the top value with a step function `1[x ≥ m]` and use
`P_F(X ≥ m) ≥ P_G(X ≥ m)`, which follows from the CDF condition.
-/
module

public import EconLean.Uncertainty.RiskAversion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace Econ

open Set Finset SimpleLottery

namespace SimpleLottery

/-- **First-order stochastic dominance** (MWG Def. 6.D.1). -/
def FOSD (F G : SimpleLottery) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → G.expect u ≤ F.expect u

/-- `P(X > t) = 1 - F(t)`. -/
theorem expect_gt (F : SimpleLottery) (t : ℝ) :
    F.expect (fun x => if t < x then 1 else 0) = 1 - F.cdf t := by
  have h : (fun x : ℝ => if t < x then (1 : ℝ) else 0) =
      fun x => (1 : ℝ) - (if x ≤ t then (1 : ℝ) else 0) := by
    funext x
    split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | norm_num
  rw [h, F.expect_sub (fun _ => 1), expect_const, cdf]

/-- Under the CDF condition, `P_G(X ≥ m) ≤ P_F(X ≥ m)` (strict-inequality
event at the left of `m` needs care: we approximate `{x < m}` from the
finite joint support). -/
theorem expect_ge_le_of_cdf {F G : SimpleLottery} (h : ∀ t, F.cdf t ≤ G.cdf t) (m : ℝ) :
    G.expect (fun x => if m ≤ x then 1 else 0) ≤ F.expect (fun x => if m ≤ x then 1 else 0) := by
  classical
  set S := F.prob.support ∪ G.prob.support
  have hF : F.prob.support ⊆ S := subset_union_left
  have hG : G.prob.support ⊆ S := subset_union_right
  -- Write `1[m ≤ x] = 1 - 1[x < m]`.
  have hsplit : ∀ H : SimpleLottery, H.expect (fun x => if m ≤ x then 1 else 0) =
      1 - H.expect (fun x => if x < m then 1 else 0) := fun H => by
    have h : (fun x : ℝ => if m ≤ x then (1 : ℝ) else 0) =
        fun x => (1 : ℝ) - (if x < m then (1 : ℝ) else 0) := by
      funext x
      split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | norm_num
    rw [h, H.expect_sub (fun _ => 1), expect_const]
  rw [hsplit, hsplit]
  suffices F.expect (fun x => if x < m then 1 else 0) ≤
      G.expect (fun x => if x < m then 1 else 0) by linarith
  set T := S.filter (· < m)
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- No support point lies below `m`.
    have : F.expect (fun x => if x < m then 1 else 0) = F.expect (fun _ => 0) :=
      F.expect_congr hF fun x hx => by
        have : x ∉ T := by rw [hT]; exact Finset.notMem_empty x
        simp only [T, Finset.mem_filter, not_and] at this
        simp [this hx]
    rw [this, expect_const]
    exact G.expect_nonneg fun x _ => by split_ifs <;> norm_num
  · -- On the support, `x < m ↔ x ≤ b` where `b` is the largest support point below `m`.
    set b := T.max' hT
    have hb : b < m := (Finset.mem_filter.1 (T.max'_mem hT)).2
    have hiff : ∀ x ∈ S, (x < m ↔ x ≤ b) := fun x hx =>
      ⟨fun hxm => T.le_max' x (Finset.mem_filter.2 ⟨hx, hxm⟩), fun hxb => hxb.trans_lt hb⟩
    have eF : F.expect (fun x => if x < m then 1 else 0) = F.cdf b :=
      F.expect_congr hF fun x hx => by simp only [hiff x hx]
    have eG : G.expect (fun x => if x < m then 1 else 0) = G.cdf b :=
      G.expect_congr hG fun x hx => by simp only [hiff x hx]
    rw [eF, eG]
    exact h b

/-- **FOSD ⟺ CDF dominance** (MWG Prop. 6.D.1). -/
theorem fosd_iff_cdf_le (F G : SimpleLottery) : FOSD F G ↔ ∀ t, F.cdf t ≤ G.cdf t := by
  classical
  constructor
  · -- Test with the nondecreasing step `1[x > t]`.
    intro h t
    have := h (fun x => if t < x then 1 else 0) fun x y hxy => by
      dsimp only
      split_ifs with h1 h2 <;> first | exact absurd (h1.trans_le hxy) h2 | norm_num
    rw [expect_gt, expect_gt] at this
    linarith
  · intro h
    set S := F.prob.support ∪ G.prob.support
    have hF : F.prob.support ⊆ S := subset_union_left
    have hG : G.prob.support ⊆ S := subset_union_right
    have hSne : S.Nonempty := F.support_nonempty.mono hF
    -- Induction on the number of values `u` takes on `S`.
    suffices key : ∀ n : ℕ, ∀ u : ℝ → ℝ, Monotone u → (S.image u).card ≤ n →
        G.expect u ≤ F.expect u from fun u hu => key _ u hu le_rfl
    intro n
    induction n with
    | zero =>
      intro u _ hcard
      exact absurd (Finset.card_pos.2 (hSne.image u)) (by omega)
    | succ n ih =>
      intro u hu hcard
      rcases le_or_gt (S.image u).card 1 with h1 | h1
      · -- `u` is constant on `S`.
        obtain ⟨x₀, hx₀⟩ := hSne
        have hconst : ∀ x ∈ S, u x = u x₀ := fun x hx =>
          Finset.card_le_one.1 h1 _ (Finset.mem_image_of_mem u hx) _
            (Finset.mem_image_of_mem u hx₀)
        rw [G.expect_congr hG hconst, F.expect_congr hF hconst, expect_const, expect_const]
      · -- Peel off the top value `M` of `u` on `S`.
        set V := S.image u
        have hV : V.Nonempty := hSne.image u
        set M := V.max' hV
        have hV' : (V.erase M).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem (V.max'_mem hV)]; omega
        set M' := (V.erase M).max' hV'
        have hM'mem : M' ∈ V.erase M := (V.erase M).max'_mem hV'
        have hM'lt : M' < M :=
          lt_of_le_of_ne (V.le_max' _ (Finset.mem_of_mem_erase hM'mem))
            (Finset.ne_of_mem_erase hM'mem)
        -- The truncated utility takes one value fewer.
        set u' : ℝ → ℝ := fun x => min (u x) M'
        have hu' : Monotone u' := fun x y hxy => min_le_min_right _ (hu hxy)
        have hsub : S.image u' ⊆ V.erase M := by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
          have hxV : u x ∈ V := Finset.mem_image_of_mem u hx
          by_cases hxM : u x = M
          · simp only [u', hxM, min_eq_right hM'lt.le]; exact hM'mem
          · have : u x ∈ V.erase M := Finset.mem_erase.2 ⟨hxM, hxV⟩
            have hle : u x ≤ M' := (V.erase M).le_max' _ this
            show min (u x) M' ∈ V.erase M
            rw [min_eq_left hle]; exact this
        have hcard' : (S.image u').card ≤ n := by
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem (V.max'_mem hV)] at this
          omega
        -- The threshold where `u` reaches `M`.
        have hTne : (S.filter fun x => M ≤ u x).Nonempty := by
          obtain ⟨x, hx, hxM⟩ := Finset.mem_image.1 (V.max'_mem hV)
          exact ⟨x, Finset.mem_filter.2 ⟨hx, hxM.ge⟩⟩
        set m := (S.filter fun x => M ≤ u x).min' hTne
        have hmM : M ≤ u m := (Finset.mem_filter.1 ((S.filter _).min'_mem hTne)).2
        have hdecomp : ∀ x ∈ S, u x = u' x + (M - M') * (if m ≤ x then 1 else 0) := by
          intro x hx
          have hxle : u x ≤ M := V.le_max' _ (Finset.mem_image_of_mem u hx)
          by_cases hxM : M ≤ u x
          · have hmx : m ≤ x := (S.filter _).min'_le x (Finset.mem_filter.2 ⟨hx, hxM⟩)
            have hmin : min (u x) M' = M' := min_eq_right (hM'lt.le.trans hxM)
            show u x = min (u x) M' + (M - M') * (if m ≤ x then 1 else 0)
            rw [hmin]; simp only [hmx, ↓reduceIte]
            linarith
          · have hmx : ¬ m ≤ x := fun hmx => hxM (hmM.trans (hu hmx))
            have hxV : u x ∈ V.erase M :=
              Finset.mem_erase.2 ⟨fun h => hxM h.ge, Finset.mem_image_of_mem u hx⟩
            have hle : u x ≤ M' := (V.erase M).le_max' _ hxV
            show u x = min (u x) M' + (M - M') * (if m ≤ x then 1 else 0)
            rw [min_eq_left hle]; simp only [hmx, ↓reduceIte]; ring
        have eF := F.expect_congr hF hdecomp
        have eG := G.expect_congr hG hdecomp
        rw [expect_add, expect_const_mul] at eF eG
        rw [eF, eG]
        have := expect_ge_le_of_cdf h m
        have hIH := ih u' hu' hcard'
        nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.2 hM'lt.le)]

/-! ### Second-order stochastic dominance -/

/-- **Second-order stochastic dominance** (MWG Def. 6.D.2): same mean, and
every nondecreasing concave `u` weakly prefers `F`. -/
def SOSD (F G : SimpleLottery) : Prop :=
  F.mean = G.mean ∧ ∀ u : ℝ → ℝ, Monotone u → ConcaveOn ℝ univ u → G.expect u ≤ F.expect u

/-- `G` is a **mean-preserving spread** of `F` (MWG §6.D): `G` is
generated by drawing `x` from `F` and then replacing `x` with an
independent lottery `H x` whose mean is `x`. -/
def IsMeanPreservingSpread (G F : SimpleLottery) : Prop :=
  ∃ H : ℝ → SimpleLottery, (∀ x ∈ F.prob.support, (H x).mean = x) ∧
    G.prob = ∑ x ∈ F.prob.support, F.prob x • (H x).prob

/-- Expectations under a compound lottery: `E_G[u] = ∑ₓ F(x) E_{H x}[u]`. -/
theorem expect_of_compound {G F : SimpleLottery} {H : ℝ → SimpleLottery}
    (hG : G.prob = ∑ x ∈ F.prob.support, F.prob x • (H x).prob) (u : ℝ → ℝ) :
    G.expect u = ∑ x ∈ F.prob.support, F.prob x * (H x).expect u := by
  rw [expect_eq_integral, hG, integral_finset_sum]
  exact Finset.sum_congr rfl fun x _ => integral_smul _ _ _

/-- A mean-preserving spread lowers expected utility for **every** concave
`u` (not necessarily monotone). -/
theorem expect_le_of_meanPreservingSpread {G F : SimpleLottery}
    (h : IsMeanPreservingSpread G F) {u : ℝ → ℝ} (hu : ConcaveOn ℝ univ u) :
    G.expect u ≤ F.expect u := by
  obtain ⟨H, hmean, hG⟩ := h
  rw [expect_of_compound hG, expect_eq_sum]
  refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ (F.nonneg x)
  have := ConcaveOn.expect_le hu (H x) (subset_univ _)
  rwa [hmean x hx] at this

/-- **Mean-preserving spreads are second-order dominated** (MWG Prop.
6.D.2, (ii) ⟹ (i)): if `G` is a mean-preserving spread of `F`, then `F`
and `G` have the same mean and `F` SOSD `G`. -/
theorem sosd_of_meanPreservingSpread {G F : SimpleLottery}
    (h : IsMeanPreservingSpread G F) : SOSD F G := by
  refine ⟨?_, fun u _ hu => expect_le_of_meanPreservingSpread h hu⟩
  obtain ⟨H, hmean, hG⟩ := h
  rw [mean, mean, expect_of_compound hG, expect_eq_sum]
  exact Finset.sum_congr rfl fun x hx => by rw [← mean, hmean x hx, id]

/-- **SOSD implies the integrated-CDF condition** (MWG Prop. 6.D.2,
(i) ⟹ (iii)), in its expected-shortfall form
`E_F[(t - X)⁺] ≤ E_G[(t - X)⁺]` for every `t`. See
`expect_shortfall_eq_integral_cdf` for `E_F[(t - X)⁺] = ∫_{-∞}^t F`. -/
theorem SOSD.shortfall_le {F G : SimpleLottery} (h : SOSD F G) (t : ℝ) :
    F.expect (fun x => max (t - x) 0) ≤ G.expect (fun x => max (t - x) 0) := by
  -- Test with the nondecreasing concave `u(x) = -(t - x)⁺ = min (x - t) 0`.
  have hmono : Monotone fun x : ℝ => -max (t - x) 0 := fun x y hxy => by
    simp only [neg_le_neg_iff]; exact max_le_max (by linarith) le_rfl
  have hconv : ConvexOn ℝ univ fun x : ℝ => max (t - x) 0 :=
    ⟨convex_univ, fun x _ y _ a b ha hb hab => by
      simp only [smul_eq_mul]
      have h1 := le_max_left (t - x) 0
      have h2 := le_max_right (t - x) 0
      have h3 := le_max_left (t - y) 0
      have h4 := le_max_right (t - y) 0
      refine max_le ?_ (by positivity)
      have ht : t = a * t + b * t := by rw [← add_mul, hab, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb]⟩
  have hconc : ConcaveOn ℝ univ fun x : ℝ => -max (t - x) 0 := hconv.neg
  have := h.2 _ hmono hconc
  rw [show (fun x => -max (t - x) 0) = fun x => (-1) * max (t - x) 0 from
    funext fun x => by ring, expect_const_mul, expect_const_mul] at this
  linarith

/-- The step `s ↦ 1[x ≤ s]` is nondecreasing. -/
theorem monotone_step (x : ℝ) : Monotone fun s : ℝ => if x ≤ s then (1 : ℝ) else 0 :=
  fun s s' hss' => by
    dsimp only
    split_ifs with h1 h2 <;> first | exact absurd (h1.trans hss') h2 | norm_num

/-- **Expected shortfall is the integrated CDF.** If `a` lies strictly below
every outcome and `a ≤ t`, then `E_F[(t - X)⁺] = ∫ₐᵗ F(s) ds`. Since
`F = 0` below `a`, the right side is `∫_{-∞}^t F`, so `SOSD.shortfall_le` is
exactly MWG's condition `∫_{-∞}^t F ≤ ∫_{-∞}^t G`. -/
theorem expect_shortfall_eq_integral_cdf (F : SimpleLottery) {a t : ℝ}
    (ha : ∀ x ∈ F.prob.support, a < x) (hat : a ≤ t) :
    F.expect (fun x => max (t - x) 0) = ∫ s in a..t, F.cdf s := by
  -- Each atom `x` contributes `F(x) · ∫ₐᵗ 1[x ≤ s] ds = F(x) · (t - x)⁺`.
  have hstep : ∀ x, a < x → ∫ s in a..t, (if x ≤ s then (1 : ℝ) else 0) = max (t - x) 0 := by
    intro x hax
    have hfun : (fun s : ℝ => if x ≤ s then (1 : ℝ) else 0) = (Ici x).indicator 1 := by
      funext s; simp [Set.indicator, Set.mem_Ici]
    rw [intervalIntegral.integral_of_le hat, hfun,
      MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hset : Ioc a t ∩ Ici x = Icc x t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hax.trans_le h1, h2⟩, h1⟩
    rw [hset]
    simp [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']
  unfold cdf
  simp only [expect_eq_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [intervalIntegral.integral_const_mul, hstep x (ha x hx)]
  · intro x _
    exact Monotone.intervalIntegrable fun s s' hss' =>
      mul_le_mul_of_nonneg_left (monotone_step x hss') (F.nonneg x)

/-- **Witness for mean-preserving spreads.** The fair coin flip `±1` is a
mean-preserving spread of the sure amount `0`, so `δ₀` second-order
dominates it. -/
example : IsMeanPreservingSpread (twoPoint (-1) 1 (1 / 2) (by norm_num) (by norm_num)) (pure 0) ∧
    SOSD (pure 0) (twoPoint (-1) 1 (1 / 2) (by norm_num) (by norm_num)) := by
  have hmps : IsMeanPreservingSpread (twoPoint (-1) 1 (1 / 2) (by norm_num) (by norm_num))
      (pure 0) := by
    refine ⟨fun _ => twoPoint (-1) 1 (1 / 2) (by norm_num) (by norm_num), fun x hx => ?_, ?_⟩
    · have hx0 : x = 0 := by
        simpa [pure] using Finsupp.support_single_subset hx
      rw [hx0, mean, expect_twoPoint]; norm_num
    · have hs : (pure 0).prob.support = {0} := Finsupp.support_single 0 one_ne_zero
      rw [hs, Finset.sum_singleton]
      simp [pure]
  exact ⟨hmps, sosd_of_meanPreservingSpread hmps⟩

end SimpleLottery

end Econ
