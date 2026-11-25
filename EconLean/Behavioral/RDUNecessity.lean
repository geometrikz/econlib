/-
# Chew–Karni–Safra: strong risk aversion forces concave utility and convex weighting

References. S. Chew, E. Karni and Z. Safra (1987), "Risk Aversion in the
Theory of Expected Utility with Rank Dependent Probabilities", *JET* 42(2),
Theorem 2; J. Quiggin (1993), *Generalized Expected Utility Theory*, ch. 6.

Builds on `RDUStrongRiskAversion.lean` (mean-preserving spreads, Yaari) and
`RDUConcaveConvex.lean` (CKS sufficiency). The RDU value of a lottery `p` on
the outcome grid `x` with utility of money `U : ℝ → ℝ` is
`rdu w (fun k => U (x k)) p`.

**Results.**
* `StronglyRiskAverse w U`: the agent weakly dislikes every mean-preserving
  spread (`IsMPS`) on every weakly increasing outcome grid. (`rdu` ranks
  outcomes by grid index, so this is RDU proper only for increasing `U`, as in
  `cks_iff`; the two necessity results hold as stated for any `U`.)
* `isMPS_affine`: mean-preserving spreads survive positive affine rescaling of
  the grid.
* `convex_of_stronglyRiskAverse` (**CKS necessity, weighting**): if `U` is
  differentiable at some `x₀` with `U'(x₀) > 0`, strong risk aversion forces
  `w` convex on `[0, 1]`. Proof: the three-point spreads behind Yaari's
  converse, on the grid `x₀, x₀ + l h, x₀ + h`, with `h → 0⁺`.
* `concave_of_stronglyRiskAverse` (**CKS necessity, utility**): if `w` is
  differentiable at some `s ∈ (0, 1)` with `w'(s) > 0`, strong risk aversion
  forces `U` concave on `ℝ`. Proof: on the grid `a, m, b, b + 1` with
  `m = (1 − λ) a + λ b`, spread a mass `δ` sitting at `m` (with mass `s` above
  it) onto `a` and `b`; the decision weights of the two new outcomes are
  `w(s + δλ) − w(s)` and `w(s + δ) − w(s + δλ)`, which in the limit `δ → 0⁺`
  are in the ratio `λ : 1 − λ`, giving `U m ≥ (1 − λ) U a + λ U b`.
  (`baseLot`, `spreadLot`, `isMPS_spread` are the lotteries used.)
* `cks_iff` (**Chew–Karni–Safra 1987**): for `U` increasing, and
  differentiable with positive derivative at some point, and `w` increasing on
  `[0, 1]` and differentiable with positive derivative at some interior point,
  the agent is strongly risk averse iff `U` is concave and `w` is convex.
  CKS weight the cumulative distribution, `g(F)`, and state the condition as
  `g` concave; with `w(t) = 1 − g(1 − t)` this is the same as `w` convex.
* Non-vacuity: `sq_id_stronglyRiskAverse` (`w t = t²`, linear `U`),
  `exp_not_stronglyRiskAverse` (`w t = t²`, `U = exp`: fails the utility half),
  `concaveW_not_stronglyRiskAverse` (`w t = 2t − t²`, linear `U`: fails the
  weighting half).

**Scope.** The regularity conditions (one point of positive derivative for each
of `U` and `w`) are those of the limit argument, not CKS's own (they assume
differentiability throughout); they exclude e.g. singular weighting functions.
`U` is defined on all of `ℝ` here.
-/
module

public import EconLean.Behavioral.RDUConcaveConvex
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

namespace Econ

namespace RankDependent

open Finset Filter Topology

/-- The agent **weakly dislikes every mean-preserving spread** on every weakly
increasing outcome grid (economically meaningful for increasing `U`; see
`cks_iff`). -/
def StronglyRiskAverse (w U : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : ℕ → ℝ), MonotoneOnGrid n x → ∀ p q : Lottery n, IsMPS x q p →
    rdu w (fun k => U (x k)) q ≤ rdu w (fun k => U (x k)) p

/-- Difference quotients along a ray `x₀ + h c`, `h → 0⁺`. -/
theorem tendsto_slope_ray {U : ℝ → ℝ} {d x₀ : ℝ} (hd : HasDerivAt U d x₀) (c : ℝ) :
    Tendsto (fun h => h⁻¹ * (U (x₀ + h * c) - U x₀)) (𝓝[>] 0) (𝓝 (c * d)) := by
  have hd0 : HasDerivAt U d (x₀ + 0 * c) := by simpa using hd
  have hin : HasDerivAt (fun h : ℝ => x₀ + h * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add x₀
  have hcomp := HasDerivAt.comp (0 : ℝ) hd0 hin
  have hsub : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ := fun h hh =>
    Set.mem_compl_singleton_iff.2 (ne_of_gt (Set.mem_Ioi.1 hh))
  have := (hasDerivAt_iff_tendsto_slope_zero.1 hcomp).mono_left (nhdsWithin_mono _ hsub)
  simpa [Function.comp, mul_comm] using this

variable {n : ℕ}

/-- Mean-preserving spreads survive positive affine rescaling of the grid. -/
theorem isMPS_affine {y : ℕ → ℝ} {p q : Lottery n} (h : IsMPS y q p) (c : ℝ) {a : ℝ}
    (ha : 0 ≤ a) : IsMPS (fun k => c + a * y k) q p := by
  have hsum : ∀ r : Lottery n, ∑ k ∈ range n, G r (k + 1) * (c + a * y (k + 1) - (c + a * y k)) =
      a * ∑ k ∈ range n, G r (k + 1) * (y (k + 1) - y k) := fun r => by
    rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  have h1 := h.1
  rw [eu_eq_layer, eu_eq_layer, add_right_inj] at h1
  refine ⟨?_, fun m hm => ?_⟩
  · rw [eu_eq_layer, eu_eq_layer, hsum, hsum, h1]
  · have := mul_le_mul_of_nonneg_left (h.2 m hm) ha
    rw [mul_sum, mul_sum] at this
    convert this using 1 <;> exact sum_congr rfl fun k _ => by ring

/-- **Chew–Karni–Safra, necessity of convex weighting.** -/
theorem convex_of_stronglyRiskAverse {w U : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hS : StronglyRiskAverse w U) {x₀ d : ℝ} (hd : HasDerivAt U d x₀) (hdpos : 0 < d) :
    ConvexOn ℝ (Set.Icc 0 1) w := by
  have key : ∀ t s l : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → 0 ≤ l → l ≤ 1 →
      w (l * t + (1 - l) * s) ≤ l * w t + (1 - l) * w s := by
    intro t s l hs hst ht hl0 hl1
    have hr0 : 0 ≤ l * t + (1 - l) * s := by nlinarith
    have hr1 : l * t + (1 - l) * s ≤ 1 := by nlinarith
    set r := l * t + (1 - l) * s
    set y : ℕ → ℝ := fun k => if k = 0 then 0 else if k = 1 then l else 1
    have hineq : ∀ h : ℝ, 0 < h →
        w r * (h⁻¹ * (U (x₀ + h * 1) - U x₀)) ≤ w t * (h⁻¹ * (U (x₀ + h * l) - U x₀)) +
          w s * (h⁻¹ * (U (x₀ + h * 1) - U x₀) - h⁻¹ * (U (x₀ + h * l) - U x₀)) := by
      intro h hh
      have hmono : MonotoneOnGrid 2 fun k => x₀ + h * y k := fun k hk => by
        interval_cases k <;> simp [y] <;> nlinarith
      have := hS 2 _ hmono _ _ (isMPS_affine (isMPS_tri hs hst ht hl0 hl1 hr0 hr1) x₀ hh.le)
      rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1] at this
      simp only [sum_range_succ, sum_range_zero, y] at this
      rw [G_triLot_one, G_triLot_two, G_triLot_one, G_triLot_two] at this
      norm_num at this
      have hh' : 0 ≤ h⁻¹ := inv_nonneg.2 hh.le
      simp only [mul_one]
      have e1 : w r * (h⁻¹ * (U (x₀ + h) - U x₀)) = h⁻¹ * (w r * (U (x₀ + h * l) - U x₀) +
          w r * (U (x₀ + h) - U (x₀ + h * l))) := by ring
      have e2 : w t * (h⁻¹ * (U (x₀ + h * l) - U x₀)) + w s * (h⁻¹ * (U (x₀ + h) - U x₀) -
          h⁻¹ * (U (x₀ + h * l) - U x₀)) = h⁻¹ * (w t * (U (x₀ + h * l) - U x₀) +
          w s * (U (x₀ + h) - U (x₀ + h * l))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (by linarith) hh'
    have lim1 := (tendsto_slope_ray hd 1).const_mul (w r)
    have lim2 := ((tendsto_slope_ray hd l).const_mul (w t)).add
      (((tendsto_slope_ray hd 1).sub (tendsto_slope_ray hd l)).const_mul (w s))
    have := le_of_tendsto_of_tendsto lim1 lim2
      (eventually_nhdsWithin_of_forall fun h (hh : (0 : ℝ) < h) => hineq h hh)
    have : w r * d ≤ (l * w t + (1 - l) * w s) * d := by nlinarith
    exact le_of_mul_le_mul_right this hdpos
  refine ⟨convex_Icc 0 1, fun a ha b hb α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rcases le_total b a with hba | hab
  · have := key a b α hb.1 hba ha.2 hα (by linarith)
    rw [show β = 1 - α by linarith]; exact this
  · have := key b a β ha.1 hab hb.2 hβ (by linarith)
    rw [show α = 1 - β by linarith, show (1 - β) * a + β * b = β * b + (1 - β) * a by ring]
    linarith

/-- Four-point lottery: mass `1 − s − δ` at index 0, `δ` at index 1, `s` at
index 3. -/
noncomputable def baseLot (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) : Lottery 3 where
  p k := if k = 0 then 1 - s - δ else if k = 1 then δ else if k = 3 then s else 0
  nonneg k := by split_ifs <;> linarith
  sum_eq_one := by simp [sum_range_succ]
  eq_zero_of_lt k hk := by
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    have h3 : k ≠ 3 := by omega
    simp [h0, h1, h3]

/-- The spread of `baseLot`: the mass `δ` at index 1 goes to indices 0 and 2
with weights `1 − λ` and `λ`. -/
noncomputable def spreadLot (s δ l : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : Lottery 3 where
  p k := if k = 0 then 1 - s - δ * l else if k = 2 then δ * l else if k = 3 then s else 0
  nonneg k := by split_ifs <;> nlinarith
  sum_eq_one := by simp [sum_range_succ]
  eq_zero_of_lt k hk := by
    have h0 : k ≠ 0 := by omega
    have h2 : k ≠ 2 := by omega
    have h3 : k ≠ 3 := by omega
    simp [h0, h2, h3]

theorem G_baseLot (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) :
    G (baseLot s δ hs hδ h) 1 = s + δ ∧ G (baseLot s δ hs hδ h) 2 = s ∧
      G (baseLot s δ hs hδ h) 3 = s := by
  refine ⟨?_, ?_, ?_⟩
  · simp [G, baseLot, sum_Ico_eq_sum_range, sum_range_succ]; ring
  · simp [G, baseLot, sum_Ico_eq_sum_range, sum_range_succ]
  · simp [G, baseLot]

theorem G_spreadLot (s δ l : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    G (spreadLot s δ l hs hδ h hl0 hl1) 1 = s + δ * l ∧
      G (spreadLot s δ l hs hδ h hl0 hl1) 2 = s + δ * l ∧
      G (spreadLot s δ l hs hδ h hl0 hl1) 3 = s := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [G, spreadLot, sum_Ico_eq_sum_range, sum_range_succ] <;> ring

/-- On the grid `a, (1 − λ) a + λ b, b, b + 1`, `spreadLot` is a
mean-preserving spread of `baseLot`. -/
theorem isMPS_spread (s δ l : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (h : s + δ ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    IsMPS (fun k : ℕ => if k = 0 then a else if k = 1 then (1 - l) * a + l * b else
        if k = 2 then b else b + 1)
      (spreadLot s δ l hs hδ h hl0 hl1) (baseLot s δ hs hδ h) := by
  obtain ⟨p1, p2, p3⟩ := G_baseLot s δ hs hδ h
  obtain ⟨q1, q2, q3⟩ := G_spreadLot s δ l hs hδ h hl0 hl1
  constructor
  · rw [eu_eq_layer, eu_eq_layer]
    simp only [sum_range_succ, sum_range_zero, p1, p2, p3, q1, q2, q3]
    norm_num; ring
  · intro m hm
    interval_cases m
    · simp
    · simp only [sum_range_succ, sum_range_zero, p1, q1]; norm_num
      nlinarith [mul_nonneg (mul_nonneg hδ (sub_nonneg.2 hl1)) (mul_nonneg hl0 (sub_nonneg.2 hab))]
    · simp only [sum_range_succ, sum_range_zero, p1, p2, q1, q2]; norm_num; ring_nf; rfl
    · simp only [sum_range_succ, sum_range_zero, p1, p2, p3, q1, q2, q3]; norm_num; ring_nf; rfl

/-- **Chew–Karni–Safra, necessity of concave utility.** -/
theorem concave_of_stronglyRiskAverse {w U : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hS : StronglyRiskAverse w U) {s e : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (he : HasDerivAt w e s)
    (hepos : 0 < e) : ConcaveOn ℝ Set.univ U := by
  have key : ∀ a b l : ℝ, a ≤ b → 0 ≤ l → l ≤ 1 →
      (1 - l) * U a + l * U b ≤ U ((1 - l) * a + l * b) := by
    intro a b l hab hl0 hl1
    set m := (1 - l) * a + l * b
    set x : ℕ → ℝ := fun k => if k = 0 then a else if k = 1 then m else if k = 2 then b else b + 1
    have hmono : MonotoneOnGrid 3 x := fun k hk => by
      interval_cases k <;> simp [x, m] <;> nlinarith
    have hineq : ∀ δ ∈ Set.Ioo (0 : ℝ) (1 - s),
        (δ⁻¹ * (w (s + δ * l) - w s)) * (U b - U m) ≤
          (δ⁻¹ * (w (s + δ * 1) - w s) - δ⁻¹ * (w (s + δ * l) - w s)) * (U m - U a) := by
      intro δ hδ
      have hsum : s + δ ≤ 1 := by linarith [hδ.2]
      have := hS 3 x hmono _ _ (isMPS_spread s δ l hs0.le hδ.1.le hsum hl0 hl1 hab)
      obtain ⟨p1, p2, p3⟩ := G_baseLot s δ hs0.le hδ.1.le hsum
      obtain ⟨q1, q2, q3⟩ := G_spreadLot s δ l hs0.le hδ.1.le hsum hl0 hl1
      rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1] at this
      simp only [sum_range_succ, sum_range_zero, p1, p2, p3, q1, q2, q3, x] at this
      norm_num at this
      have hd' : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.1.le
      rw [mul_one]
      have e1 : (δ⁻¹ * (w (s + δ * l) - w s)) * (U b - U m) =
          δ⁻¹ * ((w (s + δ * l) - w s) * (U b - U m)) := by ring
      have e2 : (δ⁻¹ * (w (s + δ) - w s) - δ⁻¹ * (w (s + δ * l) - w s)) * (U m - U a) =
          δ⁻¹ * ((w (s + δ) - w (s + δ * l)) * (U m - U a)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (by linarith) hd'
    have lim1 := (tendsto_slope_ray he l).mul_const (U b - U m)
    have lim2 := ((tendsto_slope_ray he 1).sub (tendsto_slope_ray he l)).mul_const (U m - U a)
    have hlim := le_of_tendsto_of_tendsto lim1 lim2 (by
      filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 - s)] with δ hδ
      exact hineq δ hδ)
    have : e * ((1 - l) * U a + l * U b) ≤ e * U m := by nlinarith
    exact le_of_mul_le_mul_left this hepos
  refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rcases le_total a b with hab | hba
  · have := key a b β hab hβ (by linarith)
    rw [show α = 1 - β by linarith]; exact this
  · have := key b a α hba hα (by linarith)
    rw [show β = 1 - α by linarith, show α * a + (1 - α) * b = (1 - α) * b + α * a by ring]
    linarith

/-- **Chew–Karni–Safra (1987)**: under the regularity conditions, an RDU agent
is strongly risk averse iff utility is concave and probability weighting is
convex. -/
theorem cks_iff {w U : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hwm : MonotoneOn w (Set.Icc 0 1)) {s e : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (he : HasDerivAt w e s) (hepos : 0 < e) (hUm : Monotone U) {x₀ d : ℝ}
    (hd : HasDerivAt U d x₀) (hdpos : 0 < d) :
    StronglyRiskAverse w U ↔ ConvexOn ℝ (Set.Icc 0 1) w ∧ ConcaveOn ℝ Set.univ U := by
  constructor
  · intro hS
    exact ⟨convex_of_stronglyRiskAverse hw0 hw1 hS hd hdpos,
      concave_of_stronglyRiskAverse hw0 hw1 hS hs0 hs1 he hepos⟩
  · rintro ⟨hw, hU⟩ n x hx p q h
    exact cks_mps hw0 hw1 hw hwm hU (hUm.monotoneOn _) (fun _ _ => Set.mem_univ _) hx h

theorem hasDerivAt_sq_half : HasDerivAt (fun t : ℝ => t ^ 2) 1 (1 / 2) := by
  have := hasDerivAt_pow 2 (1 / 2 : ℝ)
  norm_num at this ⊢
  exact this

/-- Non-vacuity of the utility half: with `w t = t²`, exponential (convex)
utility of money is not strongly risk averse. -/
theorem exp_not_stronglyRiskAverse : ¬ StronglyRiskAverse (fun t : ℝ => t ^ 2) Real.exp := by
  intro hS
  have hc := concave_of_stronglyRiskAverse (by norm_num) (by norm_num) hS (by norm_num)
    (by norm_num) hasDerivAt_sq_half one_pos
  have := hc.2 (Set.mem_univ (-1)) (Set.mem_univ 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  norm_num at this
  have h1 := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  have h2 := Real.exp_pos (-1)
  linarith

/-- Non-vacuity of the weighting half: with linear utility, the concave
weighting `w t = 2t − t²` is not strongly risk averse. -/
theorem concaveW_not_stronglyRiskAverse :
    ¬ StronglyRiskAverse (fun t : ℝ => 2 * t - t ^ 2) id := by
  intro hS
  have hc := convex_of_stronglyRiskAverse (by norm_num) (by norm_num) hS (hasDerivAt_id 0)
    one_pos
  have := hc.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  norm_num at this

/-- Both regularity conditions are met by `w t = t²` and linear utility, which
is strongly risk averse. -/
theorem sq_id_stronglyRiskAverse : StronglyRiskAverse (fun t : ℝ => t ^ 2) id :=
  (cks_iff (by norm_num) (by norm_num) sq_monotoneOn (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) hasDerivAt_sq_half one_pos monotone_id (hasDerivAt_id 0) one_pos).2
    ⟨sq_convex, concaveOn_id convex_univ⟩

end RankDependent

end Econ
