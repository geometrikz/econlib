/-
# Narrow bracketing and mental accounting

References. A. Tversky and D. Kahneman (1981), "The Framing of Decisions and
the Psychology of Choice", *Science* 211 (the concurrent-decisions problem);
D. Read, G. Loewenstein and M. Rabin (1999), "Choice Bracketing", *J. Risk
Uncertainty* 19 (Rabin and Weizsäcker 2009, *AER* 99(4), prove a general
version for non-CARA utility, formalized in `RabinWeizsacker.lean`; this file
has the Tversky–Kahneman example); R. Thaler (1985), "Mental Accounting and
Consumer Choice", *Marketing Science* 4(3) (hedonic editing).

**Narrow bracketing.** Two concurrent decisions:
* Decision 1: `A` = a sure gain of 240, or `B` = 1000 with probability 1/4;
* Decision 2: `C` = a sure loss of 750, or `D` = a loss of 1000 with
  probability 3/4.
Most subjects choose `A` and `D`. Resolving `B` and `D` with the same coin
(as in Tversky–Kahneman's presentation), `A ⊕ D` pays `240` w.p. `1/4` and
`−760` w.p. `3/4`, while `B ⊕ C` pays `250` and `−750` in the same events,
so `B ⊕ C` state-wise dominates `A ⊕ D`.
* `dominated`: every expected-utility maximizer with strictly increasing `u`
  who brackets broadly strictly prefers `B ⊕ C` to `A ⊕ D`.
* `narrow_choices_exist`: an S-shaped value function (strictly increasing,
  concave on gains, convex on losses, loss-averse, `v(0) = 0`) applied
  decision by decision picks both `A` and `D`. So narrow bracketing with
  prospect-theory values can produce a dominated combined choice.

**Mental accounting (hedonic editing).** For a value function `v` with
`v(0) = 0`:
* `segregate_gains`: concave on gains ⇒ `v(x + y) ≤ v(x) + v(y)` for gains:
  two separate gains feel better than one combined gain;
* `integrate_losses`: convex on losses ⇒ `v(−x) + v(−y) ≤ v(−(x + y))`:
  losses feel less bad combined;
* `integrate_mixed`: concave on gains and loss-averse
  (`v(−y) ≤ −v(y)`) ⇒ `v(x) + v(−y) ≤ v(x − y)` for `x ≥ y ≥ 0`: a small
  loss is best netted out of a larger gain ("cancellation").
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section

namespace Econ

namespace Bracketing

open Set

/-! ### Narrow bracketing -/

/-- Expected utility of a lottery paying `a` w.p. `1/4` and `b` w.p. `3/4`. -/
def eu (u : ℝ → ℝ) (a b : ℝ) : ℝ := 1 / 4 * u a + 3 / 4 * u b

/-- **State-wise dominance**: `B ⊕ C` beats `A ⊕ D` for every strictly
increasing utility. -/
theorem dominated {u : ℝ → ℝ} (hu : StrictMono u) : eu u 240 (-760) < eu u 250 (-750) := by
  unfold eu
  have h1 := hu (show (240 : ℝ) < 250 by norm_num)
  have h2 := hu (show (-760 : ℝ) < -750 by norm_num)
  linarith

/-- A narrow bracketer with value `v` picks `A` over `B` in decision 1. -/
def ChoosesA (v : ℝ → ℝ) : Prop := 1 / 4 * v 1000 + 3 / 4 * v 0 < v 240

/-- A narrow bracketer with value `v` picks `D` over `C` in decision 2. -/
def ChoosesD (v : ℝ → ℝ) : Prop := v (-750) < 3 / 4 * v (-1000) + 1 / 4 * v 0

/-- The witness value function: slope `1` on `[−630·10/9, 300]`, slope `1/10`
beyond (`min x (270 + x/10)` on gains, `max x (−630 + x/10)` on losses). -/
def vS (x : ℝ) : ℝ := max (min x (270 + x / 10)) (-630 + x / 10)

theorem vS_strictMono : StrictMono vS := fun a b h =>
  max_lt_max (lt_min (min_lt_of_left_lt h) (min_lt_of_right_lt (by linarith))) (by linarith)

theorem vS_of_nonneg {x : ℝ} (hx : 0 ≤ x) : vS x = min x (270 + x / 10) :=
  max_eq_left (le_min (by linarith) (by linarith))

theorem vS_of_nonpos {x : ℝ} (hx : x ≤ 0) : vS x = max x (-630 + x / 10) := by
  rw [vS, min_eq_left (by linarith)]

private theorem affine_concaveOn (c d : ℝ) {s : Set ℝ} (hs : Convex ℝ s) :
    ConcaveOn ℝ s fun x => c + d * x :=
  ⟨hs, fun _ _ _ _ a b _ _ hab => le_of_eq (by
    simp only [smul_eq_mul]; rw [show b = 1 - a by linarith]; ring)⟩

private theorem affine_convexOn (c d : ℝ) {s : Set ℝ} (hs : Convex ℝ s) :
    ConvexOn ℝ s fun x => c + d * x :=
  ⟨hs, fun _ _ _ _ a b _ _ hab => le_of_eq (by
    simp only [smul_eq_mul]; rw [show b = 1 - a by linarith]; ring)⟩

theorem vS_concaveOn : ConcaveOn ℝ (Ici 0) vS := by
  have h : ConcaveOn ℝ (Ici 0) (fun x : ℝ => min x (270 + x / 10)) := by
    have := (concaveOn_id (convex_Ici (0 : ℝ))).inf (affine_concaveOn 270 (1 / 10) (convex_Ici 0))
    refine this.congr fun x _ => ?_
    show min x (270 + 1 / 10 * x) = _; ring_nf
  exact h.congr fun x hx => (vS_of_nonneg hx).symm

theorem vS_convexOn : ConvexOn ℝ (Iic 0) vS := by
  have h : ConvexOn ℝ (Iic 0) (fun x : ℝ => max x (-630 + x / 10)) := by
    have := (convexOn_id (convex_Iic (0 : ℝ))).sup (affine_convexOn (-630) (1 / 10) (convex_Iic 0))
    refine this.congr fun x _ => ?_
    show max x (-630 + 1 / 10 * x) = _; ring_nf
  exact h.congr fun x hx => (vS_of_nonpos hx).symm

/-- `vS` is loss-averse: `v(−y) ≤ −v(y)` for `y ≥ 0`. -/
theorem vS_lossAverse {y : ℝ} (hy : 0 ≤ y) : vS (-y) ≤ -vS y := by
  rw [vS_of_nonpos (by linarith), vS_of_nonneg hy]
  rcases le_total y (270 + y / 10) with h | h
  · rw [min_eq_left h]; exact max_le le_rfl (by linarith)
  · rw [min_eq_right h]; exact max_le (by linarith) (by linarith)

/-- **Narrow bracketing produces dominated choices.** There is an S-shaped
value function (strictly increasing, `v(0) = 0`, concave on gains, convex on
losses, loss-averse) under which the narrow bracketer picks both `A` and `D`,
although for that very `v` (indeed for every strictly increasing utility)
the combination `A ⊕ D` is worse than `B ⊕ C`. -/
theorem narrow_choices_exist : ∃ v : ℝ → ℝ, StrictMono v ∧ v 0 = 0 ∧ ConcaveOn ℝ (Ici 0) v ∧
    ConvexOn ℝ (Iic 0) v ∧ (∀ y, 0 ≤ y → v (-y) ≤ -v y) ∧ ChoosesA v ∧ ChoosesD v ∧
    eu v 240 (-760) < eu v 250 (-750) := by
  refine ⟨vS, vS_strictMono, by norm_num [vS], vS_concaveOn, vS_convexOn,
    fun y hy => vS_lossAverse hy, ?_, ?_, dominated vS_strictMono⟩ <;>
    norm_num [ChoosesA, ChoosesD, vS]

/-! ### Mental accounting -/

/-- Concave on gains with `v(0) = 0` ⇒ subadditive on gains. -/
theorem segregate_gains {v : ℝ → ℝ} (hv : ConcaveOn ℝ (Ici 0) v) (h0 : v 0 = 0) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : v (x + y) ≤ v x + v y := by
  rcases (add_nonneg hx hy).lt_or_eq with hs | hs
  · have hxy : (0 : ℝ) ≤ x + y := hs.le
    have k1 := hv.2 (mem_Ici.2 hxy) (mem_Ici.2 le_rfl) (div_nonneg hx hxy) (div_nonneg hy hxy)
      (by field_simp)
    have k2 := hv.2 (mem_Ici.2 hxy) (mem_Ici.2 le_rfl) (div_nonneg hy hxy) (div_nonneg hx hxy)
      (by field_simp; ring)
    simp only [smul_eq_mul, mul_zero, add_zero, h0] at k1 k2
    rw [div_mul_cancel₀ _ hs.ne'] at k1 k2
    have : x / (x + y) * v (x + y) + y / (x + y) * v (x + y) = v (x + y) := by
      field_simp
    linarith
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0, h0]

/-- Convex on losses with `v(0) = 0` ⇒ losses are better integrated. -/
theorem integrate_losses {v : ℝ → ℝ} (hv : ConvexOn ℝ (Iic 0) v) (h0 : v 0 = 0) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : v (-x) + v (-y) ≤ v (-(x + y)) := by
  have hc : ConcaveOn ℝ (Ici 0) (fun z => -v (-z)) := by
    refine ⟨convex_Ici 0, fun a ha b hb s t hs ht hst => ?_⟩
    have := hv.2 (x := -a) (y := -b) (by simpa using ha) (by simpa using hb) hs ht hst
    simp only [smul_eq_mul] at this ⊢
    have e : s * -a + t * -b = -(s * a + t * b) := by ring
    rw [e] at this
    linarith
  have := segregate_gains hc (by simp [h0]) hx hy
  rw [neg_add] at this ⊢
  linarith

/-- Concave on gains and loss-averse ⇒ a smaller loss is best netted against a
larger gain. -/
theorem integrate_mixed {v : ℝ → ℝ} (hv : ConcaveOn ℝ (Ici 0) v) (h0 : v 0 = 0)
    (hla : ∀ y, 0 ≤ y → v (-y) ≤ -v y) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    v x + v (-y) ≤ v (x - y) := by
  have := segregate_gains hv h0 (sub_nonneg.2 hxy) hy
  rw [sub_add_cancel] at this
  linarith [hla y hy]

end Bracketing

end Econ
