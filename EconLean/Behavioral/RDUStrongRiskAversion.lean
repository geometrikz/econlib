/-
# Strong risk aversion under rank-dependent utility

References. M. Yaari (1987), "The Dual Theory of Choice under Risk",
*Econometrica* 55(1); S. Chew, E. Karni and Z. Safra (1987), "Risk Aversion
in the Theory of Expected Utility with Rank Dependent Probabilities", *JET*
42(2); M. Rothschild and J. Stiglitz (1970), "Increasing Risk I"; L. Fuchs
(1947), "A new proof of an inequality of Hardy–Littlewood–Pólya".

Builds on `RankDependent.lean` and `RDURiskAttitude.lean`.

**Results.**
* `fuchs` (**weighted Karamata / Fuchs inequality**): for a function `f`
  convex on a set `I`, weights `c` (no sign condition is needed), and two
  sequences `x`, `y` in `I` that are both decreasing, if every weighted
  partial sum of `x − y` is nonnegative and the total is zero, then
  `Σ c (f x − f y) ≥ 0`.
* `IsMPS x q p`: equal means and, at every grid point,
  `Σ_{k<m} G q (k+1) Δx_k ≤ Σ_{k<m} G p (k+1) Δx_k`. When `x` is weakly
  increasing this says `q` is a **mean-preserving spread** of `p`
  (Rothschild–Stiglitz): the integrated distribution function of `q` lies
  above that of `p`. On other grids it is only an algebraic condition.
* `yaari_strongRiskAverse_iff` (**Yaari 1987; Chew–Karni–Safra 1987**): a
  dual-theory agent (linear utility of money, RDU with weighting `w`,
  `w 0 = 0`, `w 1 = 1`) weakly dislikes every mean-preserving spread, on every
  weakly increasing outcome grid, iff `w` is convex on `[0, 1]`. Sufficiency
  (`yaari_mps`) holds as an algebraic inequality on any grid; only the
  converse uses a weakly increasing one (with the middle grid point chosen
  to match the convex-combination weight, so no continuity of `w` is used).
* Non-vacuity: `triLot`, `isMPS_tri` (a concrete spread on a three-point
  grid), `sq_convex` (`w t = t²` is convex).

**Scope.** Only linear utility of money (Yaari) is covered. Chew–Karni–Safra's
general RDU result (strong risk aversion iff `w` convex and `u` concave) and
the equivalence of the integral condition with sequences of elementary
spreads are not formalized.
-/
module

public import EconLean.Behavioral.RDURiskAttitude
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

namespace Econ

namespace RankDependent

open Finset

/-! ### Fuchs' inequality -/

/-- An Abel-summation lemma: if all partial sums of `a` are nonnegative and
`s` is decreasing along the support of `a`, then `Σ s a ≥ σ Σ a` for any
lower bound `σ` of `s` on the support. -/
theorem abel_support (a s : ℕ → ℝ) :
    ∀ (n : ℕ) (σ : ℝ), (∀ m ≤ n, 0 ≤ ∑ k ∈ range m, a k) →
      (∀ j k, j < k → k < n → a j ≠ 0 → a k ≠ 0 → s k ≤ s j) →
      (∀ k < n, a k ≠ 0 → σ ≤ s k) →
      σ * ∑ k ∈ range n, a k ≤ ∑ k ∈ range n, s k * a k := by
  intro n
  induction n with
  | zero => intro σ _ _ _; simp
  | succ n ih =>
    intro σ hP hs hσ
    rw [sum_range_succ, sum_range_succ]
    have hP' : ∀ m ≤ n, 0 ≤ ∑ k ∈ range m, a k := fun m hm => hP m (by omega)
    have hs' : ∀ j k, j < k → k < n → a j ≠ 0 → a k ≠ 0 → s k ≤ s j :=
      fun j k hjk hk => hs j k hjk (by omega)
    by_cases han : a n = 0
    · rw [han, mul_zero, add_zero, add_zero]
      exact ih σ hP' hs' fun k hk => hσ k (by omega)
    · have h1 := ih (s n) hP' hs' fun k hk hak => hs k n hk (by omega) hak han
      have hPn := hP (n + 1) le_rfl
      rw [sum_range_succ] at hPn
      have h2 : σ * (∑ k ∈ range n, a k + a n) ≤ s n * (∑ k ∈ range n, a k + a n) :=
        mul_le_mul_of_nonneg_right (hσ n (by omega) han) hPn
      nlinarith

/-- Chord slopes of a convex function increase in both endpoints. -/
theorem slope_le_slope {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) {a b a' b' : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (ha' : a' ∈ I) (hb' : b' ∈ I) (haa : a' ≤ a) (hbb : b' ≤ b)
    (hab : a ≠ b) (hab' : a' ≠ b') : slope f b' a' ≤ slope f b a := by
  by_cases h : a' = b
  · subst h
    have hab2 : a ≠ b' := fun e => by subst e; exact hab (le_antisymm haa hbb).symm
    calc slope f b' a' ≤ slope f b' a :=
          hf.slope_mono hb' ⟨ha', hab'⟩ ⟨ha, hab2⟩ haa
      _ = slope f a b' := slope_comm _ _ _
      _ ≤ slope f a a' := hf.slope_mono ha ⟨hb', Ne.symm hab2⟩ ⟨ha', Ne.symm hab⟩ hbb
      _ = slope f a' a := slope_comm _ _ _
  · calc slope f b' a' = slope f a' b' := slope_comm _ _ _
      _ ≤ slope f a' b := hf.slope_mono ha' ⟨hb', Ne.symm hab'⟩ ⟨hb, Ne.symm h⟩ hbb
      _ = slope f b a' := slope_comm _ _ _
      _ ≤ slope f b a := hf.slope_mono hb ⟨ha', h⟩ ⟨ha, hab⟩ haa

/-- **Fuchs' inequality** (weighted Karamata). -/
theorem fuchs {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) (n : ℕ) {c x y : ℕ → ℝ}
    (hxI : ∀ k < n, x k ∈ I) (hyI : ∀ k < n, y k ∈ I)
    (hx : ∀ j k, j < k → k < n → x k ≤ x j) (hy : ∀ j k, j < k → k < n → y k ≤ y j)
    (hP : ∀ m ≤ n, 0 ≤ ∑ k ∈ range m, c k * (x k - y k))
    (htot : ∑ k ∈ range n, c k * (x k - y k) = 0) :
    0 ≤ ∑ k ∈ range n, c k * (f (x k) - f (y k)) := by
  set a : ℕ → ℝ := fun k => c k * (x k - y k)
  set s : ℕ → ℝ := fun k => slope f (y k) (x k)
  have hsa : ∀ k, c k * (f (x k) - f (y k)) = s k * a k := fun k => by
    show c k * (f (x k) - f (y k)) = slope f (y k) (x k) * (c k * (x k - y k))
    rw [slope_def_field]
    by_cases hk : x k = y k
    · simp [hk]
    · have : x k - y k ≠ 0 := sub_ne_zero.2 hk
      field_simp
  have hne : ∀ k, a k ≠ 0 → x k ≠ y k := fun k hk e => hk (by simp [a, e])
  have hmono : ∀ j k, j < k → k < n → a j ≠ 0 → a k ≠ 0 → s k ≤ s j := by
    intro j k hjk hk hj hk'
    exact slope_le_slope hf (hxI j (by omega)) (hyI j (by omega)) (hxI k hk) (hyI k hk)
      (hx j k hjk hk) (hy j k hjk hk) (hne j hj) (hne k hk')
  set σ : ℝ := -∑ k ∈ range n, |s k|
  have hσ : ∀ k < n, a k ≠ 0 → σ ≤ s k := fun k hk _ => by
    have := single_le_sum (f := fun k => |s k|) (fun i _ => abs_nonneg _) (mem_range.2 hk)
    linarith [neg_abs_le (s k)]
  have := abel_support a s n σ hP hmono hσ
  rw [htot, mul_zero] at this
  rw [sum_congr rfl fun k _ => hsa k]
  exact this

/-! ### Mean-preserving spreads and Yaari's dual theory -/

variable {n : ℕ}

theorem G_antitone (p : Lottery n) {j k : ℕ} (h : j ≤ k) : G p k ≤ G p j := by
  unfold G
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi; simp only [mem_Ico] at hi ⊢; omega
  · intro i _ _; exact p.nonneg i

/-- `q` is a **mean-preserving spread** of `p` on the outcome grid `x`
(Rothschild–Stiglitz integral condition at the grid points). -/
def IsMPS (x : ℕ → ℝ) (q p : Lottery n) : Prop :=
  eu x q = eu x p ∧ ∀ m ≤ n,
    ∑ k ∈ range m, G q (k + 1) * (x (k + 1) - x k) ≤ ∑ k ∈ range m, G p (k + 1) * (x (k + 1) - x k)

/-- **Yaari, sufficiency**: with convex `w`, the dual-theory value
`rdu w x` never increases under a mean-preserving spread. -/
theorem yaari_mps {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw : ConvexOn ℝ (Set.Icc 0 1) w) {x : ℕ → ℝ} {p q : Lottery n} (h : IsMPS x q p) :
    rdu w x q ≤ rdu w x p := by
  rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1, add_le_add_iff_left]
  have htot : ∑ k ∈ range n, (x (k + 1) - x k) * (G p (k + 1) - G q (k + 1)) = 0 := by
    have := h.1
    rw [eu_eq_layer, eu_eq_layer, add_right_inj] at this
    rw [← sub_eq_zero.2 this.symm, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have := fuchs hw n (c := fun k => x (k + 1) - x k) (x := fun k => G p (k + 1))
    (y := fun k => G q (k + 1))
    (fun k _ => ⟨G_nonneg _ _, G_le_one _ _⟩) (fun k _ => ⟨G_nonneg _ _, G_le_one _ _⟩)
    (fun j k hjk _ => G_antitone p (by omega)) (fun j k hjk _ => G_antitone q (by omega))
    (fun m hm => by
      have := h.2 m hm
      rw [← sub_nonneg, ← sum_sub_distrib] at this
      exact this.trans_eq (sum_congr rfl fun k _ => by ring))
    htot
  rw [← sub_nonneg, ← sum_sub_distrib]
  exact this.trans_eq (sum_congr rfl fun k _ => by ring)

/-- The lottery on `{0, 1, 2}` with `Prob(≥ 1) = t` and `Prob(≥ 2) = s`. -/
noncomputable def triLot (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) : Lottery 2 where
  p k := if k = 0 then 1 - t else if k = 1 then t - s else if k = 2 then s else 0
  nonneg k := by split_ifs <;> linarith
  sum_eq_one := by simp [sum_range_succ]
  eq_zero_of_lt k hk := by
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    have h2 : k ≠ 2 := by omega
    simp [h0, h1, h2]

theorem G_triLot_one (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    G (triLot t s hs hst ht) 1 = t := by
  simp [G, triLot, sum_Ico_eq_sum_range, sum_range_succ]

theorem G_triLot_two (t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    G (triLot t s hs hst ht) 2 = s := by
  simp [G, triLot]

/-- Non-vacuity: on the grid `0, λ, 1`, moving the inner mass of
`triLot t s` to the extremes so that `Prob(≥ 1) = Prob(≥ 2) = λt + (1−λ)s`
is a mean-preserving spread. -/
theorem isMPS_tri {t s l : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    let r := l * t + (1 - l) * s
    ∀ (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
    IsMPS (fun k : ℕ => if k = 0 then 0 else if k = 1 then l else 1)
      (triLot r r hr0 le_rfl hr1) (triLot t s hs hst ht) := by
  intro r hr0 hr1
  have hrt : r ≤ t := by simp only [r]; nlinarith
  constructor
  · rw [eu_eq_layer, eu_eq_layer]
    simp [sum_range_succ, G_triLot_one, G_triLot_two, r]
    ring
  · intro m hm
    interval_cases m
    · simp
    · simp [G_triLot_one]; nlinarith
    · simp [sum_range_succ, G_triLot_one, G_triLot_two, r]; nlinarith

/-- **Yaari (1987), Chew–Karni–Safra (1987)**: a dual-theory agent dislikes
every mean-preserving spread on every weakly increasing outcome grid iff `w` is
convex on `[0, 1]`. -/
theorem yaari_strongRiskAverse_iff {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    ConvexOn ℝ (Set.Icc 0 1) w ↔
      ∀ (n : ℕ) (x : ℕ → ℝ), MonotoneOnGrid n x → ∀ p q : Lottery n, IsMPS x q p →
        rdu w x q ≤ rdu w x p := by
  constructor
  · intro hw n x _ p q h
    exact yaari_mps hw0 hw1 hw h
  · intro h
    -- convexity along `s ≤ t`
    have key : ∀ t s l : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → 0 ≤ l → l ≤ 1 →
        w (l * t + (1 - l) * s) ≤ l * w t + (1 - l) * w s := by
      intro t s l hs hst ht hl0 hl1
      have hr0 : 0 ≤ l * t + (1 - l) * s := by nlinarith
      have hr1 : l * t + (1 - l) * s ≤ 1 := by nlinarith
      have := h 2 (fun k : ℕ => if k = 0 then 0 else if k = 1 then l else 1)
        (fun k hk => by interval_cases k <;> simp [hl0, hl1]) _ _
        (isMPS_tri hs hst ht hl0 hl1 hr0 hr1)
      rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1] at this
      simp [sum_range_succ, G_triLot_one, G_triLot_two] at this
      nlinarith
    refine ⟨convex_Icc 0 1, fun a ha b hb α β hα hβ hαβ => ?_⟩
    simp only [smul_eq_mul]
    rcases le_total b a with hba | hab
    · have := key a b α hb.1 hba ha.2 hα (by linarith)
      rw [show β = 1 - α by linarith]; exact this
    · have := key b a β ha.1 hab hb.2 hβ (by linarith)
      rw [show α = 1 - β by linarith, show (1 - β) * a + β * b = β * b + (1 - β) * a by ring]
      linarith

/-- Non-vacuity: `w t = t²` is convex on `[0, 1]`. -/
theorem sq_convex : ConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => t ^ 2) :=
  (convexOn_pow 2).subset Set.Icc_subset_Ici_self (convex_Icc 0 1)

end RankDependent

end Econ
