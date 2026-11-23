/-
# Myerson's lemma and revenue equivalence

MWG §23.D (Prop. 23.D.2 and the revenue equivalence theorem, Prop. 23.D.3); Myerson (1981).
An agent with a one-dimensional type `θ ∈ [a, b]` faces a direct mechanism: reporting `r`
gives the (interim expected) allocation `q r` for the payment `p r`, so type `θ` gets
`θ q(r) − p(r)`. The mechanism is **incentive compatible** if truthful reporting is optimal for
every type. Write `U θ = θ q(θ) − p(θ)` for the truthful payoff (the information rent).

Main results:
* `myerson_ic_iff` (MWG Prop. 23.D.2): incentive compatibility ⟺ `q` is nondecreasing on
  `[a, b]` and `U θ = U a + ∫ₐ^θ q` (the envelope formula).
* `revenue_equivalence` (single-agent interim form of MWG Prop. 23.D.3; in an auction apply it
  to each bidder's interim allocation and payment): two incentive compatible mechanisms with the same
  allocation rule and the same payoff for the lowest type charge the same payment to every
  type, hence raise the same expected revenue under any type distribution.

The key analytic step is `sub_eq_integral_of_sandwich`: if the increments of `U` are
sandwiched by a monotone `f`, `f x (y − x) ≤ U y − U x ≤ f y (y − x)`, then
`U b − U a = ∫ₐᵇ f` (proved with Riemann sums on uniform partitions, without assuming `U`
differentiable).
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import EconLean.Uncertainty.MoneyLottery

@[expose] public section

namespace Econ

open Set Finset intervalIntegral

/-- **Integral from a monotone sandwich.** If `f` is monotone on `[a, b]` and the increments of
`U` satisfy `f x (y − x) ≤ U y − U x ≤ f y (y − x)` for `a ≤ x ≤ y ≤ b`, then
`U b − U a = ∫ₐᵇ f`. -/
theorem sub_eq_integral_of_sandwich {f U : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b))
    (hU : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      f x * (y - x) ≤ U y - U x ∧ U y - U x ≤ f y * (y - x)) :
    U b - U a = ∫ x in a..b, f x := by
  set D := U b - U a - ∫ x in a..b, f x
  set C := (b - a) * (f b - f a)
  -- Step 1: `|D| ≤ C / N` for every number `N ≥ 1` of subintervals.
  have hbound : ∀ N : ℕ, 0 < N → |D| ≤ C / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    set h := (b - a) / N
    have hh : 0 ≤ h := div_nonneg (sub_nonneg.2 hab) hNr.le
    let x : ℕ → ℝ := fun k => a + k * h
    have hx0 : x 0 = a := by simp [x]
    have hxN : x N = b := by simp only [x, h]; field_simp; ring
    have hxs : ∀ k, x (k + 1) - x k = h := fun k => by simp only [x]; push_cast; ring
    have hxmem : ∀ k ≤ N, x k ∈ Icc a b := by
      intro k hk
      refine ⟨by simp only [x]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], ?_⟩
      have : (k : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh
      have hNh : (N : ℝ) * h = b - a := by simp only [h]; field_simp
      simp only [x]; linarith
    have hxle : ∀ k, x k ≤ x (k + 1) := fun k => by linarith [hxs k]
    have hint : ∀ k < N, IntervalIntegrable f MeasureTheory.volume (x k) (x (k + 1)) := by
      intro k hk
      refine MonotoneOn.intervalIntegrable (hf.mono ?_)
      rw [uIcc_of_le (hxle k)]
      exact Icc_subset_Icc (hxmem k hk.le).1 (hxmem (k + 1) hk).2
    -- Lower and upper Riemann sums.
    set L := ∑ k ∈ range N, f (x k) * h
    set R := ∑ k ∈ range N, f (x (k + 1)) * h
    have hRL : R - L = h * (f b - f a) := by
      simp only [R, L, ← Finset.sum_sub_distrib, ← sub_mul]
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun k => f (x k)), hxN, hx0]
      ring
    -- `U b − U a` lies between them.
    have htel : U b - U a = ∑ k ∈ range N, (U (x (k + 1)) - U (x k)) := by
      rw [Finset.sum_range_sub (fun k => U (x k)), hxN, hx0]
    have hU1 : L ≤ U b - U a := by
      rw [htel]
      exact Finset.sum_le_sum fun k hk => by
        have := (hU _ (hxmem k (mem_range.1 hk).le) _ (hxmem (k + 1) (mem_range.1 hk))
          (hxle k)).1
        rwa [hxs k] at this
    have hU2 : U b - U a ≤ R := by
      rw [htel]
      exact Finset.sum_le_sum fun k hk => by
        have := (hU _ (hxmem k (mem_range.1 hk).le) _ (hxmem (k + 1) (mem_range.1 hk))
          (hxle k)).2
        rwa [hxs k] at this
    -- So does the integral.
    have hsplit : ∫ y in a..b, f y = ∑ k ∈ range N, ∫ y in x k..x (k + 1), f y := by
      rw [sum_integral_adjacent_intervals hint, hx0, hxN]
    have hpiece : ∀ k < N, f (x k) * h ≤ ∫ y in x k..x (k + 1), f y ∧
        ∫ y in x k..x (k + 1), f y ≤ f (x (k + 1)) * h := by
      intro k hk
      have hsub : Icc (x k) (x (k + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (hxmem k hk.le).1 (hxmem (k + 1) hk).2
      constructor
      · have := integral_mono_on (hxle k) intervalIntegrable_const (hint k hk)
          (fun y hy => hf (hxmem k hk.le) (hsub hy) hy.1)
        rwa [integral_const, smul_eq_mul, hxs k, mul_comm] at this
      · have := integral_mono_on (hxle k) (hint k hk) intervalIntegrable_const
          (fun y hy => hf (hsub hy) (hxmem (k + 1) hk) hy.2)
        rwa [integral_const, smul_eq_mul, hxs k, mul_comm] at this
    have hI1 : L ≤ ∫ y in a..b, f y := by
      rw [hsplit]; exact Finset.sum_le_sum fun k hk => (hpiece k (mem_range.1 hk)).1
    have hI2 : ∫ y in a..b, f y ≤ R := by
      rw [hsplit]; exact Finset.sum_le_sum fun k hk => (hpiece k (mem_range.1 hk)).2
    have hCN : C / N = h * (f b - f a) := by simp only [C, h]; field_simp
    rw [hCN, abs_le]
    constructor <;> linarith
  -- Step 2: a quantity bounded by `C / N` for all `N` is zero.
  suffices hD0 : D = 0 from sub_eq_zero.1 hD0
  by_contra hD
  have hpos : 0 < |D| := abs_pos.2 hD
  obtain ⟨N, hN⟩ := exists_nat_gt (C / |D|)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have hC : 0 ≤ C := mul_nonneg (sub_nonneg.2 hab)
        (sub_nonneg.2 (hf ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))
      simp at hN
      exact absurd hN (not_lt.2 (div_nonneg hC hpos.le))
    · exact h0
  have h1 := hbound N hNpos
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  rw [div_lt_iff₀ hpos] at hN
  rw [le_div_iff₀ hNr] at h1
  linarith

/-- The truthful payoff (information rent) of type `θ`. -/
def infoRent (q p : ℝ → ℝ) (θ : ℝ) : ℝ := θ * q θ - p θ

/-- The direct mechanism `(q, p)` is **incentive compatible** on `[a, b]`. -/
def IsICMech (q p : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ θ ∈ Icc a b, ∀ r ∈ Icc a b, θ * q r - p r ≤ θ * q θ - p θ

/-- **Myerson's lemma** (MWG Prop. 23.D.2). A direct mechanism is incentive compatible on
`[a, b]` iff the allocation is nondecreasing and the information rent satisfies the envelope
formula `U θ = U a + ∫ₐ^θ q`. -/
theorem myerson_ic_iff {q p : ℝ → ℝ} {a b : ℝ} :
    IsICMech q p a b ↔ MonotoneOn q (Icc a b) ∧
      ∀ θ ∈ Icc a b, infoRent q p θ = infoRent q p a + ∫ s in a..θ, q s := by
  constructor
  · intro hIC
    -- IC between `x ≤ y` sandwiches the rent increment.
    have hsand : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
        q x * (y - x) ≤ infoRent q p y - infoRent q p x ∧
          infoRent q p y - infoRent q p x ≤ q y * (y - x) := by
      intro x hx y hy _
      have h1 := hIC y hy x hx
      have h2 := hIC x hx y hy
      simp only [infoRent]
      constructor <;> nlinarith
    have hmono : MonotoneOn q (Icc a b) := by
      intro x hx y hy hxy
      rcases hxy.eq_or_lt with rfl | hlt
      · exact le_rfl
      · obtain ⟨h1, h2⟩ := hsand x hx y hy hxy
        have : q x * (y - x) ≤ q y * (y - x) := h1.trans h2
        exact le_of_mul_le_mul_right this (sub_pos.2 hlt)
    refine ⟨hmono, fun θ hθ => ?_⟩
    have hsub : Icc a θ ⊆ Icc a b := Icc_subset_Icc le_rfl hθ.2
    have := sub_eq_integral_of_sandwich hθ.1 (hmono.mono hsub)
      fun x hx y hy hxy => hsand x (hsub hx) y (hsub hy) hxy
    linarith
  · rintro ⟨hmono, henv⟩ θ hθ r hr
    have hint : ∀ c ∈ Icc a b, IntervalIntegrable q MeasureTheory.volume a c := by
      intro c hc
      have hsub : uIcc a c ⊆ Icc a b := by
        rw [uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2
      exact MonotoneOn.intervalIntegrable (hmono.mono hsub)
    -- `U θ − U r = ∫_r^θ q ≥ (θ − r) q r`.
    have hdiff : infoRent q p θ - infoRent q p r = ∫ s in r..θ, q s := by
      rw [henv θ hθ, henv r hr, ← integral_interval_sub_left (hint θ hθ) (hint r hr)]
      ring
    have hge : (θ - r) * q r ≤ ∫ s in r..θ, q s := by
      rcases le_total r θ with hrθ | hθr
      · have hsub : Icc r θ ⊆ Icc a b := Icc_subset_Icc hr.1 hθ.2
        have hii : IntervalIntegrable q MeasureTheory.volume r θ :=
          MonotoneOn.intervalIntegrable (hmono.mono (by rw [uIcc_of_le hrθ]; exact hsub))
        have := integral_mono_on hrθ intervalIntegrable_const hii
          fun s hs => hmono hr (hsub hs) hs.1
        rwa [integral_const, smul_eq_mul] at this
      · have hsub : Icc θ r ⊆ Icc a b := Icc_subset_Icc hθ.1 hr.2
        have hii : IntervalIntegrable q MeasureTheory.volume θ r :=
          MonotoneOn.intervalIntegrable (hmono.mono (by rw [uIcc_of_le hθr]; exact hsub))
        have := integral_mono_on hθr hii intervalIntegrable_const
          fun s hs => hmono (hsub hs) hr hs.2
        rw [integral_const, smul_eq_mul] at this
        rw [integral_symm]
        linarith
    simp only [infoRent] at hdiff
    nlinarith

/-- **Revenue equivalence** (MWG Prop. 23.D.3). Two incentive compatible mechanisms with the
same allocation rule on `[a, b]` and the same payoff for the lowest type `a` charge every type
the same payment. -/
theorem revenue_equivalence {q p p' : ℝ → ℝ} {a b : ℝ}
    (h : IsICMech q p a b) (h' : IsICMech q p' a b) (ha : infoRent q p a = infoRent q p' a) :
    ∀ θ ∈ Icc a b, p θ = p' θ := by
  intro θ hθ
  have e := (myerson_ic_iff.1 h).2 θ hθ
  have e' := (myerson_ic_iff.1 h').2 θ hθ
  simp only [infoRent] at e e' ha
  linarith

/-- **Expected revenue is pinned down**: under any type distribution `F` supported in
`[a, b]`, the two mechanisms of `revenue_equivalence` raise the same expected revenue. -/
theorem expected_revenue_eq {q p p' : ℝ → ℝ} {a b : ℝ}
    (h : IsICMech q p a b) (h' : IsICMech q p' a b) (ha : infoRent q p a = infoRent q p' a)
    (F : SimpleLottery) (hF : ∀ x ∈ F.prob.support, x ∈ Icc a b) : F.expect p = F.expect p' :=
  F.expect_congr (subset_refl _) fun x hx => revenue_equivalence h h' ha x (hF x hx)

/-- **Witness: the second-price auction against a uniform rival.** With one rival bid uniform
on `[0, 1]`, a bidder of value `θ` wins with probability `q θ = θ` and pays the expected rival
bid when winning, `p θ = θ² / 2`. This is incentive compatible on `[0, 1]`. -/
example : IsICMech (fun θ => θ) (fun θ => θ ^ 2 / 2) 0 1 := by
  intro θ _ r _
  nlinarith [sq_nonneg (θ - r)]

end Econ
