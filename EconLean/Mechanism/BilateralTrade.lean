/-
# Impossibility of efficient, budget-balanced, strategy-proof bilateral trade

A buyer with value `v` and a seller with cost `c`, both privately known and ranging over the
same interval `[a, b]` with `a < b` (overlapping supports, as in Myerson–Satterthwaite 1983).
A direct mechanism specifies, for reports `(v, c)`, a trade probability `x v c`, a payment
`tB v c` by the buyer and a receipt `tS v c` by the seller. The buyer's payoff is
`v x − tB`, the seller's `tS − c x`.

Main result, `no_efficient_dsic_budgetBalanced_trade` (Hurwicz 1972; Green–Laffont 1979; the
dominant-strategy counterpart of MWG Prop. 23.E.1 / Myerson–Satterthwaite): no mechanism is
simultaneously
* **ex post efficient**: trade whenever `c < v`, no trade whenever `v < c`;
* **dominant-strategy incentive compatible** for both traders; and
* **budget balanced**: `tB = tS` at every report profile.
No participation constraint is needed.

The proof pins down payments by the threshold argument behind Myerson's lemma: given `c`, a
trading buyer pays exactly `c` more than a non-trading buyer; given `v`, a trading seller
receives exactly `v` more than a non-trading seller. Budget balance then forces two distinct
thresholds to coincide.

(The Bayesian Myerson–Satterthwaite theorem, with interim IC and interim IR under atomless
type distributions, is in `Mechanism/MyersonSatterthwaite.lean`.)
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ

open Set

/-- A direct bilateral-trade mechanism: trade probability and the two transfers, as functions
of the buyer's reported value and the seller's reported cost. -/
structure TradeMechanism where
  /-- Probability of trade. -/
  x : ℝ → ℝ → ℝ
  /-- Payment made by the buyer. -/
  tB : ℝ → ℝ → ℝ
  /-- Payment received by the seller. -/
  tS : ℝ → ℝ → ℝ

namespace TradeMechanism

variable (M : TradeMechanism) (a b : ℝ)

/-- Ex post efficiency on `[a, b]²`: trade iff gains from trade are positive (ties are free). -/
def IsEfficient : Prop :=
  ∀ v ∈ Icc a b, ∀ c ∈ Icc a b, (c < v → M.x v c = 1) ∧ (v < c → M.x v c = 0)

/-- Truthful reporting is a dominant strategy for the buyer. -/
def BuyerDSIC : Prop :=
  ∀ c ∈ Icc a b, ∀ v ∈ Icc a b, ∀ v' ∈ Icc a b,
    v * M.x v' c - M.tB v' c ≤ v * M.x v c - M.tB v c

/-- Truthful reporting is a dominant strategy for the seller. -/
def SellerDSIC : Prop :=
  ∀ v ∈ Icc a b, ∀ c ∈ Icc a b, ∀ c' ∈ Icc a b,
    M.tS v c' - c * M.x v c' ≤ M.tS v c - c * M.x v c

/-- Ex post budget balance: the seller receives exactly what the buyer pays. -/
def IsBudgetBalanced : Prop := ∀ v ∈ Icc a b, ∀ c ∈ Icc a b, M.tB v c = M.tS v c

end TradeMechanism

/-- A number squeezed between all points of `[a, y)` and all points of `(y, b]` is `y`. -/
lemma eq_of_squeeze {a b y d : ℝ} (hay : a < y) (hyb : y < b)
    (hup : ∀ v ∈ Ioc y b, d ≤ v) (hlo : ∀ v ∈ Ico a y, v ≤ d) : d = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hlo (max a d / 2 + y / 2) ⟨by
      have := le_max_left a d; linarith, by
      have : max a d < y := max_lt hay h; linarith⟩
    have : max a d / 2 + y / 2 ≤ d := this
    have h1 : d ≤ max a d := le_max_right a d
    have h2 : max a d < y := max_lt hay h
    rcases le_total a d with had | hda
    · rw [max_eq_right had] at this; linarith
    · rw [max_eq_left hda] at this h2; linarith
  · have := hup (min b d / 2 + y / 2) ⟨by
      have : y < min b d := lt_min hyb h; linarith, by
      have := min_le_left b d; linarith⟩
    rcases le_total b d with hbd | hdb
    · rw [min_eq_left hbd] at this; linarith
    · rw [min_eq_right hdb] at this; linarith

namespace TradeMechanism

variable {M : TradeMechanism} {a b : ℝ}

/-- Buyer types that trade at the same seller report pay the same. -/
lemma tB_eq_of_trade (he : M.IsEfficient a b) (hB : M.BuyerDSIC a b) {c v v' : ℝ}
    (hc : c ∈ Icc a b) (hv : v ∈ Icc a b) (hv' : v' ∈ Icc a b) (h1 : c < v) (h2 : c < v') :
    M.tB v c = M.tB v' c := by
  have e1 := (he v hv c hc).1 h1
  have e2 := (he v' hv' c hc).1 h2
  have := hB c hc v hv v' hv'
  have := hB c hc v' hv' v hv
  rw [e1, e2] at *
  linarith

/-- Buyer types that do not trade at the same seller report pay the same. -/
lemma tB_eq_of_noTrade (he : M.IsEfficient a b) (hB : M.BuyerDSIC a b) {c v v' : ℝ}
    (hc : c ∈ Icc a b) (hv : v ∈ Icc a b) (hv' : v' ∈ Icc a b) (h1 : v < c) (h2 : v' < c) :
    M.tB v c = M.tB v' c := by
  have e1 := (he v hv c hc).2 h1
  have e2 := (he v' hv' c hc).2 h2
  have := hB c hc v hv v' hv'
  have := hB c hc v' hv' v hv
  rw [e1, e2] at *
  linarith

/-- Seller types that trade at the same buyer report receive the same. -/
lemma tS_eq_of_trade (he : M.IsEfficient a b) (hS : M.SellerDSIC a b) {v c c' : ℝ}
    (hv : v ∈ Icc a b) (hc : c ∈ Icc a b) (hc' : c' ∈ Icc a b) (h1 : c < v) (h2 : c' < v) :
    M.tS v c = M.tS v c' := by
  have e1 := (he v hv c hc).1 h1
  have e2 := (he v hv c' hc').1 h2
  have := hS v hv c hc c' hc'
  have := hS v hv c' hc' c hc
  rw [e1, e2] at *
  linarith

/-- Seller types that do not trade at the same buyer report receive the same. -/
lemma tS_eq_of_noTrade (he : M.IsEfficient a b) (hS : M.SellerDSIC a b) {v c c' : ℝ}
    (hv : v ∈ Icc a b) (hc : c ∈ Icc a b) (hc' : c' ∈ Icc a b) (h1 : v < c) (h2 : v < c') :
    M.tS v c = M.tS v c' := by
  have e1 := (he v hv c hc).2 h1
  have e2 := (he v hv c' hc').2 h2
  have := hS v hv c hc c' hc'
  have := hS v hv c' hc' c hc
  rw [e1, e2] at *
  linarith

/-- **Buyer threshold pricing.** At an interior seller report `c`, a trading buyer pays exactly
`c` more than a non-trading buyer. -/
lemma tB_sub_eq (he : M.IsEfficient a b) (hB : M.BuyerDSIC a b) {c v v' : ℝ}
    (hac : a < c) (hcb : c < b) (hv : v ∈ Icc a b) (hv' : v' ∈ Icc a b) (h1 : c < v)
    (h2 : v' < c) : M.tB v c - M.tB v' c = c := by
  have hc : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  refine eq_of_squeeze hac hcb (fun u hu => ?_) (fun u hu => ?_)
  · have hu' : u ∈ Icc a b := ⟨by linarith [hu.1], hu.2⟩
    have := hB c hc u hu' v' hv'
    rw [(he u hu' c hc).1 hu.1, (he v' hv' c hc).2 h2,
      tB_eq_of_trade he hB hc hu' hv hu.1 h1] at this
    linarith
  · have hu' : u ∈ Icc a b := ⟨hu.1, by linarith [hu.2]⟩
    have := hB c hc u hu' v hv
    rw [(he u hu' c hc).2 hu.2, (he v hv c hc).1 h1,
      tB_eq_of_noTrade he hB hc hu' hv' hu.2 h2] at this
    linarith

/-- **Seller threshold pricing.** At an interior buyer report `v`, a trading seller receives
exactly `v` more than a non-trading seller. -/
lemma tS_sub_eq (he : M.IsEfficient a b) (hS : M.SellerDSIC a b) {v c c' : ℝ}
    (hav : a < v) (hvb : v < b) (hc : c ∈ Icc a b) (hc' : c' ∈ Icc a b) (h1 : c < v)
    (h2 : v < c') : M.tS v c - M.tS v c' = v := by
  have hv : v ∈ Icc a b := ⟨hav.le, hvb.le⟩
  refine eq_of_squeeze hav hvb (fun u hu => ?_) (fun u hu => ?_)
  · -- `u > v`: a non-trading seller of cost `u` does not mimic the trading report `c`.
    have hu' : u ∈ Icc a b := ⟨by linarith [hu.1], hu.2⟩
    have := hS v hv u hu' c hc
    rw [(he v hv u hu').2 hu.1, (he v hv c hc).1 h1,
      tS_eq_of_noTrade he hS hv hu' hc' hu.1 h2] at this
    linarith
  · -- `u < v`: a trading seller of cost `u` does not mimic the non-trading report `c'`.
    have hu' : u ∈ Icc a b := ⟨hu.1, by linarith [hu.2]⟩
    have := hS v hv u hu' c' hc'
    rw [(he v hv u hu').1 hu.2, (he v hv c' hc').2 h2,
      tS_eq_of_trade he hS hv hu' hc hu.2 h1] at this
    linarith

end TradeMechanism

open TradeMechanism in
/-- **No efficient, strategy-proof, budget-balanced bilateral trade** (Hurwicz; Green–Laffont).
With overlapping type intervals `[a, b]`, `a < b`, no direct mechanism is ex post efficient,
dominant-strategy incentive compatible for both traders, and ex post budget balanced. -/
theorem no_efficient_dsic_budgetBalanced_trade {a b : ℝ} (hab : a < b) (M : TradeMechanism)
    (he : M.IsEfficient a b) (hB : M.BuyerDSIC a b) (hS : M.SellerDSIC a b)
    (hBB : M.IsBudgetBalanced a b) : False := by
  set h := (b - a) / 5
  have hh : 0 < h := by simp only [h]; linarith
  have hb : b = a + 5 * h := by simp only [h]; ring
  -- Four interior points `x < y < z < w`.
  set x := a + h; set y := a + 2 * h; set z := a + 3 * h; set w := a + 4 * h
  have mem : ∀ k : ℝ, 0 ≤ k → k ≤ 5 → a + k * h ∈ Icc a b := fun k h0 h5 =>
    ⟨by nlinarith, by nlinarith⟩
  have hx : x ∈ Icc a b := by simpa only [one_mul] using mem 1 (by norm_num) (by norm_num)
  have hy : y ∈ Icc a b := mem 2 (by norm_num) (by norm_num)
  have hz : z ∈ Icc a b := mem 3 (by norm_num) (by norm_num)
  have hw : w ∈ Icc a b := mem 4 (by norm_num) (by norm_num)
  -- Buyer side at seller report `y`: `tB(z, y) − tB(x, y) = y`.
  have e1 := tB_sub_eq he hB (c := y) (by simp only [y]; linarith) (by simp only [y]; linarith)
    hz hx (by simp only [y, z]; linarith) (by simp only [x, y]; linarith)
  -- Seller side at buyer report `z`: `tS(z, y) − tS(z, w) = z`.
  have e2 := tS_sub_eq he hS (v := z) (by simp only [z]; linarith) (by simp only [z]; linarith)
    hy hw (by simp only [y, z]; linarith) (by simp only [z, w]; linarith)
  -- Linking the non-trading payments through budget balance.
  have l1 := tS_eq_of_noTrade he hS hx hy hw (by simp only [x, y]; linarith)
    (by simp only [x, w]; linarith)
  have l2 := tB_eq_of_noTrade he hB hw hz hx (by simp only [z, w]; linarith)
    (by simp only [x, w]; linarith)
  have b1 := hBB x hx y hy
  have b2 := hBB x hx w hw
  have b3 := hBB z hz w hw
  have b4 := hBB z hz y hy
  have : y = z := by linarith
  simp only [y, z] at this
  linarith

/-- **The hypotheses are individually satisfiable**: the posted price `p` is DSIC and budget
balanced (but not efficient), which shows the impossibility is not vacuous in its IC and
budget-balance conditions. -/
example (a b p : ℝ) :
    let M : TradeMechanism := ⟨fun v c => if c ≤ p ∧ p ≤ v then 1 else 0,
      fun v c => if c ≤ p ∧ p ≤ v then p else 0, fun v c => if c ≤ p ∧ p ≤ v then p else 0⟩
    M.BuyerDSIC a b ∧ M.SellerDSIC a b ∧ M.IsBudgetBalanced a b := by
  intro M
  refine ⟨fun c _ v _ v' _ => ?_, fun v _ c _ c' _ => ?_, fun _ _ _ _ => rfl⟩
  · simp only [M]
    by_cases hc : c ≤ p
    · by_cases h1 : p ≤ v' <;> by_cases h2 : p ≤ v <;> simp [hc, h1, h2]
      linarith
    · simp [hc]
  · simp only [M]
    by_cases hv : p ≤ v
    · by_cases h1 : c' ≤ p <;> by_cases h2 : c ≤ p <;> simp [hv, h1, h2]
      linarith
    · simp [hv]

end Econ
