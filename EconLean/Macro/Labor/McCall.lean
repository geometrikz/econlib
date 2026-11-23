/-
# The McCall job-search model

McCall (1970); Ljungqvist–Sargent ch. 6 (§6.3, the reservation wage and
mean-preserving spreads); Stokey–Lucas §10.7.

**The economics.** An unemployed worker draws one wage offer per period from
a known distribution: offer `w i` with probability `p i` (finitely many
possible offers). Accepting `w` gives `w` forever (value `w / (1 − β)`);
rejecting gives unemployment compensation `c` today and a new draw tomorrow.
The worker discounts by `β ∈ [0, 1)`. The Bellman equation for the value `V`
of holding offer `w` is

    V(w) = max { w / (1 − β),  c + β Σⱼ pⱼ V(wⱼ) }.

The solution has the **reservation-wage** form: accept iff `w ≥ w̄`, where `w̄`
is the unique solution of

    w̄ = (1 − β) c + β Σᵢ pᵢ max(wᵢ, w̄)      (equivalently
    w̄ − c = β/(1−β) · E[(w − w̄)⁺]).

Main results:
* `existsUnique_reservationWage`: `w̄` exists and is unique.
* `bellman_reservationWage`: `V(w) = max(w, w̄)/(1 − β)` solves the Bellman
  equation, and `bellman_unique`: it is the only solution, so the optimal
  policy is "accept iff `w ≥ w̄`" (`accept_iff`).
* `reservationWage_strictMono_c`: more generous benefits raise `w̄`.
* `reservationWage_mono_riskier`: a riskier offer distribution (in the convex
  order, which is Rothschild–Stiglitz's characterization of mean-preserving
  spreads) raises `w̄`. The option value of search rises with risk because the
  worker can reject bad draws (Ljungqvist–Sargent §6.3.3).
* `mps_example`: a concrete mean-preserving spread satisfying the hypothesis.

**Deviation from the textbook.** Finitely many possible offers (Ljungqvist–
Sargent's computational setup); the textbook allows any distribution on
`[0, B]`.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

noncomputable section

namespace Econ
namespace McCall

open Finset Set

/-- A finite wage-offer distribution: offers `w i` with probabilities `p i`. -/
structure OfferDist (ι : Type*) [Fintype ι] where
  w : ι → ℝ
  p : ι → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  sum_p : ∑ i, p i = 1

variable {ι : Type*} [Fintype ι]

/-- Expectation `E[g(w)] = Σᵢ pᵢ g(wᵢ)`. -/
def OfferDist.expect (F : OfferDist ι) (g : ℝ → ℝ) : ℝ := ∑ i, F.p i * g (F.w i)

/-- The search environment: discount factor and unemployment compensation. -/
structure Env where
  β : ℝ
  c : ℝ
  hβ₀ : 0 ≤ β
  hβ₁ : β < 1

/-- The map whose fixed point is the reservation wage:
`T(x) = (1 − β) c + β E[max(w, x)]`. -/
def T (e : Env) (F : OfferDist ι) (x : ℝ) : ℝ :=
  (1 - e.β) * e.c + e.β * F.expect (fun w => max w x)

/-- `x` is a reservation wage: `x = (1 − β) c + β E[max(w, x)]`. -/
def IsReservationWage (e : Env) (F : OfferDist ι) (x : ℝ) : Prop := T e F x = x

theorem expect_const (F : OfferDist ι) (a : ℝ) : F.expect (fun _ => a) = a := by
  simp [OfferDist.expect, ← Finset.sum_mul, F.sum_p]

theorem expect_mono (F : OfferDist ι) {g h : ℝ → ℝ} (hgh : ∀ x, g x ≤ h x) :
    F.expect g ≤ F.expect h :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgh _) (F.p_nonneg i)

/-- `E[max(w, y)] − E[max(w, x)] ≤ y − x` for `x ≤ y`. -/
theorem expect_max_sub_le (F : OfferDist ι) {x y : ℝ} (hxy : x ≤ y) :
    F.expect (fun w => max w y) - F.expect (fun w => max w x) ≤ y - x := by
  have : F.expect (fun w => max w y) ≤ F.expect (fun w => max w x + (y - x)) :=
    expect_mono F fun w => by
      rcases le_total w x with h | h
      · rw [max_eq_right (h.trans hxy), max_eq_right h]; linarith
      · rw [max_eq_left h]; exact max_le (by linarith) (by linarith)
  have e : F.expect (fun w => max w x + (y - x)) = F.expect (fun w => max w x) + (y - x) := by
    simp only [OfferDist.expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, F.sum_p,
      one_mul]
  linarith

theorem expect_max_mono (F : OfferDist ι) {x y : ℝ} (hxy : x ≤ y) :
    F.expect (fun w => max w x) ≤ F.expect (fun w => max w y) :=
  expect_mono F fun _ => max_le_max le_rfl hxy

theorem continuous_T (e : Env) (F : OfferDist ι) : Continuous (T e F) := by
  unfold T OfferDist.expect
  fun_prop

/-- `T(x) − x` is strictly decreasing: `T` has slope at most `β < 1`. -/
theorem T_sub_strictAnti (e : Env) (F : OfferDist ι) : StrictAnti fun x => T e F x - x := by
  intro x y hxy
  have h := expect_max_sub_le F hxy.le
  have h2 := mul_le_mul_of_nonneg_left h e.hβ₀
  simp only [T]
  nlinarith [e.hβ₁]

theorem expect_of_forall (F : OfferDist ι) {g : ℝ → ℝ} {a : ℝ} (h : ∀ i, g (F.w i) = a) :
    F.expect g = a := by
  simp only [OfferDist.expect, h, ← Finset.sum_mul, F.sum_p, one_mul]

/-- **The textbook reservation-wage equation** (Ljungqvist–Sargent ch. 6):
`x` is a reservation wage iff `x − c = β/(1 − β) · E[(w − x)⁺]`. The cost of
searching once more (forgoing `x` now for `c`) equals the discounted expected
gain from an offer above `x`. -/
theorem isReservationWage_iff_textbook (e : Env) (F : OfferDist ι) (x : ℝ) :
    IsReservationWage e F x ↔
      x - e.c = e.β / (1 - e.β) * F.expect (fun w => max (w - x) 0) := by
  have hpt : ∀ w : ℝ, max w x = x + max (w - x) 0 := fun w => by
    rcases le_total w x with h | h
    · rw [max_eq_right h, max_eq_right (sub_nonpos.2 h), add_zero]
    · rw [max_eq_left h, max_eq_left (sub_nonneg.2 h)]; ring
  have hmax : F.expect (fun w => max w x) = x + F.expect (fun w => max (w - x) 0) := by
    simp only [OfferDist.expect, hpt, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      F.sum_p, one_mul]
  have h1 : 0 < 1 - e.β := by linarith [e.hβ₁]
  unfold IsReservationWage T
  rw [hmax, div_mul_eq_mul_div, eq_div_iff h1.ne']
  constructor <;> intro h <;> linear_combination (-1 : ℝ) * h

/-- **Existence and uniqueness of the reservation wage.** -/
theorem existsUnique_reservationWage (e : Env) (F : OfferDist ι) :
    ∃! x, IsReservationWage e F x := by
  set B := ∑ i, |F.w i|
  have hup : ∀ i, F.w i ≤ B := fun i => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |F.w i|) (fun _ _ => abs_nonneg _) (mem_univ i))
  have hlo : ∀ i, -B ≤ F.w i := fun i => by
    have := (neg_abs_le (F.w i)).trans' (neg_le_neg (Finset.single_le_sum
      (f := fun i => |F.w i|) (fun _ _ => abs_nonneg _) (mem_univ i)))
    exact this
  have h1β : 0 < 1 - e.β := by linarith [e.hβ₁]
  -- upper point: above every offer and above `c`
  set b := max B e.c + 1
  have hb : T e F b - b < 0 := by
    have hE : F.expect (fun w => max w b) = b :=
      expect_of_forall F fun i => max_eq_right ((hup i).trans (by
        have := le_max_left B e.c; linarith))
    simp only [T, hE]
    have := le_max_right B e.c
    nlinarith
  -- lower point: below every offer and below `(1 − β) c + β E[w]`
  set Ew := F.expect id
  set a := min (-B) ((1 - e.β) * e.c + e.β * Ew) - 1
  have ha : 0 < T e F a - a := by
    have hE : F.expect (fun w => max w a) = Ew := by
      unfold OfferDist.expect
      refine Finset.sum_congr rfl fun i _ => ?_
      show F.p i * max (F.w i) a = F.p i * F.w i
      rw [max_eq_left ((by have := min_le_left (-B) ((1 - e.β) * e.c + e.β * Ew); linarith :
        a ≤ -B).trans (hlo i))]
    simp only [T, hE]
    have := min_le_right (-B) ((1 - e.β) * e.c + e.β * Ew)
    linarith
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := T_sub_strictAnti e F h
    linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hab
    ((continuous_T e F).sub continuous_id).continuousOn ⟨hb.le, ha.le⟩
  refine ⟨x, sub_eq_zero.1 hx, fun y hy => ?_⟩
  have hy' : T e F y - y = 0 := sub_eq_zero.2 hy
  exact (T_sub_strictAnti e F).injective (hy'.trans hx.symm)

/-! ## The Bellman equation and the optimal policy -/

/-- The Bellman operator for the value of holding each possible offer:
`(B V)(i) = max (wᵢ / (1 − β)) (c + β Σⱼ pⱼ V j)`. -/
def bellman (e : Env) (F : OfferDist ι) (V : ι → ℝ) (i : ι) : ℝ :=
  max (F.w i / (1 - e.β)) (e.c + e.β * ∑ j, F.p j * V j)

/-- **The reservation-wage value function solves the Bellman equation:**
`V(w) = max(w, w̄)/(1 − β)`. -/
theorem bellman_reservationWage (e : Env) (F : OfferDist ι) {wbar : ℝ}
    (h : IsReservationWage e F wbar) :
    bellman e F (fun i => max (F.w i) wbar / (1 - e.β)) = fun i => max (F.w i) wbar / (1 - e.β) := by
  have h1β : 0 < 1 - e.β := by linarith [e.hβ₁]
  -- the continuation value equals `w̄ / (1 − β)`
  have hcont : e.c + e.β * ∑ j, F.p j * (max (F.w j) wbar / (1 - e.β)) = wbar / (1 - e.β) := by
    have hT : (1 - e.β) * e.c + e.β * ∑ j, F.p j * max (F.w j) wbar = wbar := h
    have : ∑ j, F.p j * (max (F.w j) wbar / (1 - e.β)) =
        (∑ j, F.p j * max (F.w j) wbar) / (1 - e.β) := by
      rw [div_eq_mul_inv, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, eq_div_iff h1β.ne']
    field_simp
    linarith
  funext i
  simp only [bellman, hcont]
  rw [max_div_div_right h1β.le]

/-- **The Bellman equation has only one solution** (the Bellman operator is a
`β`-contraction). -/
theorem bellman_unique (e : Env) (F : OfferDist ι) {V W : ι → ℝ}
    (hV : bellman e F V = V) (hW : bellman e F W = W) : V = W := by
  -- the continuation values differ by `β D` where `D = Σ pⱼ (Vⱼ − Wⱼ)`
  set D := ∑ j, F.p j * (V j - W j)
  have hpt : ∀ i, |V i - W i| ≤ e.β * |D| := by
    intro i
    rw [← congrFun hV i, ← congrFun hW i]
    simp only [bellman]
    calc |max (F.w i / (1 - e.β)) (e.c + e.β * ∑ j, F.p j * V j) -
          max (F.w i / (1 - e.β)) (e.c + e.β * ∑ j, F.p j * W j)|
        ≤ |(e.c + e.β * ∑ j, F.p j * V j) - (e.c + e.β * ∑ j, F.p j * W j)| :=
          by rw [max_comm (F.w i / (1 - e.β)), max_comm (F.w i / (1 - e.β))]
             exact abs_max_sub_max_le_abs _ _ _
      _ = e.β * |D| := by
          rw [show (e.c + e.β * ∑ j, F.p j * V j) - (e.c + e.β * ∑ j, F.p j * W j) = e.β * D by
            simp only [D, mul_sub, Finset.sum_sub_distrib]; ring,
            abs_mul, abs_of_nonneg e.hβ₀]
  have hD : |D| ≤ e.β * |D| := by
    calc |D| ≤ ∑ j, |F.p j * (V j - W j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, F.p j * |V j - W j| := Finset.sum_congr rfl fun j _ => by
          rw [abs_mul, abs_of_nonneg (F.p_nonneg j)]
      _ ≤ ∑ j, F.p j * (e.β * |D|) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpt j) (F.p_nonneg j)
      _ = e.β * |D| := by rw [← Finset.sum_mul, F.sum_p, one_mul]
  have hD0 : |D| = 0 := by
    have := abs_nonneg D
    nlinarith [e.hβ₁]
  funext i
  have := hpt i
  rw [hD0, mul_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- **The optimal policy is a reservation-wage rule:** at the (unique) solution
of the Bellman equation, accepting offer `wᵢ` is optimal (the value of
accepting is at least the value of continuing to search) iff `wᵢ ≥ w̄`. -/
theorem accept_iff (e : Env) (F : OfferDist ι) {wbar : ℝ} (h : IsReservationWage e F wbar)
    {V : ι → ℝ} (hV : bellman e F V = V) (i : ι) :
    e.c + e.β * ∑ j, F.p j * V j ≤ F.w i / (1 - e.β) ↔ wbar ≤ F.w i := by
  have h1β : 0 < 1 - e.β := by linarith [e.hβ₁]
  have hVeq := bellman_unique e F hV (bellman_reservationWage e F h)
  subst hVeq
  have hcont : e.c + e.β * ∑ j, F.p j * (max (F.w j) wbar / (1 - e.β)) = wbar / (1 - e.β) := by
    have := congrFun (bellman_reservationWage e F h) i
    have hT : (1 - e.β) * e.c + e.β * ∑ j, F.p j * max (F.w j) wbar = wbar := h
    have : ∑ j, F.p j * (max (F.w j) wbar / (1 - e.β)) =
        (∑ j, F.p j * max (F.w j) wbar) / (1 - e.β) := by
      rw [div_eq_mul_inv, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, eq_div_iff h1β.ne']
    field_simp
    linarith
  rw [hcont, div_le_div_iff_of_pos_right h1β]

/-! ## Comparative statics -/

/-- If `T₁ ≤ T₂` pointwise, the reservation wage of `T₂` is at least that of
`T₁` (both `T − id` are strictly decreasing). -/
theorem reservationWage_le_of_T_le (e₁ e₂ : Env) (F₁ : OfferDist ι) {κ : Type*} [Fintype κ]
    (F₂ : OfferDist κ) (hT : ∀ x, T e₁ F₁ x ≤ T e₂ F₂ x) {x₁ x₂ : ℝ}
    (h₁ : IsReservationWage e₁ F₁ x₁) (h₂ : IsReservationWage e₂ F₂ x₂) : x₁ ≤ x₂ := by
  by_contra hlt
  push Not at hlt
  have := T_sub_strictAnti e₂ F₂ hlt
  have := hT x₁
  unfold IsReservationWage at h₁ h₂
  linarith

/-- **More generous unemployment compensation raises the reservation
wage** (strictly). -/
theorem reservationWage_strictMono_c (F : OfferDist ι) {β c₁ c₂ : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (hc : c₁ < c₂) {x₁ x₂ : ℝ} (h₁ : IsReservationWage ⟨β, c₁, hβ₀, hβ₁⟩ F x₁)
    (h₂ : IsReservationWage ⟨β, c₂, hβ₀, hβ₁⟩ F x₂) : x₁ < x₂ := by
  by_contra hle
  push Not at hle
  have hanti := (T_sub_strictAnti ⟨β, c₂, hβ₀, hβ₁⟩ F).antitone hle
  unfold IsReservationWage T at h₁ h₂
  simp only at h₁ h₂ hanti
  unfold T at hanti
  simp only at hanti
  have := expect_max_mono F hle
  nlinarith

/-- `G` is **riskier** than `F` in the convex order: `E_F[g] ≤ E_G[g]` for every
convex `g`. For distributions with equal means this is Rothschild–Stiglitz's
characterization of "`G` is a mean-preserving spread of `F`". -/
def Riskier {κ : Type*} [Fintype κ] (F : OfferDist ι) (G : OfferDist κ) : Prop :=
  ∀ g : ℝ → ℝ, ConvexOn ℝ univ g → F.expect g ≤ G.expect g

/-- **A mean-preserving spread raises the reservation wage**
(Ljungqvist–Sargent §6.3.3): since `w ↦ max(w, x)` is convex, a riskier offer
distribution raises the option value `E[max(w, x)]` of searching. -/
theorem reservationWage_mono_riskier (e : Env) (F : OfferDist ι) {κ : Type*} [Fintype κ]
    (G : OfferDist κ) (hFG : Riskier F G) {xF xG : ℝ} (hF : IsReservationWage e F xF)
    (hG : IsReservationWage e G xG) : xF ≤ xG := by
  refine reservationWage_le_of_T_le e e F G (fun x => ?_) hF hG
  have hconv : ConvexOn ℝ univ (fun w : ℝ => max w x) :=
    convexOn_id convex_univ |>.sup (convexOn_const x convex_univ)
  have := hFG _ hconv
  simp only [T]
  nlinarith [e.hβ₀]

/-- **Non-vacuity.** The 50–50 lottery over `{0, 2}` is riskier than the sure
offer `1` (a mean-preserving spread, by Jensen's inequality). -/
theorem mps_example :
    Riskier (⟨fun _ => 1, fun _ => 1, fun _ => zero_le_one, by simp⟩ : OfferDist Unit)
      (⟨fun b => if b then 2 else 0, fun _ => 1 / 2, fun _ => by norm_num,
        by simp⟩ : OfferDist Bool) := by
  intro g hg
  simp only [OfferDist.expect, Finset.univ_unique, Finset.sum_singleton, one_mul,
    Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, ite_true, Bool.false_eq_true, ite_false]
  have := hg.2 (mem_univ (2 : ℝ)) (mem_univ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  norm_num at this ⊢
  linarith

end McCall
end Econ

end
