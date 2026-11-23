/-
# Lagos–Wright and the optimality of the Friedman rule

Lagos and Wright (2005), "A Unified Framework for Monetary Theory and Policy
Analysis", JPE; Nosal–Rocheteau, *Money, Payments, and Liquidity*, ch. 6.

**Setting.** Each period has a frictionless centralized market (CM) followed
by a decentralized market (DM) in which a buyer meets a seller with
probability `σ ∈ (0, 1]` and money is the only means of payment. With
quasi-linear CM utility, a buyer who brings real balances `z` to the DM pays
the opportunity cost `i z`, where `i ≥ 0` is the nominal interest rate
(`1 + i = (1 + π)/β`). With take-it-or-leave-it offers by buyers and a
linear production cost `c(q) = q`, the buyer gets `q = z` (up to the
efficient quantity), so her CM choice is
`max_{z > 0} Φ(z) = −i z + σ (u(z) − z)` (`buyerObj`).
Here `u` is differentiable on `(0, ∞)` with strictly decreasing marginal
utility `u'`, and the efficient quantity `q*` satisfies `u'(q*) = 1`.

**Results.**
* `isOptimal_iff`: `q > 0` solves the buyer's problem iff
  `σ (u'(q) − 1) = i` (the Lagos–Wright equilibrium condition).
* `lt_star`, `eq_star_iff`: with `i > 0` the DM quantity is below `q*`; it
  equals `q*` iff `i = 0`.
* `antitone_in_i`: higher nominal interest (inflation) lowers DM output.
* `exists_optimal`: an optimum exists for every `i ≥ 0` below the choke
  rate `σ(u'(a) − 1)` at some `a > 0` (via Darboux's theorem), so the
  conditional results are not vacuous.
* `friedman_rule`: DM surplus `σ(u(q) − q)` is maximized at `i = 0` and is
  strictly lower for every `i > 0`: the Friedman rule is optimal.

**Deviations.** Buyer take-it-or-leave-it offers (bargaining power
`θ = 1`) and linear cost: with `θ < 1` the Nash-bargaining hold-up keeps
`q < q*` even at `i = 0`, which is not formalized. The buyer is assumed to
spend all balances (`q = z` rather than `q = min(z, q*)`); this is harmless
for `i > 0`, where optimal balances are below `q*`, but it means the
non-existence of equilibrium for `i < 0` is not formalized. Stationary
equilibrium; the CM is summarized by the cost `i` of holding money.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Darboux

@[expose] public section

noncomputable section

namespace Econ
namespace LagosWright

open Set

/-- Primitives: DM matching probability and utility with derivative `du`. -/
structure Env where
  σ : ℝ
  u : ℝ → ℝ
  du : ℝ → ℝ
  qs : ℝ
  hσ : 0 < σ ∧ σ ≤ 1
  hu : ∀ q, 0 < q → HasDerivAt u (du q) q
  hdu : StrictAntiOn du (Ioi 0)
  hqs : 0 < qs
  hstar : du qs = 1

namespace Env

variable (E : Env)

/-- The buyer's CM objective given the nominal interest rate. -/
def buyerObj (i z : ℝ) : ℝ := -i * z + E.σ * (E.u z - z)

/-- Optimal real balances (= DM quantity). -/
def IsOptimal (i q : ℝ) : Prop := 0 < q ∧ ∀ z, 0 < z → E.buyerObj i z ≤ E.buyerObj i q

theorem hasDerivAt_obj (i : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (E.buyerObj i) (-i + E.σ * (E.du z - 1)) z := by
  have h := (((E.hu z hz).sub (hasDerivAt_id z)).const_mul E.σ).add
    ((hasDerivAt_id z).const_mul (-i))
  convert h using 1
  · funext w; simp [buyerObj]; ring
  · ring

/-- **The Lagos–Wright equilibrium condition.** -/
theorem isOptimal_iff (i : ℝ) {q : ℝ} (hq : 0 < q) :
    E.IsOptimal i q ↔ E.σ * (E.du q - 1) = i := by
  constructor
  · rintro ⟨-, h⟩
    have hmax : IsLocalMax (E.buyerObj i) q :=
      Filter.mem_of_superset (Ioi_mem_nhds hq) fun z hz => h z hz
    have := hmax.hasDerivAt_eq_zero (E.hasDerivAt_obj i hq)
    linarith
  · intro hfoc
    refine ⟨hq, fun z hz => ?_⟩
    rcases lt_trichotomy z q with hzq | rfl | hqz
    · -- on `(z, q)` the derivative is positive
      obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (E.buyerObj i)
        (fun w => -i + E.σ * (E.du w - 1)) hzq
        (fun w hw => (E.hasDerivAt_obj i (hz.trans_le hw.1)).continuousAt.continuousWithinAt)
        (fun w hw => E.hasDerivAt_obj i (hz.trans hw.1))
      have hlt : E.du q < E.du ξ := E.hdu (hz.trans hξ.1) hq hξ.2
      have hpos : 0 < -i + E.σ * (E.du ξ - 1) := by nlinarith [E.hσ.1]
      rw [hd, lt_div_iff₀ (by linarith)] at hpos
      linarith
    · exact le_rfl
    · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope (E.buyerObj i)
        (fun w => -i + E.σ * (E.du w - 1)) hqz
        (fun w hw => (E.hasDerivAt_obj i (hq.trans_le hw.1)).continuousAt.continuousWithinAt)
        (fun w hw => E.hasDerivAt_obj i (hq.trans hw.1))
      have hlt : E.du ξ < E.du q := E.hdu hq (hq.trans hξ.1) hξ.1
      have hneg : -i + E.σ * (E.du ξ - 1) < 0 := by nlinarith [E.hσ.1]
      rw [hd, div_lt_iff₀ (by linarith)] at hneg
      linarith

/-- With `i > 0`, DM output is below the efficient quantity. -/
theorem lt_star {i q : ℝ} (hi : 0 < i) (hq : 0 < q) (h : E.IsOptimal i q) : q < E.qs := by
  rw [E.isOptimal_iff i hq] at h
  by_contra hle; push Not at hle
  have : E.du q ≤ E.du E.qs := E.hdu.antitoneOn E.hqs hq hle
  rw [E.hstar] at this
  nlinarith [E.hσ.1]

/-- DM output is efficient iff `i = 0`. -/
theorem eq_star_iff {i q : ℝ} (hq : 0 < q) (h : E.IsOptimal i q) : q = E.qs ↔ i = 0 := by
  rw [E.isOptimal_iff i hq] at h
  constructor
  · rintro rfl; rw [← h, E.hstar]; ring
  · rintro rfl
    have h1 : E.du q = 1 := by
      have := E.hσ.1
      have : E.du q - 1 = 0 := by
        rcases mul_eq_zero.1 h with h | h
        · linarith
        · exact h
      linarith
    exact E.hdu.injOn hq E.hqs (h1.trans E.hstar.symm)

/-- **Inflation lowers DM output.** -/
theorem antitone_in_i {i₁ i₂ q₁ q₂ : ℝ} (hi : i₁ < i₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (h₁ : E.IsOptimal i₁ q₁) (h₂ : E.IsOptimal i₂ q₂) : q₂ < q₁ := by
  rw [E.isOptimal_iff _ hq₁] at h₁
  rw [E.isOptimal_iff _ hq₂] at h₂
  by_contra hle; push Not at hle
  have : E.du q₂ ≤ E.du q₁ := E.hdu.antitoneOn hq₁ hq₂ hle
  nlinarith [E.hσ.1]

/-- DM surplus `u(q) − q` is strictly increasing below `q*`. -/
theorem surplus_lt {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (h12 : q₁ < q₂) (h2 : q₂ ≤ E.qs) :
    E.u q₁ - q₁ < E.u q₂ - q₂ := by
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope E.u E.du h12
    (fun w hw => (E.hu w (hq₁.trans_le hw.1)).continuousAt.continuousWithinAt)
    (fun w hw => E.hu w (hq₁.trans hw.1))
  have : 1 < E.du ξ := by
    rw [← E.hstar]; exact E.hdu (hq₁.trans hξ.1) E.hqs (hξ.2.trans_le h2)
  rw [hd, lt_div_iff₀ (by linarith)] at this
  linarith

/-- **Existence.** For `0 ≤ i < σ(u'(a) − 1)` with `a > 0` (implied by an
Inada condition), the buyer's problem has an interior solution. -/
theorem exists_optimal {i a : ℝ} (hi : 0 ≤ i) (ha : 0 < a) (hai : i < E.σ * (E.du a - 1)) :
    ∃ q, E.IsOptimal i q := by
  have hσ := E.hσ.1
  rcases hi.eq_or_lt with rfl | hi
  · exact ⟨E.qs, (E.isOptimal_iff 0 E.hqs).2 (by rw [E.hstar]; ring)⟩
  have hm : 1 + i / E.σ < E.du a := by
    have : i / E.σ < E.du a - 1 := by rw [div_lt_iff₀ hσ]; linarith
    linarith
  have hm1 : E.du E.qs < 1 + i / E.σ := by rw [E.hstar]; have := div_pos hi hσ; linarith
  have haq : a ≤ E.qs := by
    by_contra h; push Not at h
    have := E.hdu E.hqs ha h; linarith
  obtain ⟨q, hq, hdq⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt haq
    (fun x hx => (E.hu x (ha.trans_le hx.1)).hasDerivWithinAt) hm hm1
  refine ⟨q, (E.isOptimal_iff i (ha.trans hq.1)).2 ?_⟩
  rw [hdq]; field_simp; ring

/-- **The Friedman rule is optimal.** For every `i > 0`, equilibrium DM
surplus is strictly below the surplus at `i = 0`, where `q = q*`. -/
theorem friedman_rule {i q : ℝ} (hi : 0 < i) (hq : 0 < q) (h : E.IsOptimal i q) :
    E.σ * (E.u q - q) < E.σ * (E.u E.qs - E.qs) ∧ E.IsOptimal 0 E.qs := by
  refine ⟨mul_lt_mul_of_pos_left (E.surplus_lt hq (E.lt_star hi hq h) le_rfl) E.hσ.1, ?_⟩
  rw [E.isOptimal_iff 0 E.hqs, E.hstar]; ring

end Env
end LagosWright
end Econ

end
