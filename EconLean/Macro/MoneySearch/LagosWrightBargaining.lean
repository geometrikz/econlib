/-
# Lagos–Wright with bargaining: hold-up and the Friedman rule

Lagos and Wright (2005), JPE, §3–4; Aruoba, Rocheteau and Waller (2007),
"Bargaining and the Value of Money", JME; Nosal–Rocheteau, *Money, Payments,
and Liquidity*, ch. 6.

**Setting.** As in `Econ.LagosWright` (DM matching probability `σ`, DM
utility `u` with strictly decreasing marginal utility `u'`, linear seller
cost, efficient quantity `q*` with `u'(q*) = 1`), but the buyer has
bargaining power `θ ∈ (0, 1)`.
* **Nash bargaining** (LW): to obtain `q` the buyer must bring real balances
  `g(q) = (θ q u'(q) + (1 − θ) u(q))/(θ u'(q) + 1 − θ)` (`nashPay`, the
  generalized Nash solution when the buyer's balances bind).
* **Proportional (Kalai) bargaining** (ARW): `g(q) = θ q + (1 − θ) u(q)`
  (`kalaiPay`): the buyer gets the share `θ` of the match surplus.
In both cases the buyer chooses `q` to maximize
`−i g(q) + σ (u(q) − g(q))` (`nashObj`, `kalaiObj`), `i ≥ 0` the nominal
rate.

**Results.**
* `hasDerivAt_nashPay`: at `q*`,
  `g'(q*) = 1 + θ(1 − θ) u''(q*) (q* − u(q*))`.
* `holdup`: if `0 < θ < 1`, `u''(q*) < 0` and the match has positive
  surplus at `q*` (`u(q*) > q*`), then `g'(q*) > 1`, so for every `i ≥ 0`
  the buyer's objective is strictly decreasing at `q*`: `q*` is **not**
  chosen, even at the Friedman rule `i = 0`. Nash bargaining creates a
  hold-up problem that monetary policy cannot undo. `nashObj_deriv_star`
  gives the negative slope explicitly, and `holdup_lt` the global form: any
  best choice on the bargaining domain `(0, q*]` is strictly below `q*`.
  (`u(q*) > q*` is what `u(0) = 0` would deliver; `Env` does not impose it.)
* `nashPay_one`: with `θ = 1` the payment is `q`, the baseline model.
* `kalai_foc`, `kalai_friedman`, `kalai_lt_star`: with Kalai bargaining an
  interior optimum satisfies `σθ(u'(q) − 1) = i(θ + (1 − θ)u'(q))`; the
  Friedman rule `i = 0` delivers `q*` (and `q*` is attained there,
  `kalai_friedman_attained`), and `i > 0` gives `q < q*`.
* `kalai_mono_theta`: for `i > 0`, lower buyer bargaining power means
  strictly lower DM output: the inflation tax is amplified by the hold-up.

**Deviations.** The Nash payment formula is taken from LW (the solution of
the bargaining problem when balances bind) rather than derived, and is only
the bargaining outcome for `q ≤ q*` (above `q*` the buyer's balances no
longer bind); the objectives are nevertheless defined on all of `ℝ`, and the
global hold-up statement `holdup_lt` is restricted to `(0, q*]`. Existence of
an optimum is not proved here.
-/
module

public import EconLean.Macro.MoneySearch.LagosWright
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

noncomputable section

namespace Econ
namespace LagosWright
namespace Env

open Set Filter Topology

variable (E : Env)

/-- The Nash-bargaining payment for quantity `q`. -/
def nashPay (θ q : ℝ) : ℝ := (θ * q * E.du q + (1 - θ) * E.u q) / (θ * E.du q + 1 - θ)

/-- The buyer's objective under Nash bargaining. -/
def nashObj (θ i q : ℝ) : ℝ := -i * E.nashPay θ q + E.σ * (E.u q - E.nashPay θ q)

theorem nashPay_one {q : ℝ} (hq : E.du q ≠ 0) : E.nashPay 1 q = q := by
  simp only [nashPay]
  rw [show (1 : ℝ) * E.du q + 1 - 1 = E.du q by ring,
    show 1 * q * E.du q + (1 - 1) * E.u q = q * E.du q by ring, mul_div_assoc, div_self hq, mul_one]

theorem nashPay_star (θ : ℝ) : E.nashPay θ E.qs = θ * E.qs + (1 - θ) * E.u E.qs := by
  simp [nashPay, E.hstar]

/-- **The slope of the payment at `q*`.** -/
theorem hasDerivAt_nashPay (θ : ℝ) {d2 : ℝ} (hd2 : HasDerivAt E.du d2 E.qs) :
    HasDerivAt (E.nashPay θ) (1 + θ * (1 - θ) * d2 * (E.qs - E.u E.qs)) E.qs := by
  have hu := E.hu E.qs E.hqs
  have hN : HasDerivAt (fun q => θ * q * E.du q + (1 - θ) * E.u q)
      (θ * (1 * E.du E.qs + E.qs * d2) + (1 - θ) * E.du E.qs) E.qs := by
    have := (((hasDerivAt_id E.qs).mul hd2).const_mul θ).add (hu.const_mul (1 - θ))
    convert this using 1
    · funext q; simp only [Pi.add_apply, Pi.mul_apply, id]; ring
    · rfl
  have hD : HasDerivAt (fun q => θ * E.du q + 1 - θ) (θ * d2) E.qs := by
    have := ((hd2.const_mul θ).add_const 1).sub_const θ
    simpa using this
  have hD0 : θ * E.du E.qs + 1 - θ ≠ 0 := by rw [E.hstar]; norm_num
  have := hN.div hD hD0
  convert this using 1
  · rfl
  rw [E.hstar]
  field_simp
  ring

/-- **The buyer's marginal value at `q*` is negative** under Nash bargaining
with `0 < θ < 1`, for every `i ≥ 0`. -/
theorem nashObj_deriv_star {θ i d2 : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hi : 0 ≤ i)
    (hd2 : HasDerivAt E.du d2 E.qs) (hd2neg : d2 < 0) (hsurplus : E.qs < E.u E.qs) :
    ∃ D, HasDerivAt (E.nashObj θ i) D E.qs ∧ D < 0 := by
  set g' := 1 + θ * (1 - θ) * d2 * (E.qs - E.u E.qs)
  have hg' : 1 < g' := by
    have : 0 < θ * (1 - θ) * d2 * (E.qs - E.u E.qs) := by
      have h1 : 0 < θ * (1 - θ) := mul_pos hθ (by linarith)
      have h2 : 0 < d2 * (E.qs - E.u E.qs) := mul_pos_of_neg_of_neg hd2neg (by linarith)
      have := mul_pos h1 h2; linarith [this]
    simp only [g']; linarith
  have hD : HasDerivAt (E.nashObj θ i) (-i * g' + E.σ * (E.du E.qs - g')) E.qs := by
    have hp := E.hasDerivAt_nashPay θ hd2
    have := (hp.const_mul (-i)).add (((E.hu E.qs E.hqs).sub hp).const_mul E.σ)
    convert this using 1
    funext q; simp [nashObj]
  refine ⟨_, hD, ?_⟩
  rw [E.hstar]
  have hσ := E.hσ.1
  nlinarith

/-- **The hold-up problem**: with `0 < θ < 1`, `q*` is not chosen for any
`i ≥ 0` (not even a local maximum of the buyer's objective). -/
theorem holdup {θ i d2 : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hi : 0 ≤ i)
    (hd2 : HasDerivAt E.du d2 E.qs) (hd2neg : d2 < 0) (hsurplus : E.qs < E.u E.qs) :
    ¬ IsLocalMax (E.nashObj θ i) E.qs := by
  intro hmax
  obtain ⟨D, hD, hneg⟩ := E.nashObj_deriv_star hθ hθ1 hi hd2 hd2neg hsurplus
  linarith [hmax.hasDerivAt_eq_zero hD]

/-- **Hold-up, global form**: any best choice of the buyer on the bargaining
domain `(0, q*]` lies strictly below `q*`, even at the Friedman rule. -/
theorem holdup_lt {θ i d2 q : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hi : 0 ≤ i)
    (hd2 : HasDerivAt E.du d2 E.qs) (hd2neg : d2 < 0) (hsurplus : E.qs < E.u E.qs)
    (hq : q ∈ Ioc 0 E.qs) (hbest : ∀ z ∈ Ioc 0 E.qs, E.nashObj θ i z ≤ E.nashObj θ i q) :
    q < E.qs := by
  rcases hq.2.lt_or_eq with h | h
  · exact h
  exfalso
  subst h
  obtain ⟨D, hD, hneg⟩ := E.nashObj_deriv_star hθ hθ1 hi hd2 hd2neg hsurplus
  have hT := hD.tendsto_slope_zero_left
  have hev1 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t⁻¹ • (E.nashObj θ i (E.qs + t) - E.nashObj θ i E.qs) < 0 :=
    hT (Iio_mem_nhds hneg)
  have hev2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), -E.qs < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [E.hqs]))
  have hev3 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have hz : E.qs + t ∈ Ioc 0 E.qs := ⟨by linarith, by linarith⟩
  have hle := hbest _ hz
  rw [smul_eq_mul] at h1
  have : 0 < E.nashObj θ i (E.qs + t) - E.nashObj θ i E.qs := by
    by_contra hc
    push Not at hc
    have : 0 ≤ t⁻¹ * (E.nashObj θ i (E.qs + t) - E.nashObj θ i E.qs) :=
      mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 h3.le) hc
    linarith
  linarith

/-! ### Proportional (Kalai) bargaining -/

/-- The Kalai payment. -/
def kalaiPay (θ q : ℝ) : ℝ := θ * q + (1 - θ) * E.u q

/-- The buyer's objective under Kalai bargaining. -/
def kalaiObj (θ i q : ℝ) : ℝ := -i * E.kalaiPay θ q + E.σ * (E.u q - E.kalaiPay θ q)

/-- **The Kalai first-order condition.** -/
theorem kalai_foc {θ i q : ℝ} (hq : 0 < q) (hmax : IsLocalMax (E.kalaiObj θ i) q) :
    E.σ * θ * (E.du q - 1) = i * (θ + (1 - θ) * E.du q) := by
  have hu := E.hu q hq
  have hp : HasDerivAt (E.kalaiPay θ) (θ + (1 - θ) * E.du q) q := by
    have := ((hasDerivAt_id q).const_mul θ).add (hu.const_mul (1 - θ))
    convert this using 1
    · funext w; simp [kalaiPay]
    · simp
  have hD : HasDerivAt (E.kalaiObj θ i)
      (-i * (θ + (1 - θ) * E.du q) + E.σ * (E.du q - (θ + (1 - θ) * E.du q))) q :=
    (hp.const_mul (-i)).add ((hu.sub hp).const_mul E.σ)
  have h0 := hmax.hasDerivAt_eq_zero hD
  linarith

/-- **Kalai: the Friedman rule is efficient.** -/
theorem kalai_friedman {θ q : ℝ} (hθ : 0 < θ) (hq : 0 < q)
    (hmax : IsLocalMax (E.kalaiObj θ 0) q) : q = E.qs := by
  have h := E.kalai_foc hq hmax
  simp only [zero_mul] at h
  have h1 : E.du q = 1 := by
    have := mul_pos E.hσ.1 hθ
    rcases mul_eq_zero.1 (show E.σ * θ * (E.du q - 1) = 0 by linarith) with h' | h'
    · linarith
    · linarith
  exact E.hdu.injOn hq E.hqs (h1.trans E.hstar.symm)

/-- **Kalai: the Friedman rule attains `q*`.** At `i = 0`, `q*` maximizes the
buyer's objective over all positive quantities, so `kalai_friedman` is not
vacuous. -/
theorem kalai_friedman_attained {θ : ℝ} (hθ : 0 < θ) {z : ℝ} (hz : 0 < z) :
    E.kalaiObj θ 0 z ≤ E.kalaiObj θ 0 E.qs := by
  have hopt : E.IsOptimal 0 E.qs := (E.isOptimal_iff 0 E.hqs).2 (by rw [E.hstar]; ring)
  have h := hopt.2 z hz
  have e : ∀ w, E.kalaiObj θ 0 w = θ * E.buyerObj 0 w := fun w => by
    simp only [kalaiObj, kalaiPay, buyerObj]; ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_left h hθ.le

/-- **Kalai: positive nominal rates depress output.** -/
theorem kalai_lt_star {θ i q : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hi : 0 < i) (hq : 0 < q)
    (hdu : 0 ≤ E.du q) (hmax : IsLocalMax (E.kalaiObj θ i) q) : q < E.qs := by
  have h := E.kalai_foc hq hmax
  have hgt : 1 < E.du q := by
    by_contra hle
    push Not at hle
    have h1 : E.σ * θ * (E.du q - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos E.hσ.1 hθ).le (by linarith)
    have h2 : 0 < i * (θ + (1 - θ) * E.du q) :=
      mul_pos hi (by nlinarith)
    linarith
  by_contra hge
  push Not at hge
  have : E.du q ≤ E.du E.qs := E.hdu.antitoneOn E.hqs hq hge
  rw [E.hstar] at this
  linarith

/-- **Kalai: more buyer bargaining power, more output** (for `i > 0`). -/
theorem kalai_mono_theta {θ₁ θ₂ i q₁ q₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ : θ₁ < θ₂) (_hθ₂ : θ₂ ≤ 1)
    (hi : 0 < i) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hdu₁ : 0 ≤ E.du q₁)
    (h₁ : IsLocalMax (E.kalaiObj θ₁ i) q₁) (h₂ : IsLocalMax (E.kalaiObj θ₂ i) q₂) : q₁ < q₂ := by
  have f₁ := E.kalai_foc hq₁ h₁
  have f₂ := E.kalai_foc hq₂ h₂
  set S := E.σ + i
  have hS : 0 < S := by have := E.hσ.1; simp only [S]; linarith
  -- `u'(q_k) ((σ + i) θ_k − i) = θ_k (σ + i)`
  have e₁ : E.du q₁ * (S * θ₁ - i) = θ₁ * S := by simp only [S]; linarith
  have e₂ : E.du q₂ * (S * θ₂ - i) = θ₂ * S := by simp only [S]; linarith
  have hD₁ : 0 < S * θ₁ - i := by
    rcases hdu₁.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at e₁; nlinarith
    · by_contra hc; push Not at hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos h0.le hc]
  have hD₂ : 0 < S * θ₂ - i := by nlinarith
  have hlt : E.du q₂ < E.du q₁ := by
    have k₁ : E.du q₁ = θ₁ * S / (S * θ₁ - i) := by rw [eq_div_iff hD₁.ne']; exact e₁
    have k₂ : E.du q₂ = θ₂ * S / (S * θ₂ - i) := by rw [eq_div_iff hD₂.ne']; exact e₂
    rw [k₁, k₂, div_lt_div_iff₀ hD₂ hD₁]
    nlinarith [mul_pos hS hi]
  by_contra hge
  push Not at hge
  have := E.hdu.antitoneOn hq₂ hq₁ hge
  linarith

end Env
end LagosWright
end Econ

end
