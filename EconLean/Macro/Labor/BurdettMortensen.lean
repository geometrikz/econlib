/-
# Equilibrium wage dispersion (Burdett–Mortensen)

Burdett and Mortensen (1998), "Wage Differentials, Employer Size, and
Unemployment", IER; Rogerson–Shimer–Wright (2005), JEL, §5;
Manning, *Monopsony in Motion*, ch. 2.

**Setting.** A unit mass of identical firms with labor productivity `p` post
wages; workers (unemployment income `b < p`) receive job offers at rate
`λ > 0` both when unemployed and employed, and jobs end at rate `δ > 0`.
An employed worker moves whenever she draws a higher offer. Offer rates on
and off the job are equal, which makes the reservation wage, and so the
lowest wage, equal to `b`. If offers are
drawn from a continuous distribution `F`, steady-state employment at a firm
posting `w` is `l(w) = δλ/(δ + λ(1 − F(w)))²` (up to the scale of the labor
force; `l`), and profit is `(p − w) l(w)`.

**Equilibrium.** The unique equilibrium offer distribution is
`F(w) = ((δ + λ)/λ)(1 − √((p − w)/(p − b)))` on `[b, w̄]` with
`w̄ = p − (p − b)(δ/(δ + λ))²`.

**Results.**
* `F_b`, `F_wbar`, `F_strictMonoOn`: `F` is a strictly increasing
  distribution function from `F(b) = 0` to `F(w̄) = 1` (no mass points).
* `b_lt_wbar`, `wbar_lt_p`: wages are **dispersed** among identical firms,
  strictly between the reservation wage and productivity.
* `equal_profit`: every wage in the support earns the same profit
  `(p − b) l(b)`: firms are indifferent.
* `no_profitable_deviation`: wages above `w̄` earn strictly less (they
  attract no more workers than `w̄`); wages below `b` hire nobody.
* `isEquilibrium`: no wage earns more than the common profit, with
  equality on the support, so `F` is an equilibrium.
* `tendsto_wbar_zero`, `tendsto_wbar_atTop`: as frictions vanish
  (`λ → ∞`) the top wage tends to the competitive wage `p`; as on-the-job
  search vanishes (`λ → 0`) it tends to `b` (the Diamond paradox).

**Deviations.** The derivation of `l(w)` from worker flows and the
uniqueness of `F` (no mass points, connected support) are not formalized. The equal-profit property and
the bounds characterize the equilibrium given the standard steady-state
employment formula.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace BurdettMortensen

open Filter Topology Set

/-- Parameters: separation and offer rates, productivity and reservation wage. -/
structure Params where
  δ : ℝ
  lam : ℝ
  p : ℝ
  b : ℝ
  hδ : 0 < δ
  hlam : 0 < lam
  hbp : b < p

/-- The top of the wage support as a function of the offer rate. -/
def wbarOf (δ lam p b : ℝ) : ℝ := p - (p - b) * (δ / (δ + lam)) ^ 2

namespace Params

variable (P : Params)

/-- The equilibrium wage-offer distribution. -/
def F (w : ℝ) : ℝ := (P.δ + P.lam) / P.lam * (1 - Real.sqrt ((P.p - w) / (P.p - P.b)))

/-- The top wage. -/
def wbar : ℝ := wbarOf P.δ P.lam P.p P.b

/-- The offer distribution as a CDF on all of `ℝ` (clamped to `[0, 1]`). -/
def Fc (w : ℝ) : ℝ := max 0 (min 1 (P.F w))

/-- Steady-state employment at a firm posting `w`: zero below the reservation
wage `b` (no worker accepts), otherwise `δλ/(δ + λ(1 − F(w)))²`. -/
def l (w : ℝ) : ℝ := if w < P.b then 0 else P.δ * P.lam / (P.δ + P.lam * (1 - P.Fc w)) ^ 2

theorem pb_pos : 0 < P.p - P.b := sub_pos.2 P.hbp

theorem ratio_mem : 0 < P.δ / (P.δ + P.lam) ∧ P.δ / (P.δ + P.lam) < 1 := by
  have := P.hδ; have := P.hlam
  exact ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith)⟩

theorem b_lt_wbar : P.b < P.wbar := by
  obtain ⟨h0, h1⟩ := P.ratio_mem
  have : (P.δ / (P.δ + P.lam)) ^ 2 < 1 := by nlinarith
  have := P.pb_pos
  simp only [wbar, wbarOf]; nlinarith

theorem wbar_lt_p : P.wbar < P.p := by
  obtain ⟨h0, -⟩ := P.ratio_mem
  have := P.pb_pos
  simp only [wbar, wbarOf]; nlinarith [pow_pos h0 2]

theorem F_b : P.F P.b = 0 := by
  simp [F, div_self P.pb_pos.ne']

/-- `√((p − w̄)/(p − b)) = δ/(δ + λ)`. -/
theorem sqrt_wbar : Real.sqrt ((P.p - P.wbar) / (P.p - P.b)) = P.δ / (P.δ + P.lam) := by
  have h : (P.p - P.wbar) / (P.p - P.b) = (P.δ / (P.δ + P.lam)) ^ 2 := by
    simp only [wbar, wbarOf]; field_simp [P.pb_pos.ne']; ring
  rw [h, Real.sqrt_sq P.ratio_mem.1.le]

theorem F_wbar : P.F P.wbar = 1 := by
  have := P.hδ; have := P.hlam
  rw [F, P.sqrt_wbar]
  field_simp
  ring

theorem F_strictMonoOn : StrictMonoOn P.F (Icc P.b P.wbar) := by
  intro w hw w' hw' hlt
  have hpb := P.pb_pos
  have hc : 0 < (P.δ + P.lam) / P.lam := by have := P.hδ; have := P.hlam; positivity
  simp only [F]
  apply mul_lt_mul_of_pos_left _ hc
  have : Real.sqrt ((P.p - w') / (P.p - P.b)) < Real.sqrt ((P.p - w) / (P.p - P.b)) := by
    apply Real.sqrt_lt_sqrt (div_nonneg (by linarith [hw'.2, P.wbar_lt_p]) hpb.le)
    exact div_lt_div_of_pos_right (by linarith) hpb
  linarith

/-- Key identity: `δ + λ(1 − F(w)) = (δ + λ)√((p − w)/(p − b))`. -/
theorem denom_eq (w : ℝ) :
    P.δ + P.lam * (1 - P.F w) = (P.δ + P.lam) * Real.sqrt ((P.p - w) / (P.p - P.b)) := by
  have := P.hlam
  simp only [F]; field_simp; ring

theorem F_mem {w : ℝ} (hw : w ∈ Icc P.b P.wbar) : P.F w ∈ Icc 0 1 := by
  have h1 := P.F_strictMonoOn.monotoneOn ⟨le_rfl, P.b_lt_wbar.le⟩ hw hw.1
  have h2 := P.F_strictMonoOn.monotoneOn hw ⟨P.b_lt_wbar.le, le_rfl⟩ hw.2
  rw [P.F_b] at h1; rw [P.F_wbar] at h2
  exact ⟨h1, h2⟩

theorem Fc_eq {w : ℝ} (hw : w ∈ Icc P.b P.wbar) : P.Fc w = P.F w := by
  obtain ⟨h0, h1⟩ := P.F_mem hw
  simp [Fc, min_eq_right h1, max_eq_right h0]

theorem one_le_F {w : ℝ} (hw : P.wbar ≤ w) : 1 ≤ P.F w := by
  have hpb := P.pb_pos
  have hc : 0 < (P.δ + P.lam) / P.lam := by have := P.hδ; have := P.hlam; positivity
  have hs : Real.sqrt ((P.p - w) / (P.p - P.b)) ≤ P.δ / (P.δ + P.lam) := by
    rw [← P.sqrt_wbar]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hpb.le)
  have := P.F_wbar
  simp only [F] at this ⊢
  have := mul_le_mul_of_nonneg_left (by linarith : 1 - P.δ / (P.δ + P.lam) ≤
    1 - Real.sqrt ((P.p - w) / (P.p - P.b))) hc.le
  rw [← P.sqrt_wbar] at this
  linarith

theorem Fc_eq_one {w : ℝ} (hw : P.wbar ≤ w) : P.Fc w = 1 := by
  simp [Fc, min_eq_left (P.one_le_F hw)]

/-- Profit on the support: `(p − w) l(w) = δλ(p − b)/(δ + λ)²`. -/
theorem profit_eq {w : ℝ} (hw : w ∈ Icc P.b P.wbar) :
    (P.p - w) * P.l w = P.δ * P.lam * (P.p - P.b) / (P.δ + P.lam) ^ 2 := by
  have hpb := P.pb_pos
  have hpw : 0 < P.p - w := by linarith [hw.2, P.wbar_lt_p]
  have hδl : 0 < P.δ + P.lam := by linarith [P.hδ, P.hlam]
  simp only [l, show ¬ w < P.b from not_lt.2 hw.1, ↓reduceIte, P.Fc_eq hw, P.denom_eq w, mul_pow,
    Real.sq_sqrt (div_nonneg hpw.le hpb.le)]
  field_simp

theorem profit_pos : 0 < (P.p - P.b) * P.l P.b := by
  rw [P.profit_eq ⟨le_rfl, P.b_lt_wbar.le⟩]
  have := P.hδ; have := P.hlam; have := P.pb_pos; positivity

/-- **Equal profits.** Every wage in `[b, w̄]` earns the same profit. -/
theorem equal_profit {w : ℝ} (hw : w ∈ Icc P.b P.wbar) :
    (P.p - w) * P.l w = (P.p - P.b) * P.l P.b := by
  rw [P.profit_eq hw, P.profit_eq ⟨le_rfl, P.b_lt_wbar.le⟩]

/-- **No profitable deviation above `w̄`.** A wage `w > w̄` attracts the same
workforce as `w̄` (all offers are already beaten) but costs more. -/
theorem no_profitable_deviation {w : ℝ} (hw : P.wbar < w) :
    (P.p - w) * P.l w < (P.p - P.b) * P.l P.b := by
  have hlw : P.l w = P.l P.wbar := by
    simp only [l, show ¬ w < P.b from not_lt.2 (P.b_lt_wbar.trans hw).le,
      show ¬ P.wbar < P.b from not_lt.2 P.b_lt_wbar.le, ↓reduceIte,
      P.Fc_eq_one hw.le, P.Fc_eq_one le_rfl]
  have hp : (P.p - P.wbar) * P.l P.wbar = (P.p - P.b) * P.l P.b :=
    P.equal_profit ⟨P.b_lt_wbar.le, le_rfl⟩
  have hpw : 0 < P.p - P.wbar := sub_pos.2 P.wbar_lt_p
  have hl : 0 < P.l P.wbar := by
    have := P.profit_pos; rw [← hp] at this; exact pos_of_mul_pos_right this hpw.le
  rw [hlw, ← hp]
  exact mul_lt_mul_of_pos_right (by linarith) hl

/-- **`F` is an equilibrium.** No wage earns more than the common profit, and
every wage in the support `[b, w̄]` attains it. -/
theorem isEquilibrium :
    (∀ w, (P.p - w) * P.l w ≤ (P.p - P.b) * P.l P.b) ∧
      ∀ w ∈ Icc P.b P.wbar, (P.p - w) * P.l w = (P.p - P.b) * P.l P.b := by
  refine ⟨fun w => ?_, fun w hw => P.equal_profit hw⟩
  by_cases hb : w < P.b
  · simp only [l, hb, ↓reduceIte, mul_zero]; exact P.profit_pos.le
  · by_cases hw : w ≤ P.wbar
    · exact (P.equal_profit ⟨not_lt.1 hb, hw⟩).le
    · exact (P.no_profitable_deviation (not_le.1 hw)).le

end Params

/-- **Competitive limit**: as the offer rate grows, the top wage tends to `p`. -/
theorem tendsto_wbar_atTop (δ p b : ℝ) :
    Tendsto (fun lam => wbarOf δ lam p b) atTop (𝓝 p) := by
  have h : Tendsto (fun lam => δ / (δ + lam)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ δ tendsto_id)
  have := ((h.pow 2).const_mul (p - b)).const_sub p
  simpa [wbarOf] using this

/-- **Diamond paradox limit**: as the offer rate vanishes, the top wage tends to `b`. -/
theorem tendsto_wbar_zero {δ p b : ℝ} (hδ : 0 < δ) :
    Tendsto (fun lam => wbarOf δ lam p b) (𝓝[>] 0) (𝓝 b) := by
  have hc : ContinuousAt (fun lam => wbarOf δ lam p b) 0 := by
    unfold wbarOf
    exact continuousAt_const.sub (continuousAt_const.mul
      ((continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; linarith)).pow 2))
  have h0 : wbarOf δ 0 p b = b := by simp [wbarOf, div_self hδ.ne']
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rwa [h0] at this
end BurdettMortensen
end Econ

end
