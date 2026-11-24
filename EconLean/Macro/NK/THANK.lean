/-
# The two-agent New Keynesian model (THANK): aggregate demand block

Bilbiie (2008), "Limited Asset Markets Participation, Monetary Policy and
(Inverted) Aggregate Demand Logic", JET; Bilbiie (2020), "The New Keynesian
Cross", JME; Bilbiie (2024), "Monetary Policy and Heterogeneity: An
Analytical Framework", REStud.

**Setting (log-linear, perfect foresight).** A fraction `λ ∈ [0, 1)` of
households are hand-to-mouth (`H`): they consume their income, which moves
with aggregate output with elasticity `χ` (the cyclicality of their income,
determined by labor-market and redistribution policy), so `c^H_t = χ y_t`.
The rest are savers (`S`) with the Euler equation
`c^S_t = c^S_{t+1} − σ (r_t − r^n_t)` (EIS `σ > 0`, real rate `r`, natural
rate `r^n`). Goods markets clear: `y_t = λ c^H_t + (1 − λ) c^S_t`. Assume
`λχ < 1`.

**Results.**
* `aggregate_IS`: aggregate output follows the THANK IS curve
  `y_t = y_{t+1} − δ σ (r_t − r^n_t)` with `δ = (1 − λ)/(1 − λχ)`.
* `impact`: if the gap closes by date `T`, `y_0 = −δσ Σ_{t<T}(r_t − r^n_t)`,
  versus `−σ Σ(r_t − r^n_t)` in RANK.
* `amplification_iff`: monetary policy is amplified relative to the
  representative agent (`δ > 1`) iff `χ > 1`, i.e. iff hand-to-mouth income
  is more cyclical than aggregate income; `δ = 1` when `λ = 0` or `χ = 1`.
* `iterate`: summing forward, `y_0 = y_T − δσ Σ_{t<T}(r_t − r^n_t)`.

**Deviations.** The derivation of `χ` from labor supply, profits and fiscal
redistribution (`χ = 1 + φ(1 − τ^D/λ)` in Bilbiie) is not formalized;
idiosyncratic risk (the transition between types, giving compounding or
discounting in the IS curve) is not modelled; perfect foresight replaces
expectations; the Phillips curve and policy rule (the supply and policy
blocks) are not included.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace THANK

open Finset

/-- Parameters. -/
structure Params where
  lam : ℝ
  χ : ℝ
  σ : ℝ
  hlam : 0 ≤ lam ∧ lam < 1
  hσ : 0 < σ
  hlχ : lam * χ < 1

namespace Params

variable (P : Params)

/-- The THANK multiplier on the interest-rate gap. -/
def δ : ℝ := (1 - P.lam) / (1 - P.lam * P.χ)

/-- A perfect-foresight equilibrium path. -/
structure IsEq (y cS cH r rn : ℕ → ℝ) : Prop where
  euler : ∀ t, cS t = cS (t + 1) - P.σ * (r t - rn t)
  htm : ∀ t, cH t = P.χ * y t
  clear : ∀ t, y t = P.lam * cH t + (1 - P.lam) * cS t

theorem one_sub_pos : 0 < 1 - P.lam * P.χ := by linarith [P.hlχ]

theorem cS_eq {y cS cH r rn : ℕ → ℝ} (h : P.IsEq y cS cH r rn) (t : ℕ) :
    cS t = (1 - P.lam * P.χ) / (1 - P.lam) * y t := by
  have h1 : 0 < 1 - P.lam := by linarith [P.hlam.2]
  have := h.clear t
  rw [h.htm t] at this
  field_simp
  linarith

/-- **The THANK aggregate IS curve.** -/
theorem aggregate_IS {y cS cH r rn : ℕ → ℝ} (h : P.IsEq y cS cH r rn) (t : ℕ) :
    y t = y (t + 1) - P.δ * P.σ * (r t - rn t) := by
  have h1 : 0 < 1 - P.lam := by linarith [P.hlam.2]
  have h2 := P.one_sub_pos
  have e := h.euler t
  rw [P.cS_eq h t, P.cS_eq h (t + 1)] at e
  unfold δ
  field_simp at e ⊢
  linarith

/-- **Amplification iff hand-to-mouth income is more cyclical.** -/
theorem amplification_iff (hlam : 0 < P.lam) : 1 < P.δ ↔ 1 < P.χ := by
  unfold δ
  rw [one_lt_div P.one_sub_pos]
  constructor <;> intro h <;> nlinarith

theorem δ_eq_one_of_rank (h : P.lam = 0) : P.δ = 1 := by
  simp [δ, h]

/-- **Iterating the IS curve forward.** -/
theorem iterate {y cS cH r rn : ℕ → ℝ} (h : P.IsEq y cS cH r rn) (T : ℕ) :
    y 0 = y T - P.δ * P.σ * ∑ t ∈ range T, (r t - rn t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, P.aggregate_IS h T, sum_range_succ]
    ring

/-- **The impact multiplier.** If the output gap is back at zero by date `T`
(`y_T = 0`), then `y_0 = −δσ Σ_{t<T}(r_t − r^n_t)`: a path of real-rate gaps
moves output by `δ` times its RANK effect. -/
theorem impact {y cS cH r rn : ℕ → ℝ} (h : P.IsEq y cS cH r rn) {T : ℕ} (hT : y T = 0) :
    y 0 = -(P.δ * P.σ * ∑ t ∈ range T, (r t - rn t)) := by
  rw [P.iterate h T, hT]; ring

/-- A THANK example with amplification (`λ = 1/2`, `χ = 3/2`, so `δ = 2`). -/
example : (⟨1 / 2, 3 / 2, 1, by norm_num, by norm_num, by norm_num⟩ : Params).δ = 2 := by
  norm_num [δ]

example : (⟨1 / 2, 3 / 2, 1, by norm_num, by norm_num, by norm_num⟩ : Params).IsEq
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => by norm_num, fun _ => by norm_num, fun _ => by norm_num⟩

/-- A RANK-equivalent example exists (`λ = 0`), so `IsEq` is not vacuous:
constant output with a zero rate gap. -/
example : (⟨0, 1, 1, by norm_num, by norm_num, by norm_num⟩ : Params).IsEq
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => by norm_num, fun _ => by norm_num, fun _ => by norm_num⟩

end Params
end THANK
end Econ

end
