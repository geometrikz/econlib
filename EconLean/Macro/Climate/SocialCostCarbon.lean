/-
# The social cost of carbon in closed form (DICE-style IAM, GHKT 2014)

Nordhaus (DICE); Golosov, Hassler, Krusell and Tsyvinski (2014), "Optimal
Taxes on Fossil Fuel in General Equilibrium", Econometrica, Proposition 1.

**Setting.** Log utility, discount factor `β ∈ (0,1)`, and a constant saving
rate `s ∈ [0,1)` (optimal in GHKT's economy), so consumption is
`Cⱼ = (1 − s) Yⱼ`. Output is net of climate damages, exponential in the
atmospheric carbon stock: `Yⱼ = e^{−γ Sⱼ} Ỹⱼ`, `γ > 0`, with `Ỹⱼ > 0` the
damage-free output path (any path of TFP, population, energy, ...).
**Carbon cycle.** A unit of carbon emitted at date `0` leaves
`rⱼ = φ_L + (1 − φ_L) φ₀ (1 − φ)^j` units in the atmosphere `j` periods later
(`remain`): a share `φ_L` stays forever, a share `(1 − φ_L) φ₀` decays at rate
`φ`, the rest is absorbed at once.

Emitting `e` extra units at date `0` changes date-`j` output to
`Ỹⱼ e^{−γ (Sⱼ + rⱼ e)}` (`outputAfter`) and welfare by
`ΔW(e) = Σⱼ βʲ (log Cⱼ(e) − log Cⱼ(0))` (`welfareChange`). The **social cost
of carbon** (`scc`) is the marginal welfare loss converted into date-0
consumption units at the marginal utility `1/C₀`: `SCC = −C₀ · ΔW'(0)`.

**Results.**
* `hasDerivAt_welfareChange` and `scc_eq`:
  `SCC = γ C₀ (φ_L/(1 − β) + (1 − φ_L) φ₀ / (1 − β(1 − φ)))`
  (the GHKT Prop. 1 kernel): the SCC is proportional to current consumption
  with a factor that depends only on preferences, damages and the carbon
  cycle, not on
  future TFP, population or technology (`Ỹ`, `s` and `S` drop out).
* `kernel_mono`: SCC/Y₀ rises with patience `β`.
* `kernel_unbounded`: if some carbon stays forever (`φ_L > 0`), SCC/Y₀ is
  unbounded as `β → 1` (the Stern–Nordhaus discounting debate).

**Deviations.** Damage-free output `Ỹ` is exogenous: extra emissions do not
feed back through capital accumulation. GHKT state the SCC as `γ Y₀ · kernel`;
in their economy (Cobb–Douglas, full depreciation, `s = αβ`) the capital
feedback multiplies output losses by `1/(1 − s)`, which turns `γ C₀` into
`γ Y₀`. That feedback is not modelled here, so the SCC is stated in
consumption units. Utility is logarithmic and the saving rate constant; damages are exponential in the carbon stock;
temperature dynamics are folded into the damage function. The optimal
carbon tax equals the SCC by the standard Pigouvian argument, which is not
formalized here.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

noncomputable section

namespace Econ
namespace Climate

open Real

/-- Carbon-cycle parameters and damage elasticity. -/
structure Params where
  β : ℝ
  γ : ℝ
  φL : ℝ
  φ0 : ℝ
  φ : ℝ
  s : ℝ
  hβ0 : 0 < β
  hβ1 : β < 1
  hγ : 0 < γ
  hφL : 0 ≤ φL ∧ φL ≤ 1
  hφ0 : 0 ≤ φ0 ∧ φ0 ≤ 1
  hφ : 0 < φ ∧ φ ≤ 1
  hs : 0 ≤ s ∧ s < 1

namespace Params

variable (P : Params)

/-- Share of a unit of emissions still in the atmosphere after `j` periods. -/
def remain (j : ℕ) : ℝ := P.φL + (1 - P.φL) * P.φ0 * (1 - P.φ) ^ j

/-- Date-`j` output after `e` extra units are emitted at date 0. -/
def outputAfter (Ytilde S : ℕ → ℝ) (e : ℝ) (j : ℕ) : ℝ :=
  exp (-P.γ * (S j + P.remain j * e)) * Ytilde j

/-- Welfare change from `e` extra units of date-0 emissions. -/
def welfareChange (Ytilde S : ℕ → ℝ) (e : ℝ) : ℝ :=
  ∑' j : ℕ, P.β ^ j * (log ((1 - P.s) * P.outputAfter Ytilde S e j) -
    log ((1 - P.s) * P.outputAfter Ytilde S 0 j))

/-- The discounted carbon kernel `Σⱼ βʲ rⱼ` in closed form. -/
def kernel : ℝ := P.φL / (1 - P.β) + (1 - P.φL) * P.φ0 / (1 - P.β * (1 - P.φ))

theorem summable_kernel : Summable fun j : ℕ => P.β ^ j * P.remain j := by
  have h1 : Summable fun j : ℕ => P.β ^ j :=
    summable_geometric_of_lt_one P.hβ0.le P.hβ1
  have hq0 : 0 ≤ P.β * (1 - P.φ) := mul_nonneg P.hβ0.le (by linarith [P.hφ.2])
  have hq1 : P.β * (1 - P.φ) < 1 := by nlinarith [P.hφ.1, P.hφ.2, P.hβ1, P.hβ0]
  have h2 : Summable fun j : ℕ => (P.β * (1 - P.φ)) ^ j := summable_geometric_of_lt_one hq0 hq1
  convert (h1.mul_left P.φL).add (h2.mul_left ((1 - P.φL) * P.φ0)) using 1
  funext j; simp only [remain, mul_pow]; ring

theorem tsum_kernel : ∑' j : ℕ, P.β ^ j * P.remain j = P.kernel := by
  have hq0 : 0 ≤ P.β * (1 - P.φ) := mul_nonneg P.hβ0.le (by linarith [P.hφ.2])
  have hq1 : P.β * (1 - P.φ) < 1 := by nlinarith [P.hφ.1, P.hφ.2, P.hβ1, P.hβ0]
  have h1 : Summable fun j : ℕ => P.β ^ j := summable_geometric_of_lt_one P.hβ0.le P.hβ1
  have h2 : Summable fun j : ℕ => (P.β * (1 - P.φ)) ^ j := summable_geometric_of_lt_one hq0 hq1
  have e : (fun j : ℕ => P.β ^ j * P.remain j) =
      fun j => P.φL * P.β ^ j + (1 - P.φL) * P.φ0 * (P.β * (1 - P.φ)) ^ j := by
    funext j; simp only [remain, mul_pow]; ring
  rw [e, (h1.mul_left _).tsum_add (h2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one P.hβ0.le P.hβ1, tsum_geometric_of_lt_one hq0 hq1, kernel]
  ring

/-- Welfare is linear in extra emissions: `ΔW(e) = −γ e Σⱼ βʲ rⱼ`. -/
theorem welfareChange_eq {Ytilde S : ℕ → ℝ} (hY : ∀ j, 0 < Ytilde j) (e : ℝ) :
    P.welfareChange Ytilde S e = -P.γ * e * P.kernel := by
  have hs : 0 < 1 - P.s := by linarith [P.hs.2]
  have term : ∀ j, P.β ^ j * (log ((1 - P.s) * P.outputAfter Ytilde S e j) -
      log ((1 - P.s) * P.outputAfter Ytilde S 0 j)) = -P.γ * e * (P.β ^ j * P.remain j) := by
    intro j
    have h1 : 0 < exp (-P.γ * (S j + P.remain j * e)) * Ytilde j := mul_pos (exp_pos _) (hY j)
    have h0 : 0 < exp (-P.γ * (S j + P.remain j * 0)) * Ytilde j := mul_pos (exp_pos _) (hY j)
    simp only [outputAfter]
    rw [log_mul hs.ne' h1.ne', log_mul hs.ne' h0.ne', log_mul (exp_pos _).ne' (hY j).ne',
      log_mul (exp_pos _).ne' (hY j).ne', log_exp, log_exp]
    ring
  simp only [welfareChange, term, tsum_mul_left, tsum_kernel]

theorem hasDerivAt_welfareChange {Ytilde S : ℕ → ℝ} (hY : ∀ j, 0 < Ytilde j) :
    HasDerivAt (P.welfareChange Ytilde S) (-P.γ * P.kernel) 0 := by
  have : P.welfareChange Ytilde S = fun e => (-P.γ * P.kernel) * e := by
    funext e; rw [P.welfareChange_eq hY]; ring
  rw [this]
  simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-P.γ * P.kernel)

/-- The social cost of carbon at date 0, in date-0 consumption units: the
marginal welfare loss times `C₀ = (1 − s) Y₀` (the inverse marginal utility). -/
def scc (Ytilde S : ℕ → ℝ) : ℝ :=
  -((1 - P.s) * P.outputAfter Ytilde S 0 0) * deriv (P.welfareChange Ytilde S) 0

/-- **GHKT formula.** `SCC = γ C₀ (φ_L/(1−β) + (1−φ_L)φ₀/(1−β(1−φ)))`. -/
theorem scc_eq {Ytilde S : ℕ → ℝ} (hY : ∀ j, 0 < Ytilde j) :
    P.scc Ytilde S = P.γ * ((1 - P.s) * P.outputAfter Ytilde S 0 0) * P.kernel := by
  rw [scc, (P.hasDerivAt_welfareChange hY).deriv]; ring

theorem kernel_pos_of (hL : 0 < P.φL) : 0 < P.kernel := by
  have h1 : 0 < P.φL / (1 - P.β) := div_pos hL (by linarith [P.hβ1])
  have hq1 : P.β * (1 - P.φ) < 1 := by nlinarith [P.hφ.1, P.hφ.2, P.hβ1, P.hβ0]
  have h2 : 0 ≤ (1 - P.φL) * P.φ0 / (1 - P.β * (1 - P.φ)) :=
    div_nonneg (mul_nonneg (by linarith [P.hφL.2]) P.hφ0.1) (by linarith)
  unfold kernel; linarith

/-- **More patience, higher SCC.** For two economies differing only in
`β ≤ β'`, the carbon kernel (and hence SCC/Y₀) is weakly higher under `β'`. -/
theorem kernel_mono (P Q : Params) (hL : P.φL = Q.φL) (h0 : P.φ0 = Q.φ0) (hφ : P.φ = Q.φ)
    (hβ : P.β ≤ Q.β) : P.kernel ≤ Q.kernel := by
  unfold kernel
  rw [hL, h0, hφ]
  have hQ := Q.hβ1
  have hφ1 := Q.hφ.2
  have hφ0 := Q.hφ.1
  have hqP : 0 < 1 - P.β * (1 - Q.φ) := by nlinarith [P.hβ0]
  have hqQ : 0 < 1 - Q.β * (1 - Q.φ) := by nlinarith [Q.hβ0]
  gcongr
  · exact Q.hφL.1
  · exact mul_nonneg (by linarith [Q.hφL.2]) Q.hφ0.1

/-- **Discounting dominates.** If a share `φ_L > 0` of carbon stays in the
atmosphere forever, SCC/Y₀ can be made arbitrarily large by taking `β`
close enough to one. -/
theorem kernel_unbounded (P : Params) (hL : 0 < P.φL) (M : ℝ) :
    ∃ Q : Params, Q.φL = P.φL ∧ Q.φ0 = P.φ0 ∧ Q.φ = P.φ ∧ Q.γ = P.γ ∧ M < Q.kernel := by
  -- choose `β = 1 − ε` with `φ_L/ε > M`
  set ε := min (1 / 2) (P.φL / (|M| + 1)) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hL (by positivity))
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  let Q : Params := { P with β := 1 - ε, hβ0 := by linarith, hβ1 := by linarith }
  refine ⟨Q, rfl, rfl, rfl, rfl, ?_⟩
  have hk : Q.φL / (1 - Q.β) ≤ Q.kernel := by
    have hq1 : Q.β * (1 - Q.φ) < 1 := by nlinarith [Q.hφ.1, Q.hφ.2, Q.hβ1, Q.hβ0]
    have : 0 ≤ (1 - Q.φL) * Q.φ0 / (1 - Q.β * (1 - Q.φ)) :=
      div_nonneg (mul_nonneg (by linarith [Q.hφL.2]) Q.hφ0.1) (by linarith)
    unfold kernel; linarith
  refine lt_of_lt_of_le ?_ hk
  show M < P.φL / (1 - (1 - ε))
  rw [sub_sub_cancel, lt_div_iff₀ hε0]
  have : ε ≤ P.φL / (|M| + 1) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith [le_abs_self M, abs_nonneg M]

end Params
end Climate
end Econ

end
