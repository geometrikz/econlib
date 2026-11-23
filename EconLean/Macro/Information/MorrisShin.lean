/-
# The social value of public information (Morris–Shin)

Morris and Shin (2002), "Social Value of Public Information", AER;
Angeletos and Pavan (2007), Econometrica, §2; Veldkamp, *Information Choice
in Macroeconomics and Finance*, ch. 4.

**Setting (beauty contest).** A continuum of agents choose `a_i` to minimize
`(1 − r)(a_i − θ)² + r (L_i − L̄)`, so the best response is
`a_i = (1 − r) E_i θ + r E_i ā` with coordination weight `r ∈ [0, 1)`. Under
a diffuse prior, each agent sees a public signal `y = θ + η` (precision
`α > 0`) and a private signal `x_i = θ + ε_i` (precision `β > 0`), so
`E_i θ = (α y + β x_i)/(α + β)`. In a linear equilibrium
`a_i = κ y + (1 − κ) x_i`, so `E_i ā = κ y + (1 − κ) E_i θ`, and the best
response has `y`-coefficient `(1 − rκ) α/(α + β) + rκ` (`IsEqWeight`).
Social welfare is `−E(a_i − θ)² = −(κ²/α + (1 − κ)²/β)` (`loss`).

**Results.**
* `isEqWeight_iff`: the unique linear equilibrium weight on public information is
  `κ = α/(α + β(1 − r))`, which exceeds the Bayesian weight `α/(α + β)` when
  `r > 0`: agents over-react to public signals.
* `loss_eq`: equilibrium loss is `(α + β(1 − r)²)/(α + β(1 − r))²`.
* `hasDerivAt_loss_alpha`, `public_info_harmful_iff`: more precise public
  information **raises** the loss (positive derivative) iff
  `α < β(1 − r)(2r − 1)`; `harmful_region_nonempty` gives an instance;
  `public_info_helps_of_le_half`: with `r ≤ 1/2` it always helps.
* `hasDerivAt_loss_beta`, `private_info_helps`: more precise private
  information always lowers the loss.

**Deviations.** Diffuse prior; linear equilibria; the uniqueness of the
linear equilibrium among all equilibria (Morris–Shin, via iterated
expectations) is not formalized. The welfare criterion is MS's
`−E(a − θ)²`, which ignores the coordination term (the Angeletos–Pavan
efficient-use benchmark is not formalized).
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace MorrisShin

/-- The equilibrium condition on the weight `κ` on the public signal. -/
def IsEqWeight (r α β κ : ℝ) : Prop := (1 - r * κ) * (α / (α + β)) + r * κ = κ

/-- The equilibrium weight on public information. -/
def kappa (r α β : ℝ) : ℝ := α / (α + β * (1 - r))

/-- Expected squared distance from the fundamental, for weight `κ`. -/
def lossOf (α β κ : ℝ) : ℝ := κ ^ 2 / α + (1 - κ) ^ 2 / β

/-- Equilibrium loss as a function of the precisions. -/
def loss (r α β : ℝ) : ℝ := (α + β * (1 - r) ^ 2) / (α + β * (1 - r)) ^ 2

variable {r α β : ℝ}

theorem isEqWeight_iff (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) (κ : ℝ) :
    IsEqWeight r α β κ ↔ κ = kappa r α β := by
  have h1 : 0 < α + β := by linarith
  have h2 : 0 < α + β * (1 - r) := by nlinarith
  unfold IsEqWeight kappa
  rw [eq_div_iff h2.ne']
  constructor
  · intro h
    field_simp at h
    linear_combination -h
  · intro h
    field_simp
    linear_combination -h

/-- Over-reaction to public information. -/
theorem kappa_ge_bayes (hr : 0 ≤ r) (hr1 : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    α / (α + β) ≤ kappa r α β := by
  unfold kappa
  apply div_le_div_of_nonneg_left hα.le (by nlinarith) (by nlinarith)

theorem loss_eq (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    lossOf α β (kappa r α β) = loss r α β := by
  have h2 : 0 < α + β * (1 - r) := by nlinarith
  unfold lossOf kappa loss
  field_simp
  ring

theorem hasDerivAt_loss_alpha (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    HasDerivAt (fun a => loss r a β)
      ((β * (1 - r) * (2 * r - 1) - α) / (α + β * (1 - r)) ^ 3) α := by
  have h2 : α + β * (1 - r) ≠ 0 := by nlinarith
  have hn : HasDerivAt (fun a => a + β * (1 - r) ^ 2) 1 α :=
    HasDerivAt.add_const _ (hasDerivAt_id α)
  have hd : HasDerivAt (fun a => (a + β * (1 - r)) ^ 2) (2 * (α + β * (1 - r))) α := by
    simpa using (HasDerivAt.add_const (β * (1 - r)) (hasDerivAt_id α)).fun_pow 2
  convert hn.div hd (pow_ne_zero 2 h2) using 1
  · rfl
  · field_simp
    ring

/-- **Public information can be harmful.** The equilibrium loss is locally
increasing in public precision iff `α < β(1 − r)(2r − 1)`. -/
theorem public_info_harmful_iff (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    0 < deriv (fun a => loss r a β) α ↔ α < β * (1 - r) * (2 * r - 1) := by
  have h2 : 0 < α + β * (1 - r) := by nlinarith
  rw [(hasDerivAt_loss_alpha hr hα hβ).deriv, div_pos_iff_of_pos_right (pow_pos h2 3), sub_pos]

/-- With weak coordination motives (`r ≤ 1/2`), public information always helps. -/
theorem public_info_helps_of_le_half (hr : r ≤ 1 / 2) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun a => loss r a β) α < 0 := by
  have h2 : 0 < α + β * (1 - r) := by nlinarith
  rw [(hasDerivAt_loss_alpha (by linarith) hα hβ).deriv]
  apply div_neg_of_neg_of_pos _ (pow_pos h2 3)
  have : 0 ≤ β * (1 - r) * (1 - 2 * r) := mul_nonneg (mul_nonneg hβ.le (by linarith)) (by linarith)
  linarith

/-- The harmful region is non-empty: with `r = 3/4`, `α = 1`, `β = 16`. -/
theorem harmful_region_nonempty : 0 < deriv (fun a => loss (3 / 4) a 16) 1 := by
  rw [public_info_harmful_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem hasDerivAt_loss_beta (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    HasDerivAt (fun b => loss r α b)
      ((1 - r) * (α * (-1 - r) - β * (1 - r) ^ 2) / (α + β * (1 - r)) ^ 3) β := by
  have h2 : α + β * (1 - r) ≠ 0 := by nlinarith
  have hn : HasDerivAt (fun b => α + b * (1 - r) ^ 2) ((1 - r) ^ 2) β := by
    simpa using HasDerivAt.const_add α ((hasDerivAt_id β).mul_const ((1 - r) ^ 2))
  have hd : HasDerivAt (fun b => (α + b * (1 - r)) ^ 2) (2 * (α + β * (1 - r)) * (1 - r)) β := by
    simpa using (HasDerivAt.const_add α ((hasDerivAt_id β).mul_const (1 - r))).fun_pow 2
  convert hn.div hd (pow_ne_zero 2 h2) using 1
  · rfl
  · field_simp
    ring

/-- **Private information always helps.** -/
theorem private_info_helps (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) (hr0 : -1 < r) :
    deriv (fun b => loss r α b) β < 0 := by
  have h2 : 0 < α + β * (1 - r) := by nlinarith
  rw [(hasDerivAt_loss_beta hr hα hβ).deriv]
  apply div_neg_of_neg_of_pos _ (pow_pos h2 3)
  apply mul_neg_of_pos_of_neg (by linarith)
  nlinarith [sq_nonneg (1 - r)]

end MorrisShin
end Econ

end
