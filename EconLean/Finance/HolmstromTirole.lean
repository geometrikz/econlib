/-
# Pledgeable income and credit rationing (Holmström–Tirole)

Holmström and Tirole (1997, QJE; 1998, JPE); Tirole, *The Theory of
Corporate Finance* (2006), §3.2 (fixed-investment model).

**Setting.** An entrepreneur with net worth `A ≥ 0` needs `I > A` to start a
project. The project succeeds (pays `R`) with probability `p_H` if the
entrepreneur behaves and `p_L = p_H − Δp` if she shirks, in which case she
enjoys a private benefit `B > 0`. Investors are competitive and risk
neutral (zero interest). A contract gives the entrepreneur `R_b ≥ 0` and
investors `R_l ≥ 0` on success, `R_b + R_l = R`, and nothing on failure.
It is **feasible** (`Feasible`) if it induces good behaviour,
`Δp · R_b ≥ B`, and investors break even, `p_H R_l ≥ I − A`.

**Results.**
* `feasible_iff`: a feasible contract exists iff `A ≥ Ā`, where
  `Ā = I − p_H (R − B/Δp)` (`threshold`); `p_H(R − B/Δp)` is the
  **pledgeable income**.
* `credit_rationing`: a project with positive NPV (`p_H R > I`) is not
  financed when net worth is below `Ā` (and `Ā > 0` whenever the agency rent
  `p_H B/Δp` exceeds the NPV).

**Deviations.** `p_H ≤ 1` and `p_L = p_H − Δp ≥ 0` are not imposed (the
results do not use them); the entrepreneur's participation constraint is
omitted (it holds when `p_H R ≥ I`). Fixed investment scale; limited liability built into the
contract space; the variable-scale model and liquidity are not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace HolmstromTirole

/-- The fixed-investment moral-hazard model. -/
structure Model where
  I : ℝ
  R : ℝ
  pH : ℝ
  Δp : ℝ
  B : ℝ
  hpH : 0 < pH
  hΔp : 0 < Δp
  hB : 0 < B

namespace Model

variable (M : Model)

/-- Feasible contract `(R_b, R_l)` for net worth `A`. -/
def Feasible (A Rb Rl : ℝ) : Prop :=
  0 ≤ Rb ∧ 0 ≤ Rl ∧ Rb + Rl = M.R ∧ M.B ≤ M.Δp * Rb ∧ M.I - A ≤ M.pH * Rl

/-- Pledgeable income. -/
def pledgeable : ℝ := M.pH * (M.R - M.B / M.Δp)

/-- Net-worth threshold. -/
def threshold : ℝ := M.I - M.pledgeable

/-- **Financing condition.** -/
theorem feasible_iff (A : ℝ) (hR : M.B / M.Δp ≤ M.R) :
    (∃ Rb Rl, M.Feasible A Rb Rl) ↔ M.threshold ≤ A := by
  have hΔ := M.hΔp
  constructor
  · rintro ⟨Rb, Rl, -, -, hsum, hic, hir⟩
    have : M.B / M.Δp ≤ Rb := by rw [div_le_iff₀ hΔ]; linarith
    have : Rl ≤ M.R - M.B / M.Δp := by linarith
    simp only [threshold, pledgeable]
    nlinarith [M.hpH]
  · intro hA
    refine ⟨M.B / M.Δp, M.R - M.B / M.Δp, (div_pos M.hB hΔ).le, by linarith, by ring,
      by rw [mul_div_cancel₀ _ hΔ.ne'], ?_⟩
    simp only [threshold, pledgeable] at hA
    linarith

/-- **Credit rationing.** If net worth is below the threshold, no feasible
contract exists, even when the project has positive NPV. -/
theorem credit_rationing {A : ℝ} (hA : A < M.threshold) (Rb Rl : ℝ) :
    ¬ M.Feasible A Rb Rl := by
  rintro ⟨-, -, hsum, hic, hir⟩
  have : M.B / M.Δp ≤ Rb := by rw [div_le_iff₀ M.hΔp]; linarith
  have : Rl ≤ M.R - M.B / M.Δp := by linarith
  simp only [threshold, pledgeable] at hA
  nlinarith [M.hpH]

/-- **Non-vacuity**: `I = 10, R = 20, p_H = 1, Δp = 1/2, B = 6` has NPV
`p_H R − I = 10 > 0` but threshold `Ā = 10 − (20 − 12) = 2`, so an
entrepreneur with `A = 1` is rationed. -/
example : ∃ M : Model, M.I < M.pH * M.R ∧ 1 < M.threshold :=
  ⟨⟨10, 20, 1, 1 / 2, 6, by norm_num, by norm_num, by norm_num⟩, by norm_num,
    by simp only [threshold, pledgeable]; norm_num⟩

end Model
end HolmstromTirole
end Econ

end
