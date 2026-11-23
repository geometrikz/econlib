/-
# Rules versus discretion (Kydland–Prescott, Barro–Gordon)

Kydland and Prescott (1977), JPE; Barro and Gordon (1983), JPE;
Walsh, *Monetary Theory and Policy*, ch. 7.

**Setting.** Output follows a surprise supply curve `y = ȳ + (π − πᵉ)`. The
policymaker's loss is `L = π² + λ (y − ȳ − k)²` with `λ > 0`, where `k > 0`
is the gap between its output target and potential (a distortion).
Under **discretion** the policymaker chooses `π` taking expectations `πᵉ` as
given; a **rational-expectations discretionary equilibrium** is a `π` that is
the best response to `πᵉ = π`. Under **commitment** the policymaker picks a
rule that the public anticipates, so `πᵉ = π` and output stays at `ȳ`.

**Results.**
* `bestResponse`: given `πᵉ`, the unique optimal inflation is
  `π = λ(πᵉ + k)/(1 + λ)`.
* `discretion_eq`: the unique discretionary equilibrium has the
  **inflation bias** `π = λk > 0`, with no output gain.
* `commitment_optimal`: with rational expectations, `π = 0` is the best rule.
* `commitment_better`: commitment to `π = 0` yields strictly lower loss
  (`λk²` versus `λk² + λ²k²`): time inconsistency is costly.

**Deviations.** One-shot game, no shocks (so no stabilization motive).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace BarroGordon

/-- The policymaker's loss given inflation and expected inflation (output
written relative to potential: `y − ȳ = π − πᵉ`). -/
def loss (lam k π πe : ℝ) : ℝ := π ^ 2 + lam * (π - πe - k) ^ 2

/-- **Discretion: best response to expectations.** -/
theorem bestResponse {lam k πe : ℝ} (hlam : 0 < lam) (π : ℝ) :
    loss lam k (lam * (πe + k) / (1 + lam)) πe ≤ loss lam k π πe ∧
    (loss lam k π πe ≤ loss lam k (lam * (πe + k) / (1 + lam)) πe →
      π = lam * (πe + k) / (1 + lam)) := by
  have h1 : 0 < 1 + lam := by linarith
  set πs := lam * (πe + k) / (1 + lam)
  have key : loss lam k π πe = loss lam k πs πe + (1 + lam) * (π - πs) ^ 2 := by
    simp only [loss, πs]; field_simp; ring
  refine ⟨by rw [key]; nlinarith [sq_nonneg (π - πs)], fun h => ?_⟩
  rw [key] at h
  have : (1 + lam) * (π - πs) ^ 2 = 0 := by nlinarith [sq_nonneg (π - πs)]
  have := pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left h1.ne')
  linarith

/-- A **discretionary (time-consistent) equilibrium**: inflation is a best
response to expectations, and expectations are rational. -/
def IsDiscretionEq (lam k π : ℝ) : Prop := ∀ π', loss lam k π π ≤ loss lam k π' π

/-- **Inflation bias.** The unique discretionary equilibrium is `π = λk`. -/
theorem discretion_eq {lam k : ℝ} (hlam : 0 < lam) (π : ℝ) :
    IsDiscretionEq lam k π ↔ π = lam * k := by
  constructor
  · intro h
    have := (bestResponse (k := k) (πe := π) hlam π).2 (h _)
    have h1 : 0 < 1 + lam := by linarith
    field_simp at this; linarith
  · rintro rfl π'
    have h1 : 0 < 1 + lam := by linarith
    have := (bestResponse (k := k) (πe := lam * k) hlam π').1
    have e : lam * (lam * k + k) / (1 + lam) = lam * k := by field_simp; ring
    rwa [e] at this

/-- **Commitment beats discretion.** With `k ≠ 0`, the rule `π = 0` (with
`πᵉ = 0`) gives loss `λk²`, strictly below the discretionary loss `λk² + λ²k²`. -/
theorem commitment_better {lam k : ℝ} (hlam : 0 < lam) (hk : k ≠ 0) :
    loss lam k 0 0 < loss lam k (lam * k) (lam * k) := by
  simp only [loss]
  have : 0 < lam ^ 2 * k ^ 2 := by positivity
  nlinarith

/-- **Zero inflation is the optimal commitment.** When expectations equal
the announced rule, the loss is `π² + λk²`, minimized at `π = 0`. -/
theorem commitment_optimal (lam k π : ℝ) : loss lam k 0 0 ≤ loss lam k π π := by
  simp only [loss]; nlinarith [sq_nonneg π]

end BarroGordon
end Econ

end
