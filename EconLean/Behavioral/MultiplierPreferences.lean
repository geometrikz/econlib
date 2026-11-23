/-
# Multiplier preferences and robust control (Hansen–Sargent)

References. L. P. Hansen and T. J. Sargent (2001), "Robust Control and Model
Uncertainty", *AER P&P* 91(2), and *Robustness* (2008), ch. 1–2;
F. Maccheroni, M. Marinacci and A. Rustichini (2006), "Ambiguity Aversion,
Robustness, and the Variational Representation of Preferences",
*Econometrica* 74(6), §4.2 (multiplier preferences are variational).

A decision maker has a reference model `p` (full support on finitely many
states) but fears it is misspecified. She evaluates a utility profile `u` by
the worst case over alternative models `q`, penalized by relative entropy:

    min_q  Σ_s q(s) u(s) + θ KL(q ‖ p),     θ > 0.

**Results.**
* `isLeast_mult` (robust control = risk-sensitive utility): the minimum is
  attained and equals `mult θ p u = −θ log Σ_s p(s) e^{−u(s)/θ}`; the
  minimizer is the exponentially tilted model `worstCase`
  (`mult_eq_at_worstCase`), and it is unique (`eq_worstCase_of_min`). So
  multiplier preferences are variational preferences with cost `θ KL`.
* `worstCase_tilts`: the worst case overweights bad states: the likelihood
  ratio `q*(s)/p(s)` is strictly decreasing in `u(s)`.
* `min_le_mult`, `mult_le_eu`: `min u ≤ mult ≤ E_p u`: robustness lowers the
  value below expected utility under the reference model.
* `mult_add_const`, `mult_mono`, `mult_concave`: translation invariance,
  monotonicity and concavity (preference for hedging), the MMR axioms in
  utility space.
-/
module

public import EconLean.Behavioral.RationalInattention

@[expose] public section

noncomputable section

namespace Econ

namespace Multiplier

open Finset Real Logit RationalInattention

variable {S : Type*} [Fintype S] [Nonempty S]

/-- The multiplier (risk-sensitive) value `−θ log Σ_s p(s) e^{−u(s)/θ}`. -/
def mult (θ : ℝ) (p u : S → ℝ) : ℝ := -θ * log (Z θ p (fun s => -u s))

/-- The penalized expected utility of model `q`. -/
def penalized (θ : ℝ) (p u q : S → ℝ) : ℝ := ∑ s, q s * u s + θ * kl q p

/-- The worst-case model: exponential tilting of `p` toward low utility. -/
def worstCase (θ : ℝ) (p u : S → ℝ) : S → ℝ := generalizedLogit θ p (fun s => -u s)

variable {θ : ℝ} {p u : S → ℝ}

omit [Nonempty S] in
theorem penalized_eq_neg_objective (q : S → ℝ) :
    penalized θ p u q = -objective θ p (fun s => -u s) q := by
  simp only [penalized, objective, kl, mul_neg, sum_neg_distrib]; ring

theorem worstCase_isProb (hp : ∀ s, 0 < p s) : IsProb (worstCase θ p u) :=
  generalizedLogit_isProb hp

/-- The worst case attains the multiplier value. -/
theorem mult_eq_at_worstCase (hθ : 0 < θ) (hp : ∀ s, 0 < p s) :
    penalized θ p u (worstCase θ p u) = mult θ p u := by
  rw [penalized_eq_neg_objective, worstCase, objective_generalizedLogit hθ hp, mult]; ring

/-- Every model's penalized value is at least the multiplier value. -/
theorem mult_le_penalized (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {q : S → ℝ} (hq : IsProb q) :
    mult θ p u ≤ penalized θ p u q := by
  rw [← mult_eq_at_worstCase hθ hp, penalized_eq_neg_objective, penalized_eq_neg_objective]
  exact neg_le_neg (generalizedLogit_optimal hθ hp hq)

/-- **Robust control = risk-sensitive utility** (Hansen–Sargent): the
minimum of penalized expected utility over models is the multiplier value. -/
theorem isLeast_mult (hθ : 0 < θ) (hp : ∀ s, 0 < p s) :
    IsLeast {x | ∃ q, IsProb q ∧ x = penalized θ p u q} (mult θ p u) :=
  ⟨⟨_, worstCase_isProb hp, (mult_eq_at_worstCase hθ hp).symm⟩,
    fun _ ⟨_, hq, hx⟩ => hx ▸ mult_le_penalized hθ hp hq⟩

/-- The worst-case model is the unique minimizer. -/
theorem eq_worstCase_of_min (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {q : S → ℝ} (hq : IsProb q)
    (hmin : penalized θ p u q ≤ mult θ p u) : q = worstCase θ p u := by
  apply eq_generalizedLogit_of_optimal hθ hp hq
  rw [← mult_eq_at_worstCase hθ hp, penalized_eq_neg_objective, penalized_eq_neg_objective]
    at hmin
  unfold worstCase at hmin
  linarith

/-- **The worst case overweights bad states.** -/
theorem worstCase_tilts (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {s s' : S} (h : u s < u s') :
    worstCase θ p u s' / p s' < worstCase θ p u s / p s := by
  have hZ := Z_pos (lam := θ) (v := fun s => -u s) hp
  have key : ∀ t, worstCase θ p u t / p t = exp (-u t / θ) / Z θ p (fun s => -u s) :=
    fun t => by
      simp only [worstCase, generalizedLogit]
      have := (hp t).ne'
      field_simp
  rw [key, key]
  apply div_lt_div_of_pos_right _ hZ
  exact exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hθ)

/-- **Robustness lowers the value below reference expected utility.** -/
theorem mult_le_eu (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (hp1 : ∑ s, p s = 1) :
    mult θ p u ≤ ∑ s, p s * u s := by
  have h := mult_le_penalized (u := u) hθ hp ⟨fun s => (hp s).le, hp1⟩
  have hkl : kl p p = 0 := by simp [kl]
  rw [penalized, hkl, mul_zero, add_zero] at h
  exact h

/-- The multiplier value is at least the worst outcome. -/
theorem min_le_mult (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (hp1 : ∑ s, p s = 1) {m : ℝ}
    (hm : ∀ s, m ≤ u s) : m ≤ mult θ p u := by
  rw [← mult_eq_at_worstCase hθ hp, penalized]
  have hq := worstCase_isProb (θ := θ) (u := u) hp
  have hkl := kl_nonneg hq ⟨fun s => (hp s).le, hp1⟩ hp
  have : m ≤ ∑ s, worstCase θ p u s * u s := by
    calc m = ∑ s, worstCase θ p u s * m := by rw [← sum_mul, hq.2, one_mul]
      _ ≤ _ := sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hm s) (hq.1 s)
  nlinarith

/-- **Translation invariance.** -/
theorem mult_add_const (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (k : ℝ) :
    mult θ p (fun s => u s + k) = mult θ p u + k := by
  have hZ := Z_pos (lam := θ) (v := fun s => -u s) hp
  have e : Z θ p (fun s => -(u s + k)) = Z θ p (fun s => -u s) * exp (-k / θ) := by
    simp only [Z, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_assoc, ← exp_add]; congr 2; ring
  simp only [mult]
  rw [e, log_mul hZ.ne' (exp_pos _).ne', log_exp]
  field_simp; ring

/-- **Monotonicity.** -/
theorem mult_mono (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {u' : S → ℝ} (h : ∀ s, u s ≤ u' s) :
    mult θ p u ≤ mult θ p u' := by
  have hZ := Z_pos (lam := θ) (v := fun s => -u' s) hp
  have hle : Z θ p (fun s => -u' s) ≤ Z θ p (fun s => -u s) :=
    sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [h s]) hθ.le)) (hp s).le
  simp only [mult]
  have := log_le_log hZ hle
  nlinarith

/-- **Concavity (preference for hedging).** -/
theorem mult_concave (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (u' : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    α * mult θ p u + (1 - α) * mult θ p u' ≤ mult θ p (fun s => α * u s + (1 - α) * u' s) := by
  set w := fun s => α * u s + (1 - α) * u' s
  set q := worstCase θ p w
  have hq := worstCase_isProb (θ := θ) (u := w) hp
  have h1 := mult_le_penalized (u := u) hθ hp hq
  have h2 := mult_le_penalized (u := u') hθ hp hq
  have hs : ∑ s, q s * w s = α * ∑ s, q s * u s + (1 - α) * ∑ s, q s * u' s := by
    simp only [w, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  have e : penalized θ p w q = α * penalized θ p u q + (1 - α) * penalized θ p u' q := by
    unfold penalized; rw [hs]; ring
  rw [← mult_eq_at_worstCase (u := w) hθ hp, e]
  have := mul_le_mul_of_nonneg_left h1 hα0
  have := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - α)
  linarith

end Multiplier

end Econ
