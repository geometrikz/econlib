/-
# A behavioral New Keynesian model: cognitive discounting (Gabaix 2020)

Reference. X. Gabaix (2020), "A Behavioral New Keynesian Model", *AER*
110(8), Propositions 2–3 and the forward-guidance discussion of §II.

**The model** (deviations from steady state, perfect foresight, no shocks),
with forecasts formed by the cognitive-discounting belief rule of
`BeliefRule.lean`, applied with aggregate discount factors `M` (households)
and `M^f` (firms), `0 < M, M^f ≤ 1`:
* IS curve `x_t = M x_{t+1} − (i_t − π_{t+1})/σ`;
* Phillips curve `π_t = β M^f π_{t+1} + κ x_t`;
* Taylor rule `i_t = φ_π π_t + φ_x x_t`.
`σ` is the inverse elasticity of intertemporal substitution, as in
`Macro/NK/ThreeEquation.lean` (Gabaix writes the IS curve with the
elasticity). With `M = M^f = 1` this is that file's rational model
(`toRational`, `isEquilibrium_rational`).

**Results.**
* `determinate_iff` (Gabaix Proposition 3): the equilibrium is determinate
  iff `κ(φ_π − 1) + (1 − βM^f) φ_x + σ(1 − M)(1 − βM^f) > 0`.
  At `M = M^f = 1` this is the Taylor principle of the rational model
  (`determinate_iff_rational`).
* `peg_determinate_iff`: an interest-rate peg (`φ_π = φ_x = 0`) is
  determinate iff `κ < σ(1 − M)(1 − βM^f)`, i.e. with enough cognitive
  discounting the Taylor principle is not needed (Gabaix Proposition 3's
  corollary); under rational expectations a peg is never determinate
  (`peg_indeterminate_rational`).
* **Forward guidance** (partial equilibrium: IS block only, with an exogenous
  path for the *real* rate and output assumed back at steady state after the
  cut, in the spirit of McKay–Nakamura–Steinsson 2016; Gabaix's
  general-equilibrium version, where the rational response grows with the
  horizon through inflation feedback, is not formalized here): a one-period cut of
  the real rate `T` periods ahead raises output today by `M^T/σ`
  (`fg_response`). It vanishes as `T → ∞` for `M < 1`
  (`fg_vanishes`) but stays at `1/σ` under rational expectations
  (`fg_puzzle_rational`): the forward-guidance puzzle.
* **Robust vs knife-edge** (PLAN bridge B5): determinacy under an active
  rule is robust, holding for all `M, M^f ∈ (0, 1]`
  (`determinate_robust`), while the undiminished power of forward guidance is
  knife-edge: for every `M < 1` the response eventually falls below half the
  rational response `1/σ` (`fg_eventually_below_half`).
-/
module

public import EconLean.Behavioral.BeliefRule
public import EconLean.Macro.NK.ThreeEquation
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace Econ

namespace CognitiveNK

open Matrix BeliefRule

/-- Parameters of the behavioral NK model. -/
structure Model where
  σ : ℝ
  κ : ℝ
  β : ℝ
  φπ : ℝ
  φx : ℝ
  /-- households' cognitive discount -/
  M : ℝ
  /-- firms' cognitive discount -/
  Mf : ℝ
  hσ : 0 < σ
  hκ : 0 < κ
  hβ₀ : 0 < β
  hβ₁ : β < 1
  hφπ : 0 ≤ φπ
  hφx : 0 ≤ φx
  hM₀ : 0 < M
  hM₁ : M ≤ 1
  hMf₀ : 0 < Mf
  hMf₁ : Mf ≤ 1

namespace Model

variable (E : Model)

/-- An equilibrium path: forecasts of next period's output gap and inflation
are formed by cognitive discounting (`M` for households, `M^f` for firms);
the expected real rate uses undiscounted expected inflation, as in Gabaix. -/
def IsEquilibrium (x p i : ℕ → ℝ) : Prop :=
  ∀ t, x t = (Linear.cognitive E.M).forecast (x (t + 1)) (x t) - (i t - p (t + 1)) / E.σ ∧
    p t = E.β * (Linear.cognitive E.Mf).forecast (p (t + 1)) (p t) + E.κ * x t ∧
    i t = E.φπ * p t + E.φx * x t

/-- Determinacy: the only bounded equilibrium is the steady state. -/
def Determinate : Prop :=
  ∀ x p i, E.IsEquilibrium x p i → (∃ B, ∀ t, |x t| ≤ B ∧ |p t| ≤ B ∧ |i t| ≤ B) →
    ∀ t, x t = 0 ∧ p t = 0 ∧ i t = 0

/-- The forward map `(x_t, π_t) ↦ (x_{t+1}, π_{t+1})`. -/
def forward : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + E.φx / E.σ + E.κ / (E.σ * (E.β * E.Mf))) / E.M,
      (E.φπ - 1 / (E.β * E.Mf)) / (E.σ * E.M);
    -E.κ / (E.β * E.Mf), 1 / (E.β * E.Mf)]

theorem forward_det :
    E.forward.det = (E.σ + E.φx + E.κ * E.φπ) / (E.σ * E.M * (E.β * E.Mf)) := by
  have := E.hσ.ne'; have := E.hβ₀.ne'; have := E.hM₀.ne'; have := E.hMf₀.ne'
  rw [forward, det_fin_two_of]; field_simp; ring

theorem forward_trace : E.forward.trace =
    (1 + E.φx / E.σ + E.κ / (E.σ * (E.β * E.Mf))) / E.M + 1 / (E.β * E.Mf) := by
  rw [forward, trace_fin_two_of]

theorem isEquilibrium_iff (x p i : ℕ → ℝ) :
    E.IsEquilibrium x p i ↔ (∀ t, i t = E.φπ * p t + E.φx * x t) ∧
      NK.IsOrbit E.forward fun t => ![x t, p t] := by
  have hσ := E.hσ.ne'; have hβ := E.hβ₀.ne'; have hM := E.hM₀.ne'; have hMf := E.hMf₀.ne'
  have e0 : ∀ t, (E.forward *ᵥ ![x t, p t]) 0 =
      (1 + E.φx / E.σ + E.κ / (E.σ * (E.β * E.Mf))) / E.M * x t +
        (E.φπ - 1 / (E.β * E.Mf)) / (E.σ * E.M) * p t := fun t => by
    simp [NK.mulVec_zero', forward]
  have e1 : ∀ t, (E.forward *ᵥ ![x t, p t]) 1 = -E.κ / (E.β * E.Mf) * x t +
      1 / (E.β * E.Mf) * p t := fun t => by
    simp [NK.mulVec_one', forward]
  simp only [IsEquilibrium, Linear.forecast_cognitive]
  constructor
  · intro h
    refine ⟨fun t => (h t).2.2, fun t => funext fun j => ?_⟩
    obtain ⟨h1, h2, h3⟩ := h t
    have hp1 : p (t + 1) = (p t - E.κ * x t) / (E.β * E.Mf) := by
      field_simp; linarith
    have hx1 : x (t + 1) = (x t + (i t - p (t + 1)) / E.σ) / E.M := by
      rw [eq_div_iff hM, h1]; ring
    fin_cases j
    · show x (t + 1) = (E.forward *ᵥ ![x t, p t]) 0
      rw [e0, hx1, h3, hp1]; field_simp; ring
    · show p (t + 1) = (E.forward *ᵥ ![x t, p t]) 1
      rw [e1, hp1]; field_simp; ring
  · rintro ⟨hi, ho⟩ t
    have h0 : x (t + 1) = _ := (congrFun (ho t) 0).trans (e0 t)
    have h1 : p (t + 1) = _ := (congrFun (ho t) 1).trans (e1 t)
    refine ⟨?_, ?_, hi t⟩
    · rw [hi t, h0, h1]; field_simp; ring
    · rw [h1]; field_simp; ring

theorem determinate_iff_forward : E.Determinate ↔ NK.Determinate E.forward := by
  constructor
  · intro h z hz ⟨B, hB⟩ t
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
    have heq : E.IsEquilibrium (fun t => z t 0) (fun t => z t 1)
        (fun t => E.φπ * z t 1 + E.φx * z t 0) := by
      rw [isEquilibrium_iff]
      refine ⟨fun _ => rfl, fun t => ?_⟩
      have : ∀ t, ![z t 0, z t 1] = z t := fun t => by
        funext j; fin_cases j <;> rfl
      simp only [this]; exact hz t
    have hbd : ∀ t, |z t 0| ≤ B + (E.φπ + E.φx) * B ∧ |z t 1| ≤ B + (E.φπ + E.φx) * B ∧
        |E.φπ * z t 1 + E.φx * z t 0| ≤ B + (E.φπ + E.φx) * B := fun t => by
      have h0 := hB t 0; have h1 := hB t 1
      have hφ : 0 ≤ (E.φπ + E.φx) * B := mul_nonneg (add_nonneg E.hφπ E.hφx) hB0
      refine ⟨by linarith, by linarith, ?_⟩
      calc |E.φπ * z t 1 + E.φx * z t 0| ≤ |E.φπ * z t 1| + |E.φx * z t 0| := abs_add_le _ _
        _ = E.φπ * |z t 1| + E.φx * |z t 0| := by
          rw [abs_mul, abs_mul, abs_of_nonneg E.hφπ, abs_of_nonneg E.hφx]
        _ ≤ E.φπ * B + E.φx * B := by
          gcongr
          · exact E.hφπ
          · exact E.hφx
        _ ≤ _ := by nlinarith
    obtain ⟨a, b, -⟩ := h _ _ _ heq ⟨_, hbd⟩ t
    funext j; fin_cases j
    · exact a
    · exact b
  · intro h x p i heq ⟨B, hB⟩ t
    obtain ⟨hi, ho⟩ := (E.isEquilibrium_iff x p i).1 heq
    have hz := h _ ho ⟨B, fun t j => by fin_cases j <;> simp [(hB t).1, (hB t).2.1]⟩ t
    have a : x t = 0 := by simpa using congrFun hz 0
    have b : p t = 0 := by simpa using congrFun hz 1
    exact ⟨a, b, by rw [hi, a, b]; ring⟩

/-- The determinacy index `κ(φ_π − 1) + (1 − βM^f)φ_x + σ(1 − M)(1 − βM^f)`. -/
def index : ℝ :=
  E.κ * (E.φπ - 1) + (1 - E.β * E.Mf) * E.φx + E.σ * (1 - E.M) * (1 - E.β * E.Mf)

/-- **Gabaix (2020), Proposition 3.** The behavioral NK model is determinate
iff `κ(φ_π − 1) + (1 − βM^f)φ_x + σ(1 − M)(1 − βM^f) > 0`. -/
theorem determinate_iff : E.Determinate ↔ 0 < E.index := by
  have hσ := E.hσ; have hβ₀ := E.hβ₀; have hβ₁ := E.hβ₁; have hM₀ := E.hM₀
  have hM₁ := E.hM₁; have hMf₀ := E.hMf₀; have hMf₁ := E.hMf₁
  have hφπ := E.hφπ; have hφx := E.hφx; have hκ := E.hκ
  have ha₀ : 0 < E.β * E.Mf := mul_pos hβ₀ hMf₀
  have ha₁ : E.β * E.Mf < 1 := by nlinarith
  have hden : 0 < E.σ * E.M * (E.β * E.Mf) := by positivity
  have hD1 : 1 < E.forward.det := by
    rw [forward_det, one_lt_div hden]
    have : E.M * (E.β * E.Mf) < 1 := by nlinarith
    nlinarith
  have hT : 1 + E.forward.det - E.forward.trace = E.index / (E.σ * E.M * (E.β * E.Mf)) := by
    rw [forward_det, forward_trace, index]
    have := hσ.ne'; have := hM₀.ne'; have := ha₀.ne'
    field_simp; ring
  have hTpos : 0 < E.forward.trace := by rw [forward_trace]; positivity
  rw [determinate_iff_forward, NK.determinate_iff _ (by linarith), abs_of_pos hTpos]
  constructor
  · rintro ⟨-, h⟩
    have : 0 < E.index / (E.σ * E.M * (E.β * E.Mf)) := by linarith
    exact (div_pos_iff_of_pos_right hden).1 this
  · intro h
    exact ⟨hD1, by have := div_pos h hden; linarith⟩

/-- **Pegs can be determinate.** With `φ_π = φ_x = 0` the model is
determinate iff `κ < σ(1 − M)(1 − βM^f)`. -/
theorem peg_determinate_iff (hπ : E.φπ = 0) (hx : E.φx = 0) :
    E.Determinate ↔ E.κ < E.σ * (1 - E.M) * (1 - E.β * E.Mf) := by
  rw [determinate_iff, index, hπ, hx]
  constructor <;> intro h <;> linarith

/-- Under rational expectations (`M = M^f = 1`) a peg is never determinate. -/
theorem peg_indeterminate_rational (hπ : E.φπ = 0) (hx : E.φx = 0) (hM : E.M = 1)
    (hMf : E.Mf = 1) : ¬ E.Determinate := by
  rw [peg_determinate_iff E hπ hx, hM, hMf]
  have := E.hκ
  simp only [sub_self, mul_zero, zero_mul, not_lt]
  exact this.le

/-- The rational NK model with the same structural parameters. -/
def toRational : NK.Model :=
  ⟨E.σ, E.κ, E.β, E.φπ, E.φx, E.hσ, E.hκ, E.hβ₀, E.hβ₁, E.hφπ, E.hφx⟩

/-- With `M = M^f = 1` the equilibria are those of the rational model. -/
theorem isEquilibrium_rational (hM : E.M = 1) (hMf : E.Mf = 1) (x p i : ℕ → ℝ) :
    E.IsEquilibrium x p i ↔ E.toRational.IsEquilibrium x p i := by
  simp only [IsEquilibrium, NK.Model.IsEquilibrium, toRational, Linear.forecast_cognitive, hM,
    hMf, one_mul]

/-- At `M = M^f = 1` the determinacy condition is the rational model's Taylor
principle. -/
theorem determinate_iff_rational (hM : E.M = 1) (hMf : E.Mf = 1) :
    E.Determinate ↔ E.toRational.Determinate := by
  rw [determinate_iff, NK.Model.taylor_principle, index, hM, hMf]
  simp [toRational]

/-! ### Forward guidance -/

/-- The IS block with an exogenous real-rate path `r`:
`x_t = M x_{t+1} − r_t/σ`. -/
def IsISPath (M σ : ℝ) (r x : ℕ → ℝ) : Prop :=
  ∀ t, x t = (Linear.cognitive M).forecast (x (t + 1)) (x t) - r t / σ

/-- A one-period real-rate cut of size `1` at date `T`. -/
def cut (T : ℕ) (t : ℕ) : ℝ := if t = T then -1 else 0

/-- **Response to forward guidance.** If output returns to steady state after
the cut (`x_t = 0` for `t > T`), today's output rises by `M^T/σ`. -/
theorem fg_response {M σ : ℝ} {T : ℕ} {x : ℕ → ℝ} (hx : IsISPath M σ (cut T) x)
    (hend : x (T + 1) = 0) : x 0 = M ^ T / σ := by
  have key : ∀ k, k ≤ T → x (T - k) = M ^ k / σ := by
    intro k
    induction k with
    | zero =>
      intro _
      have := hx T
      simp only [Linear.forecast_cognitive, cut, ite_true, hend, mul_zero] at this
      rw [Nat.sub_zero, this, pow_zero]; ring
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have := hx (T - (k + 1))
      have hne : T - (k + 1) ≠ T := by omega
      have hs : T - (k + 1) + 1 = T - k := by omega
      simp only [Linear.forecast_cognitive, cut, hne, ite_false, zero_div, sub_zero, hs, h1]
        at this
      rw [this, pow_succ]; ring
  simpa using key T le_rfl

/-- The forward-guidance path exists: `x_t = M^{T−t}/σ` up to `T`, then `0`. -/
theorem fg_path_exists (M σ : ℝ) (T : ℕ) :
    ∃ x, IsISPath M σ (cut T) x ∧ x (T + 1) = 0 := by
  refine ⟨fun t => if t ≤ T then M ^ (T - t) / σ else 0, fun t => ?_, by simp⟩
  simp only [Linear.forecast_cognitive, cut]
  rcases lt_trichotomy t T with h | rfl | h
  · have h1 : t + 1 ≤ T := h
    have hs : T - t = T - (t + 1) + 1 := by omega
    simp only [h.le, h1, ite_true, h.ne, ite_false, zero_div, sub_zero, hs, pow_succ]
    ring
  · have h2 : ¬ t + 1 ≤ t := by omega
    simp only [le_refl, ite_true, Nat.sub_self, pow_zero, h2, ite_false]; ring
  · have h1 : ¬ t ≤ T := by omega
    have h2 : ¬ t + 1 ≤ T := by omega
    simp [h1, h2, h.ne']

/-- **Cognitive discounting removes the forward-guidance puzzle**: with
`0 ≤ M < 1`, the effect on today's output of a cut `T` periods ahead tends to
`0` as `T → ∞`. -/
theorem fg_vanishes {M σ : ℝ} (hM0 : 0 ≤ M) (hM1 : M < 1) :
    Filter.Tendsto (fun T : ℕ => M ^ T / σ) Filter.atTop (nhds 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hM0 hM1).div_const σ

/-- **The forward-guidance puzzle** under rational expectations: the effect
does not decay with the horizon. -/
theorem fg_puzzle_rational {σ : ℝ} {T : ℕ} {x : ℕ → ℝ} (hx : IsISPath 1 σ (cut T) x)
    (hend : x (T + 1) = 0) : x 0 = 1 / σ := by
  rw [fg_response hx hend, one_pow]

/-! ### Robust vs knife-edge (bridge B5) -/

/-- **Determinacy is robust.** If the rational model with structural
parameters `(σ, κ, β, φ_π, φ_x)` satisfies the Taylor condition
`κ(φ_π − 1) + (1 − β)φ_x > 0`, then *every* behavioral model with those
parameters, i.e. any `M, M^f ∈ (0, 1]` (in particular a whole neighborhood of
rational expectations), is determinate: cognitive discounting only enlarges
the determinacy region. -/
theorem determinate_robust (E : Model) (h : 0 < E.κ * (E.φπ - 1) + (1 - E.β) * E.φx) :
    E.Determinate := by
  rw [determinate_iff, index]
  have := E.hM₁; have := E.hMf₁; have := E.hMf₀; have := E.hβ₀; have := E.hβ₁
  have := E.hφx; have := E.hσ
  have hb : 1 - E.β ≤ 1 - E.β * E.Mf := by nlinarith
  have : 0 ≤ E.σ * (1 - E.M) * (1 - E.β * E.Mf) := by
    apply mul_nonneg (mul_nonneg E.hσ.le (by linarith)); nlinarith
  nlinarith

/-- **Undiminished forward guidance is knife-edge**: at `M = 1` the response is
`1/σ` at every horizon (`fg_puzzle_rational`), but for every `M ∈ [0, 1)` some
horizon has a response below half of that. -/
theorem fg_eventually_below_half {σ : ℝ} (hσ : 0 < σ) {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M < 1) :
    ∃ T : ℕ, M ^ T / σ < 1 / (2 * σ) := by
  have := (fg_vanishes hM0 hM1 (σ := σ)).eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < 1 / (2 * σ)))
  obtain ⟨T, hT⟩ := this.exists
  exact ⟨T, hT⟩

end Model

/-- **Non-vacuity.** With `σ = 1`, `κ = 1/10`, `β = 99/100`, `M = 1/2`,
`M^f = 1/2`, an interest-rate peg is determinate
(`κ = 0.1 < σ(1 − M)(1 − βM^f) ≈ 0.25`). -/
example : (⟨1, 1 / 10, 99 / 100, 0, 0, 1 / 2, 1 / 2, one_pos, by norm_num, by norm_num, by norm_num,
    le_rfl, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩ : Model).Determinate := by
  rw [Model.peg_determinate_iff _ rfl rfl]
  norm_num

end CognitiveNK

end Econ
