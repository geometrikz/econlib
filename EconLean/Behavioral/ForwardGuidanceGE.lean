/-
# Forward guidance in general equilibrium (Gabaix 2020)

Reference. X. Gabaix (2020), "A Behavioral New Keynesian Model", *AER*
110(8), §III.B (forward guidance) and Proposition 4; D. Del Negro,
M. Giannoni and C. Patterson (2012) and A. McKay, E. Nakamura and
J. Steinsson (2016) on the forward-guidance puzzle.

**Experiment.** The model of `CognitiveDiscounting.lean` (IS curve with
cognitive discount `M`, Phillips curve with `M^f`), but with the *nominal*
rate set exogenously: it is held at steady state except for a one-period cut
of size `1` at date `T` (`cut T`), and the economy is back at steady state
after the cut (`x_{T+1} = π_{T+1} = 0`). Unlike the partial-equilibrium
version in `CognitiveDiscounting.lean`, inflation feeds back into the real
rate through the Phillips curve.

Solving backward, `(x_T, π_T) = (1/σ, κ/σ)` and
`(x_t, π_t) = B (x_{t+1}, π_{t+1})` before the cut, with the nonnegative
matrix `B = [[M, 1/σ], [κM, βM^f + κ/σ]]`. So today's response is
`(x_0, π_0) = B^T (1/σ, κ/σ)` (`response`, `fgGE_response`, `fgGE_path_exists`).

**Results.**
* `fgGE_puzzle`: under rational expectations (`M = M^f = 1`) the output
  response grows without bound in the horizon `T`
  (`x_0 ≥ 1/σ + T κ/σ²`): promises about the far future are *more* powerful,
  the forward-guidance puzzle in general equilibrium.
* `fgGE_vanishes`: if cognitive discounting is strong enough that an
  interest-rate peg is determinate, `κ < σ(1 − M)(1 − βM^f)`
  (`CognitiveNK.Model.peg_determinate_iff`), the output and inflation responses
  tend to `0` as `T → ∞`, and conversely (`fgGE_vanishes_iff`,
  `fgGE_vanishes_iff_determinate`): forward guidance fades iff the peg is
  determinate. The proof exhibits a positive vector `w` with
  `B w ≤ ρ w`, `ρ < 1`, so `B` is a contraction in a weighted sup norm
  (`iter_tendsto_zero`).
-/
module

public import EconLean.Behavioral.CognitiveDiscounting
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace Econ

namespace CognitiveNK

open BeliefRule Filter Topology

/-! ### Nonnegative 2×2 recursions -/

/-- Iterates of the linear map `(a, b) ↦ (B₁₁a + B₁₂b, B₂₁a + B₂₂b)` from `v`. -/
def iter (B₁₁ B₁₂ B₂₁ B₂₂ : ℝ) (v : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => v
  | n + 1 => (B₁₁ * (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1 + B₁₂ * (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2,
      B₂₁ * (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1 + B₂₂ * (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2)

/-- **Weighted contraction.** If all entries and the initial vector are
nonnegative and some `w = (1, w₂)`, `w₂ > 0`, satisfies `B w ≤ ρ w` with
`ρ < 1`, the iterates go to zero; quantitatively both coordinates are
bounded by multiples of `ρⁿ`. -/
theorem iter_bound {B₁₁ B₁₂ B₂₁ B₂₂ w ρ c : ℝ} {v : ℝ × ℝ} (h₁₁ : 0 ≤ B₁₁) (h₁₂ : 0 ≤ B₁₂)
    (h₂₁ : 0 ≤ B₂₁) (h₂₂ : 0 ≤ B₂₂) (hr1 : B₁₁ + B₁₂ * w ≤ ρ)
    (hr2 : B₂₁ + B₂₂ * w ≤ ρ * w) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2) (hc1 : v.1 ≤ c)
    (hc2 : v.2 ≤ w * c) (n : ℕ) :
    0 ≤ (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1 ∧ 0 ≤ (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2 ∧
      (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1 ≤ c * ρ ^ n ∧
      (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2 ≤ w * (c * ρ ^ n) := by
  induction n with
  | zero => simpa using ⟨hv1, hv2, hc1, hc2⟩
  | succ n ih =>
    obtain ⟨a0, b0, a1, b1⟩ := ih
    set a := (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1
    set b := (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2
    have hK : 0 ≤ c * ρ ^ n := a0.trans a1
    simp only [iter]
    refine ⟨by positivity, by positivity, ?_, ?_⟩
    · calc B₁₁ * a + B₁₂ * b ≤ B₁₁ * (c * ρ ^ n) + B₁₂ * (w * (c * ρ ^ n)) := by gcongr
        _ = (B₁₁ + B₁₂ * w) * (c * ρ ^ n) := by ring
        _ ≤ ρ * (c * ρ ^ n) := by gcongr
        _ = c * ρ ^ (n + 1) := by ring
    · calc B₂₁ * a + B₂₂ * b ≤ B₂₁ * (c * ρ ^ n) + B₂₂ * (w * (c * ρ ^ n)) := by gcongr
        _ = (B₂₁ + B₂₂ * w) * (c * ρ ^ n) := by ring
        _ ≤ ρ * w * (c * ρ ^ n) := by gcongr
        _ = w * (c * ρ ^ (n + 1)) := by ring

theorem iter_tendsto_zero {B₁₁ B₁₂ B₂₁ B₂₂ w ρ : ℝ} {v : ℝ × ℝ} (h₁₁ : 0 ≤ B₁₁)
    (h₁₂ : 0 ≤ B₁₂) (h₂₁ : 0 ≤ B₂₁) (h₂₂ : 0 ≤ B₂₂) (hw : 0 < w) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hr1 : B₁₁ + B₁₂ * w ≤ ρ) (hr2 : B₂₁ + B₂₂ * w ≤ ρ * w) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2) :
    Tendsto (fun n => (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1) atTop (𝓝 0) ∧
      Tendsto (fun n => (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2) atTop (𝓝 0) := by
  set c := v.1 + v.2 / w
  have hc1 : v.1 ≤ c := by have : 0 ≤ v.2 / w := by positivity
                           linarith
  have hc2 : v.2 ≤ w * c := by
    have : w * c = w * v.1 + v.2 := by simp only [c]; field_simp
    rw [this]; nlinarith
  have hb := iter_bound h₁₁ h₁₂ h₂₁ h₂₂ hr1 hr2 hv1 hv2 hc1 hc2
  have hg : Tendsto (fun n : ℕ => c * ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul c
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun n => (hb n).1) (fun n => (hb n).2.2.1), ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hg.const_mul w) (fun n => (hb n).2.1) (fun n => (hb n).2.2.2)

/-! ### The forward-guidance experiment -/

namespace Model

variable (E : Model)

/-- An equilibrium path under an exogenous nominal-rate path `i`. -/
def IsRatePath (i x p : ℕ → ℝ) : Prop :=
  ∀ t, x t = (Linear.cognitive E.M).forecast (x (t + 1)) (x t) - (i t - p (t + 1)) / E.σ ∧
    p t = E.β * (Linear.cognitive E.Mf).forecast (p (t + 1)) (p t) + E.κ * x t

/-- The backward map `B` iterated `T` times from `(1/σ, κ/σ)`: the responses of
`(x_0, π_0)` to a unit nominal-rate cut `T` periods ahead. -/
def response (T : ℕ) : ℝ × ℝ :=
  iter E.M (1 / E.σ) (E.κ * E.M) (E.β * E.Mf + E.κ / E.σ) (1 / E.σ, E.κ / E.σ) T

/-- **The general-equilibrium response.** If the nominal rate is cut by `1`
at date `T` only and the economy is at steady state from `T + 1` on, today's
output gap and inflation are `response T`. -/
theorem fgGE_response {T : ℕ} {x p : ℕ → ℝ} (h : E.IsRatePath (cut T) x p)
    (hx : x (T + 1) = 0) (hp : p (T + 1) = 0) : (x 0, p 0) = E.response T := by
  have hσ := E.hσ.ne'
  have key : ∀ k, k ≤ T → (x (T - k), p (T - k)) = E.response k := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨h1, h2⟩ := h T
      simp only [Linear.forecast_cognitive, cut, ite_true, hx, hp, mul_zero, zero_add,
        zero_sub] at h1 h2
      rw [Nat.sub_zero, response, iter, Prod.mk.injEq, h2, h1]
      constructor <;> field_simp
      all_goals ring
    | succ k ih =>
      intro hk
      have e := ih (by omega)
      rw [Prod.mk.injEq] at e
      obtain ⟨h1, h2⟩ := h (T - (k + 1))
      have hne : T - (k + 1) ≠ T := by omega
      have hs : T - (k + 1) + 1 = T - k := by omega
      simp only [Linear.forecast_cognitive, cut, hne, ite_false, zero_sub, hs, e.1, e.2]
        at h1 h2
      rw [response, iter, ← response, Prod.mk.injEq, h2, h1]
      constructor <;> field_simp <;> ring
  simpa using key T le_rfl

/-- The experiment has an equilibrium path (so `fgGE_response` is not vacuous). -/
theorem fgGE_path_exists (T : ℕ) :
    ∃ x p : ℕ → ℝ, E.IsRatePath (cut T) x p ∧ x (T + 1) = 0 ∧ p (T + 1) = 0 := by
  have hσ := E.hσ.ne'
  refine ⟨fun t => if t ≤ T then (E.response (T - t)).1 else 0,
    fun t => if t ≤ T then (E.response (T - t)).2 else 0, fun t => ?_, by simp, by simp⟩
  simp only [Linear.forecast_cognitive, cut]
  rcases lt_trichotomy t T with ht | rfl | ht
  · have h1 : t + 1 ≤ T := ht
    have hs : T - t = T - (t + 1) + 1 := by omega
    simp only [ht.le, h1, ite_true, ht.ne, ite_false, hs, response, iter]
    constructor <;> field_simp <;> ring
  · have h2 : ¬ t + 1 ≤ t := by omega
    simp only [le_refl, ite_true, Nat.sub_self, h2, ite_false, response, iter]
    constructor <;> field_simp <;> ring
  · have h1 : ¬ t ≤ T := by omega
    have h2 : ¬ t + 1 ≤ T := by omega
    simp [h1, h2, ht.ne']

/-- **The forward-guidance puzzle in general equilibrium.** Under rational
expectations (`M = M^f = 1`) a peg is indeterminate
(`peg_indeterminate_rational`), and the return-to-steady-state path is the
McKay–Nakamura–Steinsson selection among the bounded solutions. Along it, the
output response to a cut `T` periods ahead
is at least `1/σ + Tκ/σ²`, so it grows without bound in the horizon. -/
theorem fgGE_puzzle_bound (hM : E.M = 1) (hMf : E.Mf = 1) (T : ℕ) :
    1 / E.σ + T * (E.κ / E.σ ^ 2) ≤ (E.response T).1 ∧ E.κ / E.σ ≤ (E.response T).2 := by
  have hσ := E.hσ; have hκ := E.hκ; have hβ := E.hβ₀
  induction T with
  | zero => simp [response, iter]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have ha : 0 ≤ (E.response n).1 := le_trans (by positivity) h1
    have hb : 0 ≤ (E.response n).2 := le_trans (by positivity) h2
    have e : E.response (n + 1) = (E.M * (E.response n).1 + 1 / E.σ * (E.response n).2,
        E.κ * E.M * (E.response n).1 + (E.β * E.Mf + E.κ / E.σ) * (E.response n).2) := rfl
    rw [e, hM, hMf]
    simp only [one_mul, mul_one]
    constructor
    · have : E.κ / E.σ ^ 2 ≤ 1 / E.σ * (E.response n).2 := by
        calc E.κ / E.σ ^ 2 = 1 / E.σ * (E.κ / E.σ) := by field_simp
          _ ≤ _ := by gcongr
      push_cast; linarith
    · have : E.κ / E.σ ≤ E.κ * (E.response n).1 := by
        calc E.κ / E.σ = E.κ * (1 / E.σ) := by ring
          _ ≤ _ := by gcongr; linarith [show (0 : ℝ) ≤ n * (E.κ / E.σ ^ 2) by positivity]
      have : 0 ≤ (E.β + E.κ / E.σ) * (E.response n).2 := by positivity
      linarith

theorem fgGE_puzzle (hM : E.M = 1) (hMf : E.Mf = 1) :
    Tendsto (fun T => (E.response T).1) atTop atTop := by
  have hσ := E.hσ; have hκ := E.hκ
  refine tendsto_atTop_mono (fun T => (E.fgGE_puzzle_bound hM hMf T).1) ?_
  apply tendsto_atTop_add_const_left
  exact Tendsto.atTop_mul_const (by positivity) tendsto_natCast_atTop_atTop

/-- **Cognitive discounting resolves the puzzle.** If an interest-rate peg is
determinate, `κ < σ(1 − M)(1 − βM^f)`, the output and inflation responses to
a cut `T` periods ahead vanish as `T → ∞`. -/
theorem fgGE_vanishes (h : E.κ < E.σ * (1 - E.M) * (1 - E.β * E.Mf)) :
    Tendsto (fun T => (E.response T).1) atTop (𝓝 0) ∧
      Tendsto (fun T => (E.response T).2) atTop (𝓝 0) := by
  have hσ := E.hσ; have hκ := E.hκ; have hβ₀ := E.hβ₀; have hβ₁ := E.hβ₁
  have hM₀ := E.hM₀; have hMf₀ := E.hMf₀; have hMf₁ := E.hMf₁
  have hM1 : 0 < 1 - E.M := by
    by_contra hc
    have : E.σ * (1 - E.M) * (1 - E.β * E.Mf) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hσ.le (by linarith))
      nlinarith
    linarith
  have ha : 0 < 1 - E.β * E.Mf := by nlinarith
  -- d = 1 − βM^f − κ/σ > 0
  have hd : 0 < 1 - E.β * E.Mf - E.κ / E.σ := by
    have : E.κ / E.σ < (1 - E.M) * (1 - E.β * E.Mf) := by
      rw [div_lt_iff₀ hσ]; linarith
    nlinarith
  set d := 1 - E.β * E.Mf - E.κ / E.σ
  set L := E.κ * E.M / d
  set U := E.σ * (1 - E.M)
  have hLU : L < U := by
    rw [div_lt_iff₀ hd]
    have e : U * d = E.σ * (1 - E.M) * (1 - E.β * E.Mf) - E.κ * (1 - E.M) := by
      simp only [U, d]; field_simp
    rw [e]; nlinarith
  have hL : 0 < L := by positivity
  set w := (L + U) / 2
  have hw : 0 < w := by positivity
  have hwU : w < U := by simp only [w]; linarith
  have hLw : L < w := by simp only [w]; linarith
  set r1 := E.M + 1 / E.σ * w
  set r2 := (E.κ * E.M + (E.β * E.Mf + E.κ / E.σ) * w) / w
  have hr1 : r1 < 1 := by
    have : w < U := hwU
    have : 1 / E.σ * w < 1 - E.M := by
      rw [one_div_mul_eq_div, div_lt_iff₀ hσ]; simp only [U] at this; linarith
    linarith
  have hr2 : r2 < 1 := by
    rw [div_lt_one hw]
    have : L < w := hLw
    have : E.κ * E.M < w * d := by
      have := (div_lt_iff₀ hd).1 this; linarith
    simp only [d] at this; nlinarith
  have hr1' : 0 ≤ r1 := by positivity
  refine iter_tendsto_zero (ρ := max r1 r2) (w := w) hM₀.le (by positivity) (by positivity)
    (by positivity) hw (le_max_of_le_left hr1') (max_lt hr1 hr2) (le_max_left _ _) ?_
    (by simp; positivity) (by simp; positivity)
  calc E.κ * E.M + (E.β * E.Mf + E.κ / E.σ) * w = r2 * w := by
        simp only [r2]; field_simp
    _ ≤ max r1 r2 * w := by gcongr; exact le_max_right _ _

theorem iter_nonneg {B₁₁ B₁₂ B₂₁ B₂₂ : ℝ} {v : ℝ × ℝ} (h₁₁ : 0 ≤ B₁₁) (h₁₂ : 0 ≤ B₁₂)
    (h₂₁ : 0 ≤ B₂₁) (h₂₂ : 0 ≤ B₂₂) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2) (n : ℕ) :
    0 ≤ (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).1 ∧ 0 ≤ (iter B₁₁ B₁₂ B₂₁ B₂₂ v n).2 := by
  induction n with
  | zero => exact ⟨hv1, hv2⟩
  | succ n ih => simp only [iter]; exact ⟨by nlinarith [ih.1, ih.2], by nlinarith [ih.1, ih.2]⟩

/-- **Sharpness.** If the peg is not determinate,
`σ(1 − M)(1 − βM^f) ≤ κ`, the output response does not vanish: the
functional `ℓ = (1, (1 − M)/(κM))` satisfies `ℓB ≥ ℓ`, so `ℓ · response T`
never falls below its value `> 0` at `T = 0`. -/
theorem fgGE_not_vanishes (h : E.σ * (1 - E.M) * (1 - E.β * E.Mf) ≤ E.κ) :
    ¬ Tendsto (fun T => (E.response T).1) atTop (𝓝 0) := by
  have hσ := E.hσ; have hκ := E.hκ; have hβ₀ := E.hβ₀; have hM₀ := E.hM₀
  have hM₁ := E.hM₁; have hMf₀ := E.hMf₀
  set l := (1 - E.M) / (E.κ * E.M)
  have hl : 0 ≤ l := div_nonneg (by linarith) (by positivity)
  have hl1 : E.M + l * (E.κ * E.M) = 1 := by
    simp only [l]; field_simp; ring
  have hl2 : l ≤ 1 / E.σ + l * (E.β * E.Mf + E.κ / E.σ) := by
    have e : l * (1 - E.β * E.Mf - E.κ / E.σ) ≤ 1 / E.σ := by
      simp only [l]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hσ]
      have : (1 - E.M) * (1 - E.β * E.Mf - E.κ / E.σ) * E.σ =
          E.σ * (1 - E.M) * (1 - E.β * E.Mf) - E.κ * (1 - E.M) := by field_simp
      rw [this]; nlinarith
    linarith
  have hnn := iter_nonneg (B₁₁ := E.M) (B₁₂ := 1 / E.σ) (B₂₁ := E.κ * E.M)
    (B₂₂ := E.β * E.Mf + E.κ / E.σ) (v := (1 / E.σ, E.κ / E.σ)) hM₀.le (by positivity)
    (by positivity) (by positivity) (by simp; positivity) (by simp; positivity)
  have mono : ∀ T, 1 / E.σ ≤ (E.response T).1 + l * (E.response T).2 := by
    intro T
    induction T with
    | zero =>
      simp only [response, iter]
      have : 0 ≤ l * (E.κ / E.σ) := by positivity
      linarith
    | succ n ih =>
      have e : E.response (n + 1) = (E.M * (E.response n).1 + 1 / E.σ * (E.response n).2,
          E.κ * E.M * (E.response n).1 + (E.β * E.Mf + E.κ / E.σ) * (E.response n).2) := rfl
      rw [e]
      have ha := (hnn n).1; have hb := (hnn n).2
      change 0 ≤ (E.response n).1 at ha; change 0 ≤ (E.response n).2 at hb
      simp only
      nlinarith
  intro ht
  -- the second coordinate is bounded by a multiple of the first plus ...: use `ℓ · response`
  -- tends to `0` along with the first coordinate only if the second does; argue via the
  -- recursion: `response (T+1).1 ≥ (1/σ)·response T .2`
  have h2 : Tendsto (fun T => (E.response (T + 1)).1) atTop (𝓝 0) :=
    ht.comp (tendsto_add_atTop_nat 1)
  have hsq : Tendsto (fun T => E.σ * (E.response (T + 1)).1) atTop (𝓝 0) := by
    simpa using h2.const_mul E.σ
  have hle : ∀ T, (E.response T).2 ≤ E.σ * (E.response (T + 1)).1 := fun T => by
    have e : (E.response (T + 1)).1 = E.M * (E.response T).1 + 1 / E.σ * (E.response T).2 := rfl
    rw [e]
    have ha := (hnn T).1; change 0 ≤ (E.response T).1 at ha
    field_simp
    have := mul_nonneg (mul_nonneg hσ.le hM₀.le) ha
    linarith
  have hb : Tendsto (fun T => (E.response T).2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
      (fun T => (hnn T).2) hle
  have hsum : Tendsto (fun T => (E.response T).1 + l * (E.response T).2) atTop (𝓝 0) := by
    simpa using ht.add (hb.const_mul l)
  have := (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / E.σ by positivity))).exists
  obtain ⟨T, hT⟩ := this
  linarith [mono T]

/-- **Gabaix's condition is sharp**: forward guidance fades with the horizon
iff an interest-rate peg is determinate. -/
theorem fgGE_vanishes_iff : Tendsto (fun T => (E.response T).1) atTop (𝓝 0) ↔
    E.κ < E.σ * (1 - E.M) * (1 - E.β * E.Mf) := by
  constructor
  · intro ht; by_contra hc; exact E.fgGE_not_vanishes (not_lt.1 hc) ht
  · intro h; exact (E.fgGE_vanishes h).1

/-- In terms of determinacy of the peg itself. -/
theorem fgGE_vanishes_iff_determinate (hπ : E.φπ = 0) (hx : E.φx = 0) :
    Tendsto (fun T => (E.response T).1) atTop (𝓝 0) ↔ E.Determinate := by
  rw [fgGE_vanishes_iff, E.peg_determinate_iff hπ hx]

end Model

/-- **Non-vacuity.** In the model with `σ = 1`, `κ = 1/10`, `β = 99/100`,
`M = M^f = 1/2`, forward guidance fades with the horizon. -/
example : Tendsto (fun T => ((⟨1, 1 / 10, 99 / 100, 0, 0, 1 / 2, 1 / 2, one_pos, by norm_num,
    by norm_num, by norm_num, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num,
    by norm_num⟩ : Model).response T).1) atTop (𝓝 0) :=
  (Model.fgGE_vanishes _ (by norm_num)).1

end CognitiveNK

end Econ
