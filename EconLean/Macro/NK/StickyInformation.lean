/-
# Sticky information (Mankiw–Reis)

Mankiw and Reis (2002), "Sticky Information versus Sticky Prices: A Proposal
to Replace the New Keynesian Phillips Curve", QJE; Reis (2006), J. Monetary Econ.

**Setting.** Firms set prices every period but update their *information*
only occasionally: each period a fraction `λ ∈ (0,1]` of firms, drawn at
random, obtains current information. All variables are in logs. A firm's
desired price is `p*ₜ = pₜ + α yₜ = (1 − α) pₜ + α mₜ`, where `yₜ = mₜ − pₜ`
is output, `mₜ` nominal demand, and `α ∈ (0,1]` measures real rigidity.

**News shock.** Before date `0` everyone expected nominal demand path `m⁰`,
under which the economy is at its neutral equilibrium `p = m⁰`. At date `0`
the actual path `m` is revealed (announced). By date `t ≥ 0` the share of
firms that have updated since the announcement is
`Λₜ = 1 − (1 − λ)^{t+1}` (`share`). Updated firms set `p*ₜ` under `m`;
the others still set the price `m⁰ₜ` they expected. So the price level solves
`pₜ = Λₜ ((1 − α) pₜ + α mₜ) + (1 − Λₜ) m⁰ₜ` (`IsEquilibrium`).

**Results.**
* `existsUnique_equilibrium` and the closed form for output `output_eq`:
  `yₜ = (1 − Λₜ)(mₜ − m⁰ₜ) / (1 − Λₜ(1 − α))`.
* `output_zero_of_expected`: news that leaves date-`t` demand unchanged has
  no effect at date `t`; in particular a policy change announced before it
  takes effect has no output cost while it is not yet in force.
* `surprise_recession`: an unanticipated cut in nominal demand
  (`mₜ < m⁰ₜ`, `λ < 1`) causes a recession, `yₜ < 0`.
* `announced_disinflation_cost`: if the change only applies from date `T` on,
  output at every date is bounded by `(1 − λ)^{T+1} · |Δm| / α`: a disinflation
  announced far enough in advance is almost costless (contrast with the
  sticky-price Phillips curve, where announced disinflations can cause booms).
* `recovery`: after a permanent surprise demand shift, the output gap
  shrinks monotonically as information diffuses.

**Deviations.** Uninformed firms' expectations are fixed at the neutral
pre-shock path (`p = m⁰`); the general SIPC with stochastic expectations
`E_{t−j}` is not formalized. Deterministic news shock only. `m` is a level
path, so a "disinflation" here is a lower path of nominal demand; Mankiw–Reis's
results on inflation inertia and the timing of the inflation response to a
growth-rate change are not captured.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace StickyInfo

/-- Share of firms informed of the date-0 news by date `t`. -/
def share (lam : ℝ) (t : ℕ) : ℝ := 1 - (1 - lam) ^ (t + 1)

/-- Price-level equilibrium after a news shock. -/
def IsEquilibrium (lam α : ℝ) (m m0 p : ℕ → ℝ) : Prop :=
  ∀ t, p t = share lam t * ((1 - α) * p t + α * m t) + (1 - share lam t) * m0 t

variable {lam α : ℝ}

theorem one_sub_share (lam : ℝ) (t : ℕ) : 1 - share lam t = (1 - lam) ^ (t + 1) := by
  simp [share]

theorem share_mem (hl : 0 < lam) (hl1 : lam ≤ 1) (t : ℕ) :
    0 ≤ 1 - share lam t ∧ 1 - share lam t ≤ 1 := by
  rw [one_sub_share]
  exact ⟨pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith)⟩

/-- The denominator `1 − Λₜ(1 − α)` is at least `α`. -/
theorem den_ge (hl : 0 < lam) (hl1 : lam ≤ 1) (hα1 : α ≤ 1) (t : ℕ) :
    α ≤ 1 - share lam t * (1 - α) := by
  obtain ⟨h0, h1⟩ := share_mem hl hl1 t
  nlinarith

/-- Equilibrium output. -/
def output (lam α : ℝ) (m m0 : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 - share lam t) * (m t - m0 t) / (1 - share lam t * (1 - α))

theorem existsUnique_equilibrium (hl : 0 < lam) (hl1 : lam ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (m m0 : ℕ → ℝ) : ∃! p, IsEquilibrium lam α m m0 p := by
  have hd := fun t => (hα.trans_le (den_ge hl hl1 hα1 t)).ne'
  refine ⟨fun t => m t - output lam α m m0 t, fun t => ?_, fun p hp => funext fun t => ?_⟩
  · simp only [output]
    field_simp [hd t]
    ring
  · have := hp t
    simp only [output]
    field_simp [hd t]
    linarith

/-- **Output after the news.** -/
theorem output_eq (hl : 0 < lam) (hl1 : lam ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {m m0 p : ℕ → ℝ} (hp : IsEquilibrium lam α m m0 p) (t : ℕ) :
    m t - p t = output lam α m m0 t := by
  have hd := (hα.trans_le (den_ge hl hl1 hα1 t)).ne'
  have := hp t
  simp only [output]
  field_simp
  linarith

/-- News that leaves date-`t` demand unchanged has no effect on date-`t` output. -/
theorem output_zero_of_expected {m m0 : ℕ → ℝ} {t : ℕ} (h : m t = m0 t) :
    output lam α m m0 t = 0 := by
  simp [output, h]

/-- **A surprise demand contraction causes a recession.** -/
theorem surprise_recession (hl : 0 < lam) (hl1 : lam < 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {m m0 : ℕ → ℝ} {t : ℕ} (h : m t < m0 t) : output lam α m m0 t < 0 := by
  have hd := hα.trans_le (den_ge hl hl1.le hα1 t)
  have hs : 0 < 1 - share lam t := by rw [one_sub_share]; exact pow_pos (by linarith) _
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs (by linarith)) hd

/-- **Announced disinflations are (almost) costless.** If nominal demand
deviates from the old path by at most `D`, and only from date `T` on, then
output at every date is at most `(1 − λ)^{T+1} D / α` in absolute value. -/
theorem announced_disinflation_cost (hl : 0 < lam) (hl1 : lam ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {m m0 : ℕ → ℝ} {T : ℕ} {D : ℝ} (hpre : ∀ t < T, m t = m0 t)
    (hD : ∀ t, |m t - m0 t| ≤ D) (t : ℕ) :
    |output lam α m m0 t| ≤ (1 - lam) ^ (T + 1) * D / α := by
  have hd := hα.trans_le (den_ge hl hl1 hα1 t)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  rcases lt_or_ge t T with ht | ht
  · rw [output_zero_of_expected (hpre t ht), abs_zero]
    have : 0 ≤ 1 - lam := by linarith
    positivity
  · simp only [output, abs_div, abs_mul, one_sub_share, abs_of_pos hd,
      abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam) _)]
    rw [div_le_div_iff₀ hd hα]
    have hp : (1 - lam) ^ (t + 1) ≤ (1 - lam) ^ (T + 1) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    have hp0 : 0 ≤ (1 - lam) ^ (t + 1) := pow_nonneg (by linarith) _
    calc (1 - lam) ^ (t + 1) * |m t - m0 t| * α ≤ (1 - lam) ^ (T + 1) * D * α := by
          gcongr
          exact hD t
      _ ≤ (1 - lam) ^ (T + 1) * D * (1 - share lam t * (1 - α)) := by
          have : 0 ≤ (1 - lam) ^ (T + 1) * D := by
            have : 0 ≤ (1 - lam) ^ (T + 1) := pow_nonneg (by linarith) _
            positivity
          exact mul_le_mul_of_nonneg_left (den_ge hl hl1 hα1 t) this

/-- **Gradual recovery.** After a permanent surprise shift of nominal demand
by `Δ` (`mₜ − m⁰ₜ = Δ` for all `t`), the output gap shrinks in absolute value
every period as more firms learn about the shock. -/
theorem recovery (hl : 0 < lam) (hl1 : lam ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {m m0 : ℕ → ℝ} {Δ : ℝ} (hΔ : ∀ t, m t - m0 t = Δ) (t : ℕ) :
    |output lam α m m0 (t + 1)| ≤ |output lam α m m0 t| := by
  have g : ∀ s, |output lam α m m0 s| =
      (1 - lam) ^ (s + 1) / (1 - (1 - (1 - lam) ^ (s + 1)) * (1 - α)) * |Δ| := by
    intro s
    have hd := hα.trans_le (den_ge hl hl1 hα1 s)
    simp only [output, hΔ, abs_div, abs_mul, one_sub_share, abs_of_pos hd,
      abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam) _)]
    rw [show share lam s = 1 - (1 - lam) ^ (s + 1) by simp [share]]
    ring
  rw [g, g]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  -- `x ↦ x / (1 − (1 − x)(1 − α)) = x / (α + x(1 − α))` is increasing in `x ≥ 0`
  set a := (1 - lam) ^ (t + 1 + 1)
  set b := (1 - lam) ^ (t + 1)
  have ha : 0 ≤ a := pow_nonneg (by linarith) _
  have hab : a ≤ b := pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hda : 0 < 1 - (1 - a) * (1 - α) := by nlinarith
  have hdb : 0 < 1 - (1 - b) * (1 - α) := by nlinarith
  rw [div_le_div_iff₀ hda hdb]
  nlinarith

end StickyInfo
end Econ

end
