/-
# Fiat money in a search economy (Kiyotaki–Wright)

Kiyotaki and Wright (1993), "A Search-Theoretic Approach to Monetary
Economics", AER; Wright (lecture notes), Nosal–Rocheteau, *Money, Payments,
and Liquidity*, ch. 3.

**Setting (continuous time, indivisible goods and money).** A fraction
`M ∈ (0,1)` of agents hold one unit of fiat money; the rest are producers.
Agents meet at rate `α > 0`; in any meeting an agent likes the partner's good
with probability `x ∈ (0,1]` (so a barter double coincidence has probability
`x²`). Consuming gives utility `u`, producing costs `c`, `0 < c < u`; the
discount rate is `r > 0`. Producers accept money with probability `Π`
(the same for everyone in a symmetric equilibrium). Values `V₀` (producer) and
`V₁` (money holder) satisfy (`IsValue`)
* `r V₀ = α(1 − M) x² (u − c) + α M x Π (V₁ − V₀ − c)`,
* `r V₁ = α(1 − M) x Π (u + V₀ − V₁)`.
A producer is willing to accept money iff `V₁ − V₀ ≥ c`. An equilibrium is a
`Π ∈ {0, 1}` that is a best response given the values it generates (`IsEq`).

**Results.**
* `nonmonetary`: `Π = 0` is always an equilibrium (money is worthless if
  nobody accepts it).
* `monetary_iff`: `Π = 1` is an equilibrium iff
  `α x (1 − M)(1 − x)(u − c) ≥ r c`.
* `no_money_with_double_coincidence`: with `x = 1` (every meeting is a
  double coincidence) there is no monetary equilibrium: money is valued only
  because it overcomes the absence of a double coincidence of wants.
* `monetary_iff_rbar`, `rbar_pos`: equivalently `r ≤ r̄`, and `r̄ > 0`
  whenever `x < 1`: patient enough agents value money.
* `mixed_iff`: a mixed equilibrium `Π ∈ (0, 1)` (`IsMixedEq`, with
  indifference `V₁ − V₀ = c`) exists iff the monetary condition holds
  strictly.

**Deviations.** Produce-on-demand timing (Williamson–Wright textbook
variant): a seller pays `c` when trading, and a money holder pays nothing
when buying, rather than KW93's "consume, then produce a new good" timing;
the threshold has the same form. Symmetric equilibria: the same `Π` is each
agent's own and everyone else's acceptance probability. Values are any
solution of the Bellman equations (they are unique; `delta_eq`).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace KiyotakiWright

/-- Parameters of the model. -/
structure Params where
  r : ℝ
  α : ℝ
  M : ℝ
  x : ℝ
  u : ℝ
  c : ℝ
  hr : 0 < r
  hα : 0 < α
  hM : 0 < M ∧ M < 1
  hx : 0 < x ∧ x ≤ 1
  hc : 0 < c
  hcu : c < u

namespace Params

variable (P : Params)

/-- The Bellman equations given acceptance probability `acc`. -/
def IsValue (acc V₀ V₁ : ℝ) : Prop :=
  P.r * V₀ = P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) + P.α * P.M * P.x * acc * (V₁ - V₀ - P.c) ∧
  P.r * V₁ = P.α * (1 - P.M) * P.x * acc * (P.u + V₀ - V₁)

/-- A symmetric pure-strategy equilibrium. -/
def IsEq (acc : ℝ) : Prop :=
  (acc = 0 ∨ acc = 1) ∧ ∃ V₀ V₁, P.IsValue acc V₀ V₁ ∧
    (acc = 1 → P.c ≤ V₁ - V₀) ∧ (acc = 0 → V₁ - V₀ ≤ P.c)

/-- With `acc = 1`, the value of money is pinned down:
`(r + αx)(V₁ − V₀) = αx[(1 − M)(u − x(u − c)) + M c]`. -/
theorem delta_eq {V₀ V₁ : ℝ} (h : P.IsValue 1 V₀ V₁) :
    (P.r + P.α * P.x) * (V₁ - V₀) =
      P.α * P.x * ((1 - P.M) * (P.u - P.x * (P.u - P.c)) + P.M * P.c) := by
  obtain ⟨h0, h1⟩ := h
  linear_combination h1 - h0

/-- **Money is worthless if nobody accepts it.** -/
theorem nonmonetary : P.IsEq 0 := by
  have hr := P.hr.ne'
  refine ⟨Or.inl rfl, P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) / P.r, 0,
    ⟨by field_simp; ring, by ring⟩, fun h => absurd h (by norm_num), fun _ => ?_⟩
  have : 0 ≤ P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) / P.r := by
    have := P.hα; have := P.hM; have := P.hx; have := P.hcu
    apply div_nonneg _ P.hr.le
    apply mul_nonneg (mul_nonneg (mul_nonneg P.hα.le (by linarith)) (sq_nonneg _)) (by linarith)
  linarith [P.hc]

theorem isValue_one_exists : ∃ V₀ V₁, P.IsValue 1 V₀ V₁ := by
  -- solve the linear system explicitly
  have hr := P.hr; have hα := P.hα; have hx := P.hx.1
  set D := P.α * P.x * ((1 - P.M) * (P.u - P.x * (P.u - P.c)) + P.M * P.c) / (P.r + P.α * P.x)
  have hden : 0 < P.r + P.α * P.x := by positivity
  refine ⟨(P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) + P.α * P.M * P.x * (D - P.c)) / P.r,
    (P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) + P.α * P.M * P.x * (D - P.c)) / P.r + D, ?_, ?_⟩
  · field_simp; ring
  · simp only [D]; field_simp; ring

/-- **Existence of monetary equilibrium.** `acc = 1` is an equilibrium iff
`α x (1 − M)(1 − x)(u − c) ≥ r c`. -/
theorem monetary_iff : P.IsEq 1 ↔ P.r * P.c ≤ P.α * P.x * (1 - P.M) * (1 - P.x) * (P.u - P.c) := by
  have hden : 0 < P.r + P.α * P.x := by have := P.hx.1; have := P.hα; have := P.hr; positivity
  constructor
  · rintro ⟨-, V₀, V₁, hv, h1, -⟩
    have hd := P.delta_eq hv
    have := h1 rfl
    nlinarith
  · intro h
    obtain ⟨V₀, V₁, hv⟩ := P.isValue_one_exists
    refine ⟨Or.inr rfl, V₀, V₁, hv, fun _ => ?_, fun h => absurd h (by norm_num)⟩
    have hd := P.delta_eq hv
    by_contra hlt; push Not at hlt
    have : (P.r + P.α * P.x) * (V₁ - V₀) < (P.r + P.α * P.x) * P.c :=
      mul_lt_mul_of_pos_left hlt hden
    nlinarith

/-- **No money with a double coincidence of wants.** -/
theorem no_money_with_double_coincidence (hx : P.x = 1) : ¬ P.IsEq 1 := by
  rw [monetary_iff, hx]
  have := mul_pos P.hr P.hc
  simp; linarith

/-- A symmetric **mixed** equilibrium: acceptance probability strictly
between 0 and 1, which requires indifference `V₁ − V₀ = c`. -/
def IsMixedEq (acc : ℝ) : Prop :=
  0 < acc ∧ acc < 1 ∧ ∃ V₀ V₁, P.IsValue acc V₀ V₁ ∧ V₁ - V₀ = P.c

/-- **Mixed monetary equilibrium.** A mixed equilibrium exists iff the pure
monetary condition holds strictly; it is unique, with acceptance probability
`x + r c/(α(1 − M) x (u − c))`. -/
theorem mixed_iff :
    (∃ acc, P.IsMixedEq acc) ↔ P.r * P.c < P.α * P.x * (1 - P.M) * (1 - P.x) * (P.u - P.c) := by
  have hK : 0 < P.α * (1 - P.M) * P.x * (P.u - P.c) := by
    have := P.hα; have := P.hM.2; have := P.hx.1; have := P.hcu
    apply mul_pos (mul_pos (mul_pos P.hα (by linarith)) P.hx.1) (by linarith)
  constructor
  · rintro ⟨acc, -, hacc1, V₀, V₁, ⟨h0, h1⟩, hd⟩
    have key : P.r * P.c = P.α * (1 - P.M) * P.x * (P.u - P.c) * (acc - P.x) := by
      have hV₁ : V₁ = V₀ + P.c := by linarith
      subst hV₁
      linear_combination h1 - h0
    have := mul_lt_mul_of_pos_left (show acc - P.x < 1 - P.x by linarith) hK
    nlinarith
  · intro h
    set K := P.α * (1 - P.M) * P.x * (P.u - P.c)
    have hlt : P.r * P.c / K < 1 - P.x := by
      rw [div_lt_iff₀ hK]; linarith
    have hpos : 0 < P.r * P.c / K := div_pos (mul_pos P.hr P.hc) hK
    refine ⟨P.x + P.r * P.c / K, by linarith [P.hx.1], by linarith,
      P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) / P.r,
      P.α * (1 - P.M) * P.x ^ 2 * (P.u - P.c) / P.r + P.c, ⟨?_, ?_⟩, by ring⟩
    · have := P.hr.ne'; field_simp; ring
    · have := P.hr.ne'; have := hK.ne'; field_simp; ring

/-- The critical discount rate `r̄ = αx(1 − M)(1 − x)(u − c)/c`. -/
def rbar : ℝ := P.α * P.x * (1 - P.M) * (1 - P.x) * (P.u - P.c) / P.c

/-- **Patience sustains money**: a monetary equilibrium exists iff `r ≤ r̄`. -/
theorem monetary_iff_rbar : P.IsEq 1 ↔ P.r ≤ P.rbar := by
  rw [monetary_iff, rbar, le_div_iff₀ P.hc]

/-- Without a double coincidence for sure (`x < 1`), `r̄ > 0`: sufficiently
patient economies have monetary equilibria. -/
theorem rbar_pos (hx1 : P.x < 1) : 0 < P.rbar := by
  have := P.hα; have := P.hx.1; have := P.hM.2; have := P.hcu; have := P.hc
  unfold rbar
  apply div_pos _ P.hc
  apply mul_pos (mul_pos (mul_pos (mul_pos P.hα P.hx.1) (by linarith)) (by linarith))
  linarith

/-- **Non-vacuity**: a monetary equilibrium exists for some parameters. -/
example : (⟨1 / 100, 1, 1 / 2, 1 / 2, 2, 1, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩ : Params).IsEq 1 := by
  rw [monetary_iff]; norm_num

end Params
end KiyotakiWright
end Econ

end
