/-
# Monopoly: the markup rule, underprovision and third-degree price discrimination

MWG §12.B; Tirole, *The Theory of Industrial Organization*, Ch. 1 and 3.

A monopolist facing inverse demand `P` with cost `C` chooses `q ≥ 0` to maximize
`P(q) q − C(q)`.

Main results:
* `monopoly_foc` (MWG (12.B.4)): at an interior optimum, marginal revenue equals marginal
  cost: `P(q) + P'(q) q = C'(q)`.
* `lerner_rule`: the Lerner index equals the inverse elasticity of demand,
  `(p − C') / p = 1/ε` with `ε = −p / (P'(q) q)`.
* `monopoly_price_gt_mc` and `monopoly_output_lt` (MWG Prop. 12.B.1): with downward-sloping
  demand the monopoly price exceeds marginal cost, and with strictly decreasing demand and
  nondecreasing marginal cost the monopoly output is below the efficient (competitive)
  output.
* `linear_monopoly`: linear demand `a − bq`, constant marginal cost `c`: output `(a−c)/(2b)`,
  price `(a+c)/2`, and deadweight loss `(a−c)²/(8b)` (total surplus computed as an integral).
* `discrimination_price_le` and `third_degree_discrimination` (third-degree price
  discrimination, Tirole §3.2): a monopolist maximizing total profit over two separated
  markets with a common marginal cost sets `p (1 − 1/ε) = c` in each, so the market with the
  lower elasticity pays the higher price.
* `monopoly_optimum_lt_competitive`: the interior monopoly optimum is below the competitive
  output.
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

open Filter Topology

/-- The monopolist's profit at output `q`. -/
def monopolyProfit (P C : ℝ → ℝ) (q : ℝ) : ℝ := P q * q - C q

/-- `q` is a **monopoly optimum**: it maximizes profit over `q ≥ 0`. -/
def IsMonopolyOptimum (P C : ℝ → ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' ≥ 0, monopolyProfit P C q' ≤ monopolyProfit P C q

/-- **Marginal revenue equals marginal cost** at an interior monopoly optimum
(MWG (12.B.4)). -/
theorem monopoly_foc {P C : ℝ → ℝ} {q P' C' : ℝ} (hP : HasDerivAt P P' q)
    (hC : HasDerivAt C C' q) (hq : 0 < q) (hopt : IsMonopolyOptimum P C q) :
    P q + P' * q = C' := by
  have hd : HasDerivAt (monopolyProfit P C) (P' * q + P q * 1 - C') q :=
    (hP.mul (hasDerivAt_id q)).sub hC
  have hmax : IsLocalMax (monopolyProfit P C) q :=
    Filter.mem_of_superset (Ioi_mem_nhds hq) fun q' hq' => hopt.2 q' (le_of_lt hq')
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **The Lerner rule**: the markup over marginal cost, as a fraction of the price, equals
the inverse elasticity of demand `ε = −p / (P'(q) q)`. -/
theorem lerner_rule {P C : ℝ → ℝ} {q P' C' : ℝ} (hP : HasDerivAt P P' q)
    (hC : HasDerivAt C C' q) (hq : 0 < q) (hopt : IsMonopolyOptimum P C q) (hp : P q ≠ 0) :
    (P q - C') / P q = 1 / (-(P q) / (P' * q)) := by
  have h := monopoly_foc hP hC hq hopt
  have hq0 : q ≠ 0 := hq.ne'
  rw [← h]
  field_simp
  ring

/-- **The monopoly price exceeds marginal cost** when demand slopes down. -/
theorem monopoly_price_gt_mc {P C : ℝ → ℝ} {q P' C' : ℝ} (hP : HasDerivAt P P' q)
    (hC : HasDerivAt C C' q) (hq : 0 < q) (hopt : IsMonopolyOptimum P C q) (hP' : P' < 0) :
    C' < P q := by
  have h := monopoly_foc hP hC hq hopt
  nlinarith

/-- **Monopoly underprovision** (MWG Prop. 12.B.1). With strictly decreasing inverse demand
and nondecreasing marginal cost `MC`, an output `qm` at which price exceeds marginal cost is
below the competitive output `qo`, where price equals marginal cost. -/
theorem monopoly_output_lt {P MC : ℝ → ℝ} (hP : StrictAnti P) (hMC : Monotone MC)
    {qm qo : ℝ} (hm : MC qm < P qm) (ho : P qo = MC qo) : qm < qo := by
  by_contra h
  push Not at h
  have h1 : P qm ≤ P qo := hP.antitone h
  have h2 : MC qo ≤ MC qm := hMC h
  linarith

/-! ### Linear demand -/

/-- Total surplus at output `q`: the area between inverse demand `a − bs` and marginal
cost `c`. -/
noncomputable def linearSurplus (a b c q : ℝ) : ℝ := ∫ s in (0 : ℝ)..q, (a - b * s - c)

lemma linearSurplus_eq (a b c q : ℝ) : linearSurplus a b c q = (a - c) * q - b * q ^ 2 / 2 := by
  have e : linearSurplus a b c q = ∫ s in (0 : ℝ)..q, ((a - c) - b * s) := by
    simp only [linearSurplus]; congr 1; funext s; ring
  rw [e, intervalIntegral.integral_sub (f := fun _ => a - c) (g := fun s => b * s)
    intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable 0 q)]
  have h1 : ∫ x in (0 : ℝ)..q, b * x = b * (q ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [h1, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Linear monopoly.** With inverse demand `a − bq` (`b > 0`) and constant marginal cost
`c < a`, the monopoly output is `(a−c)/(2b)`, the price `(a+c)/2`, and the deadweight loss
(surplus at the competitive output `(a−c)/b` minus surplus at the monopoly output) is
`(a−c)²/(8b)`. -/
theorem linear_monopoly {a b c : ℝ} (hb : 0 < b) (hac : c < a) :
    IsMonopolyOptimum (fun q => a - b * q) (fun q => c * q) ((a - c) / (2 * b)) ∧
      a - b * ((a - c) / (2 * b)) = (a + c) / 2 ∧
      linearSurplus a b c ((a - c) / b) - linearSurplus a b c ((a - c) / (2 * b)) =
        (a - c) ^ 2 / (8 * b) := by
  refine ⟨⟨div_nonneg (by linarith) (by linarith), fun q _ => ?_⟩, ?_, ?_⟩
  · simp only [monopolyProfit]
    have : (a - b * q) * q - c * q =
        (a - c) ^ 2 / (4 * b) - b * (q - (a - c) / (2 * b)) ^ 2 := by field_simp; ring
    rw [this]
    have : (a - b * ((a - c) / (2 * b))) * ((a - c) / (2 * b)) - c * ((a - c) / (2 * b)) =
        (a - c) ^ 2 / (4 * b) := by field_simp; ring
    rw [this]
    nlinarith [sq_nonneg (q - (a - c) / (2 * b))]
  · field_simp; ring
  · rw [linearSurplus_eq, linearSurplus_eq]
    field_simp
    ring

/-! ### Third-degree price discrimination -/

/-- **Inverse-elasticity pricing across markets.** If a monopolist with common marginal
cost `c ≥ 0` sets prices `pₖ, pₗ` with `pₖ (1 − 1/εₖ) = c` and `pₗ (1 − 1/εₗ) = c`
(marginal revenue equals marginal cost in each market, written with the elasticities
`εₖ, εₗ > 1`), then the less elastic market pays more: `εₖ ≤ εₗ → pₗ ≤ pₖ`. -/
theorem discrimination_price_le {c pk pl εk εl : ℝ} (hc : 0 ≤ c) (hk1 : 1 < εk)
    (hl1 : 1 < εl) (hk : pk * (1 - 1 / εk) = c) (hl : pl * (1 - 1 / εl) = c)
    (hε : εk ≤ εl) : pl ≤ pk := by
  have hk0 : εk ≠ 0 := by positivity
  have hl0 : εl ≠ 0 := by positivity
  have ek : pk = c * εk / (εk - 1) := by
    field_simp [show εk - 1 ≠ 0 by linarith] at hk ⊢; linarith
  have el : pl = c * εl / (εl - 1) := by
    field_simp [show εl - 1 ≠ 0 by linarith] at hl ⊢; linarith
  rw [ek, el, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hc (sub_nonneg.2 hε)]

/-- **Monopoly underprovision at the optimum** (MWG Prop. 12.B.1): with strictly decreasing
inverse demand and nondecreasing marginal cost `MC = C'`, an interior monopoly optimum lies
strictly below any competitive output `qo` (where `P(qo) = MC(qo)`). -/
theorem monopoly_optimum_lt_competitive {P C MC : ℝ → ℝ} {qm qo P' : ℝ}
    (hP : HasDerivAt P P' qm) (hC : HasDerivAt C (MC qm) qm) (hqm : 0 < qm)
    (hopt : IsMonopolyOptimum P C qm) (hP' : P' < 0) (hPanti : StrictAnti P)
    (hMC : Monotone MC) (ho : P qo = MC qo) : qm < qo :=
  monopoly_output_lt hPanti hMC (monopoly_price_gt_mc hP hC hqm hopt hP') ho

/-- Profit of a monopolist selling `q.1` in market 1 and `q.2` in market 2 at constant
marginal cost `c`. -/
def discrimProfit (P₁ P₂ : ℝ → ℝ) (c : ℝ) (q : ℝ × ℝ) : ℝ :=
  P₁ q.1 * q.1 + P₂ q.2 * q.2 - c * (q.1 + q.2)

/-- **Third-degree price discrimination** (Tirole §3.2). A monopolist serving two separated
markets at common marginal cost `c ≥ 0` chooses `(q₁, q₂) ≥ 0` to maximize total profit. At
an interior optimum, if the price elasticities `εₖ = −pₖ / (Pₖ'(qₖ) qₖ)` exceed one, the
market with the lower elasticity pays the higher price. -/
theorem third_degree_discrimination {P₁ P₂ : ℝ → ℝ} {c q₁ q₂ P₁' P₂' : ℝ} (hc : 0 ≤ c)
    (h₁ : HasDerivAt P₁ P₁' q₁) (h₂ : HasDerivAt P₂ P₂' q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hopt : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 →
      discrimProfit P₁ P₂ c q ≤ discrimProfit P₁ P₂ c (q₁, q₂))
    (hε₁ : 1 < -(P₁ q₁) / (P₁' * q₁)) (hε₂ : 1 < -(P₂ q₂) / (P₂' * q₂))
    (hε : -(P₁ q₁) / (P₁' * q₁) ≤ -(P₂ q₂) / (P₂' * q₂)) : P₂ q₂ ≤ P₁ q₁ := by
  have hlin : ∀ q, HasDerivAt (fun q : ℝ => c * q) c q := fun q => by
    simpa using (hasDerivAt_id q).const_mul c
  -- Each market's quantity is a monopoly optimum given the other.
  have hm₁ : IsMonopolyOptimum P₁ (fun q => c * q) q₁ := ⟨hq₁.le, fun q hq => by
    have := hopt (q, q₂) hq hq₂.le
    simp only [discrimProfit] at this
    simp only [monopolyProfit]; linarith⟩
  have hm₂ : IsMonopolyOptimum P₂ (fun q => c * q) q₂ := ⟨hq₂.le, fun q hq => by
    have := hopt (q₁, q) hq₁.le hq
    simp only [discrimProfit] at this
    simp only [monopolyProfit]; linarith⟩
  have f₁ := monopoly_foc h₁ (hlin q₁) hq₁ hm₁
  have f₂ := monopoly_foc h₂ (hlin q₂) hq₂ hm₂
  -- Rewrite marginal revenue as `p (1 − 1/ε)`.
  have hmr : ∀ {p P' q : ℝ}, 0 < q → 1 < -p / (P' * q) →
      p * (1 - 1 / (-p / (P' * q))) = p + P' * q :=
    fun {p P' q} hq hε => by
      have hP' : P' ≠ 0 := by rintro rfl; simp at hε; linarith
      have hp : p ≠ 0 := by rintro rfl; simp at hε; linarith
      field_simp
      ring
  exact discrimination_price_le hc hε₁ hε₂ (by rw [hmr hq₁ hε₁]; exact f₁)
    (by rw [hmr hq₂ hε₂]; exact f₂) hε

end Econ
