/-
# Credit cycles: the intertemporal multiplier (stylized dynamic Kiyotaki–Moore)

A stylized linearization in the spirit of Kiyotaki and Moore (1997),
"Credit Cycles", JPE, §2–3, as presented in Brunnermeier–Eisenbach–Sannikov
(2013), §2.2. It is not KM's own system of equations.

**Setting.** Deviations from steady state after a shock at date 0.
Constrained farmers' landholdings follow the linearized law of motion
`k_{t+1} = λ k_t` (`HoldingsEq`) with persistence `λ ∈ [0, 1)`. In KM this
persistence is *derived* from the slow rebuilding of farmers' net worth;
here `λ` is an **exogenous parameter**, so `persistence` below shows how the
price inherits it rather than deriving it. The land price `q_t` is the
present value of future user costs: the land-market equilibrium gives the
user cost `q_t − q_{t+1}/R` (gross rate `R > 1`) as an increasing linear
function of farmers' holdings, `ψ k_t` with `ψ > 0` (`PriceEq`; `ψ` is a
price-response coefficient, not KM's land-supply elasticity `η`). At date 0
farmers' net worth falls one-for-one with productivity and land-price losses
on their inherited land `K̄ > 0`, so with down payment `d` their holdings
satisfy `d k_0 = K̄ (Δa + q_0)` (`ImpactEq`, the linearized form of
`Econ.KiyotakiMoore.IsEq`).

**Results.**
* `holdings_eq`: `k_t = λ^t k_0`.
* `price_eq`: for any bounded price path solving the pricing equation, the
  land price is `q_t = φ k_t` with `φ = ψ R/(R − λ)`: the **intertemporal
  multiplier** — the price capitalizes all future user-cost changes.
* `φ_ge`, `φ_gt`, `φ_strictMono`: `φ ≥ ψ` (the static response), strictly
  if `λ > 0`, and `φ` increases with persistence.
* `impact`: under the stability condition `d > K̄ φ`, date-0 holdings are
  `k_0 = K̄ Δa/(d − K̄ φ)`.
* `amplification`: for `Δa > 0` the dynamic response exceeds the static
  collateral multiplier `K̄ Δa/(d − K̄ ψ)` (and the direct effect `K̄ Δa/d`)
  whenever `λ > 0`: persistence amplifies the impact of the shock.
* `persistence`: land prices inherit the holdings' decay rate `λ`.

**Deviations.** Linearized reduced form; the persistence `λ` is a parameter
(KM derive it from farmers' budget constraints); the user-cost schedule is
linear; the no-bubble condition is imposed as boundedness of the price path.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace DynamicKM

open Filter Topology

/-- Parameters. -/
structure Params where
  ψ : ℝ
  R : ℝ
  lam : ℝ
  d : ℝ
  Kbar : ℝ
  hψ : 0 < ψ
  hR : 1 < R
  hlam : 0 ≤ lam ∧ lam < 1
  hK : 0 < Kbar

namespace Params

variable (P : Params)

/-- The intertemporal price multiplier `ψ R/(R − λ)`. -/
def φ : ℝ := P.ψ * P.R / (P.R - P.lam)

theorem R_sub_pos : 0 < P.R - P.lam := by linarith [P.hR, P.hlam.2]

/-- Linearized law of motion of farmers' holdings: deviations decay at the
(exogenous) rate `λ`. -/
def HoldingsEq (k : ℕ → ℝ) : Prop := ∀ t, k (t + 1) = P.lam * k t

/-- Land-market equilibrium: the user cost `q_t − q_{t+1}/R` equals `ψ k_t`. -/
def PriceEq (k q : ℕ → ℝ) : Prop := ∀ t, q t = P.ψ * k t + q (t + 1) / P.R

theorem holdings_eq {k : ℕ → ℝ} (hk : P.HoldingsEq k) (t : ℕ) : k t = P.lam ^ t * k 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [hk t, ih, pow_succ]; ring

/-- Forward solution of `q_t = ψ λ^t k₀ + q_{t+1}/R` (bounded solutions). -/
theorem price_eq_aux {k₀ : ℝ} {q : ℕ → ℝ}
    (hq : ∀ t, q t = P.ψ * (P.lam ^ t * k₀) + q (t + 1) / P.R) (hb : ∃ M, ∀ t, |q t| ≤ M) (t : ℕ) :
    q t = P.φ * (P.lam ^ t * k₀) := by
  obtain ⟨M, hM⟩ := hb
  have hR0 : 0 < P.R := by linarith [P.hR]
  set r := P.lam / P.R
  have hr0 : 0 ≤ r := div_nonneg P.hlam.1 hR0.le
  have hr1 : r < 1 := by rw [div_lt_one hR0]; linarith [P.hR, P.hlam.2]
  -- iterate `n` times
  have iter : ∀ n, q t = P.ψ * (P.lam ^ t * k₀) * ∑ s ∈ Finset.range n, r ^ s +
      q (t + n) / P.R ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, Finset.sum_range_succ, hq (t + n), pow_succ, show t + n + 1 = t + (n + 1) by ring]
      simp only [r, div_pow, pow_add]
      field_simp
      ring
  -- the remainder vanishes
  have hrem : Tendsto (fun n => q (t + n) / P.R ^ n) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => M / P.R ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hR0.le)
        (inv_lt_one_of_one_lt₀ P.hR)).const_mul M
      simpa [div_eq_mul_inv, inv_pow] using this
    apply squeeze_zero_norm _ hpow
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hR0 n)]
    exact div_le_div_of_nonneg_right (hM _) (pow_pos hR0 n).le
  have hgeom : Tendsto (fun n => ∑ s ∈ Finset.range n, r ^ s) atTop (𝓝 (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).tendsto_sum_nat
  have hlim : Tendsto (fun n => P.ψ * (P.lam ^ t * k₀) * ∑ s ∈ Finset.range n, r ^ s +
      q (t + n) / P.R ^ n) atTop (𝓝 (P.ψ * (P.lam ^ t * k₀) * (1 - r)⁻¹ + 0)) :=
    (hgeom.const_mul _).add hrem
  have hconst : Tendsto (fun _ : ℕ => q t) atTop (𝓝 (q t)) := tendsto_const_nhds
  have heq := tendsto_nhds_unique hconst (hlim.congr' (Eventually.of_forall fun n => (iter n).symm))
  rw [heq, add_zero, φ]
  have h1 : (1 - r) = (P.R - P.lam) / P.R := by simp only [r]; field_simp
  rw [h1, inv_div]
  ring

/-- **The intertemporal multiplier.** For every bounded solution of the
pricing equation along the holdings path, `q_t = φ k_t`. -/
theorem price_eq {k q : ℕ → ℝ} (hk : P.HoldingsEq k) (hq : P.PriceEq k q)
    (hb : ∃ M, ∀ t, |q t| ≤ M) (t : ℕ) : q t = P.φ * k t := by
  rw [P.holdings_eq hk t]
  exact P.price_eq_aux (fun s => by rw [hq s, P.holdings_eq hk s]) hb t

theorem φ_ge : P.ψ ≤ P.φ := by
  rw [φ, le_div_iff₀ P.R_sub_pos]
  nlinarith [P.hψ, P.hlam.1]

theorem φ_gt (hlam : 0 < P.lam) : P.ψ < P.φ := by
  rw [φ, lt_div_iff₀ P.R_sub_pos]
  nlinarith [P.hψ]

/-- More persistence, a larger price multiplier. -/
theorem φ_strictMono (P' : Params) (hψ : P'.ψ = P.ψ) (hR : P'.R = P.R) (hlam : P.lam < P'.lam) :
    P.φ < P'.φ := by
  simp only [φ, hψ, hR]
  have h1 := P.R_sub_pos
  have h2 : 0 < P.R - P'.lam := by rw [← hR]; exact P'.R_sub_pos
  apply div_lt_div_of_pos_left (mul_pos P.hψ (by linarith [P.hR])) h2
  linarith

/-- Date-0 holdings given the price response. -/
def ImpactEq (Δa k₀ q₀ : ℝ) : Prop := P.d * k₀ = P.Kbar * (Δa + q₀)

/-- **Impact response.** -/
theorem impact (hstab : P.Kbar * P.φ < P.d) {Δa : ℝ} {k q : ℕ → ℝ} (hk : P.HoldingsEq k)
    (hq : P.PriceEq k q) (hb : ∃ M, ∀ t, |q t| ≤ M) (h : P.ImpactEq Δa (k 0) (q 0)) :
    k 0 = P.Kbar * Δa / (P.d - P.Kbar * P.φ) := by
  have hq0 := P.price_eq hk hq hb 0
  rw [ImpactEq, hq0] at h
  rw [eq_div_iff (by linarith)]
  linarith

/-- **Persistence amplifies.** For a positive shock and `λ > 0`, the dynamic
response exceeds the static collateral multiplier, which in turn exceeds the
direct effect. -/
theorem amplification (hstab : P.Kbar * P.φ < P.d) (hlam : 0 < P.lam) {Δa : ℝ}
    (hΔ : 0 < Δa) {k q : ℕ → ℝ} (hk : P.HoldingsEq k) (hq : P.PriceEq k q)
    (hb : ∃ M, ∀ t, |q t| ≤ M) (h : P.ImpactEq Δa (k 0) (q 0)) :
    P.Kbar * Δa / P.d < P.Kbar * Δa / (P.d - P.Kbar * P.ψ) ∧
      P.Kbar * Δa / (P.d - P.Kbar * P.ψ) < k 0 := by
  rw [P.impact hstab hk hq hb h]
  have hφ := P.φ_gt hlam
  have hKη : P.Kbar * P.ψ < P.Kbar * P.φ := mul_lt_mul_of_pos_left hφ P.hK
  have hnum : 0 < P.Kbar * Δa := mul_pos P.hK hΔ
  have hd1 : 0 < P.d - P.Kbar * P.φ := by linarith
  have hd2 : 0 < P.d - P.Kbar * P.ψ := by linarith
  refine ⟨div_lt_div_of_pos_left hnum hd2 (by nlinarith [mul_pos P.hK P.hψ]),
    div_lt_div_of_pos_left hnum hd1 (by linarith)⟩

/-- **Persistence**: holdings and prices decay at rate `λ`. -/
theorem persistence {k q : ℕ → ℝ} (hk : P.HoldingsEq k) (hq : P.PriceEq k q)
    (hb : ∃ M, ∀ t, |q t| ≤ M) (t : ℕ) : q (t + 1) = P.lam * q t := by
  rw [P.price_eq hk hq hb, P.price_eq hk hq hb, hk t]
  ring

end Params
end DynamicKM
end Econ

end
