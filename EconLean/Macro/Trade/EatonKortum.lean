/-
# Ricardian trade with Fréchet productivities (Eaton–Kortum)

Eaton and Kortum (2002), "Technology, Geography, and Trade", Econometrica;
Costinot–Rodríguez-Clare (2014), Handbook of International Economics, §3.

**Setting.** A destination buys each of a continuum of goods from the
cheapest source. Source `i` has efficiency drawn from a Fréchet distribution
`P(z ≤ s) = exp(−T_i s^{−θ})`, so its delivered price `p_i = c_i d_i / z` has
`P(p_i > p) = exp(−Φ_i p^θ)` with `Φ_i = T_i (c_i d_i)^{−θ} > 0`. Equivalently
`U_i = p_i^θ` is exponential with rate `Φ_i`, and since `p ↦ p^θ` is
increasing, `i` is the cheapest source iff `U_i` is the smallest. Write
`Φ = Σ_k Φ_k`.

**Results.**
* `survival_min`: the minimum of independent `U_k` has survival
  `Π_k exp(−Φ_k u) = exp(−Φ u)`.
* `trade_share`: the probability that `i` is the cheapest source,
  `∫_0^∞ Φ_i e^{−Φ_i u} Π_{k ≠ i} e^{−Φ_k u} du`, equals `Φ_i/Φ`: the
  **gravity trade share** `π_i = T_i (c_i d_i)^{−θ} / Σ_k T_k (c_k d_k)^{−θ}`.
* `trade_shares_sum`: the shares sum to one.
* `frechet_to_exp`: the change of variables from Fréchet productivity to
  exponential `U = p^θ`.
* `price_moment`: with CES demand (elasticity `σ < 1 + θ`),
  `E[p^{1−σ}] = Γ(1 + (1 − σ)/θ) Φ^{(σ−1)/θ}`, so the CES price index
  (`priceIndex`) is `P = γ Φ^{−1/θ}` with `γ = Γ(1 + (1 − σ)/θ)^{1/(1−σ)}`
  (`priceIndex_eq`).
* `real_wage`: with `Φ_k = T_k (w_k d_k)^{−θ}` and `d_n = 1`, the real wage is
  `w_n/P_n = γ^{−1} (T_n/π_nn)^{1/θ}` where `π_nn` is the domestic trade share:
  welfare depends only on the domestic trade share and the trade elasticity
  `θ` (the ACR formula).

**Deviations.** Independence across sources and the Fréchet-to-exponential
change of variables (`U = p^θ`) are stated in the docstring, not derived from
a probability space; the integrals are written directly.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace EatonKortum

open Real MeasureTheory Set Finset

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (Φ : ι → ℝ)

omit [DecidableEq ι] in
/-- Survival of the minimum of independent exponentials. -/
theorem survival_min (u : ℝ) :
    ∏ k ∈ s, Real.exp (-(Φ k * u)) = Real.exp (-((∑ k ∈ s, Φ k) * u)) := by
  rw [← Real.exp_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- **Gravity trade shares**: the probability that `i` is the cheapest source. -/
theorem trade_share (hΦ : ∀ k ∈ s, 0 < Φ k) {i : ι} (hi : i ∈ s) :
    ∫ u in Ioi (0 : ℝ), Φ i * Real.exp (-(Φ i * u)) * ∏ k ∈ s.erase i, Real.exp (-(Φ k * u)) =
      Φ i / ∑ k ∈ s, Φ k := by
  have hsum : 0 < ∑ k ∈ s, Φ k := Finset.sum_pos hΦ ⟨i, hi⟩
  have hint : ∀ u, Φ i * Real.exp (-(Φ i * u)) * ∏ k ∈ s.erase i, Real.exp (-(Φ k * u)) =
      Φ i * Real.exp ((-∑ k ∈ s, Φ k) * u) := by
    intro u
    rw [mul_assoc, survival_min, ← Real.exp_add, ← Finset.add_sum_erase s Φ hi]
    congr 2; ring
  simp_rw [hint]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

omit [DecidableEq ι] in
theorem trade_shares_sum (hΦ : ∀ k ∈ s, 0 < Φ k) (hne : s.Nonempty) :
    ∑ i ∈ s, Φ i / ∑ k ∈ s, Φ k = 1 := by
  rw [← Finset.sum_div, div_self (Finset.sum_pos hΦ hne).ne']

/-- **The price moment.** If `U = p^θ` is exponential with rate `Φ`, then
`E[p^{1−σ}] = E[U^{(1−σ)/θ}] = Γ(1 + (1−σ)/θ) Φ^{(σ−1)/θ}`. -/
theorem price_moment {θ σ Φtot : ℝ} (hθ : 0 < θ) (hσ : σ < 1 + θ) (hΦ : 0 < Φtot) :
    ∫ u in Ioi (0 : ℝ), u ^ ((1 - σ) / θ) * (Φtot * Real.exp (-(Φtot * u))) =
      Real.Gamma (1 + (1 - σ) / θ) * Φtot ^ ((σ - 1) / θ) := by
  have ha : 0 < 1 + (1 - σ) / θ := by
    have : -1 < (1 - σ) / θ := by rw [lt_div_iff₀ hθ]; linarith
    linarith
  have h := integral_rpow_mul_exp_neg_mul_Ioi ha hΦ
  have e : 1 + (1 - σ) / θ - 1 = (1 - σ) / θ := by ring
  rw [e] at h
  have : ∀ u, u ^ ((1 - σ) / θ) * (Φtot * Real.exp (-(Φtot * u))) =
      Φtot * (u ^ ((1 - σ) / θ) * Real.exp (-(Φtot * u))) := fun u => by ring
  simp_rw [this]
  rw [integral_const_mul, h, one_div, inv_rpow hΦ.le, ← rpow_neg hΦ.le]
  rw [show Φtot * (Φtot ^ (-(1 + (1 - σ) / θ)) * Real.Gamma (1 + (1 - σ) / θ)) =
      Real.Gamma (1 + (1 - σ) / θ) * (Φtot ^ (1 : ℝ) * Φtot ^ (-(1 + (1 - σ) / θ))) by
    rw [rpow_one]; ring, ← rpow_add hΦ]
  congr 2
  ring

/-- **Fréchet to exponential.** If `P(Z ≤ s) = exp(−T s^{−θ})` then the price
`p = c/Z` satisfies `P(p > q) = P(Z < c/q) = exp(−T (c/q)^{−θ}) = exp(−Φ q^θ)`
with `Φ = T c^{−θ}`, so `U = p^θ` is exponential with rate `Φ`. -/
theorem frechet_to_exp {T c q θ : ℝ} (hc : 0 < c) (hq : 0 < q) :
    T * (c / q) ^ (-θ) = T * c ^ (-θ) * q ^ θ := by
  rw [div_rpow hc.le hq.le, rpow_neg hq.le θ, div_inv_eq_mul]
  ring

/-- The CES price index `P = (E p^{1−σ})^{1/(1−σ)}` when `p^θ` is exponential
with rate `Φ`. -/
def priceIndex (θ σ Φtot : ℝ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), u ^ ((1 - σ) / θ) * (Φtot * Real.exp (-(Φtot * u)))) ^ (1 / (1 - σ))

/-- The constant `γ = Γ(1 + (1 − σ)/θ)^{1/(1−σ)}`. -/
def gammaConst (θ σ : ℝ) : ℝ := Real.Gamma (1 + (1 - σ) / θ) ^ (1 / (1 - σ))

theorem gammaConst_pos {θ σ : ℝ} (hθ : 0 < θ) (hσ : σ < 1 + θ) : 0 < gammaConst θ σ := by
  have ha : 0 < 1 + (1 - σ) / θ := by
    have : -1 < (1 - σ) / θ := by rw [lt_div_iff₀ hθ]; linarith
    linarith
  exact rpow_pos_of_pos (Real.Gamma_pos_of_pos ha) _

/-- **The Eaton–Kortum price index**: `P = γ Φ^{−1/θ}`. -/
theorem priceIndex_eq {θ σ Φtot : ℝ} (hθ : 0 < θ) (hσ : σ < 1 + θ) (hσ1 : σ ≠ 1)
    (hΦ : 0 < Φtot) :
    priceIndex θ σ Φtot = gammaConst θ σ * Φtot ^ (-1 / θ) := by
  have ha : 0 < 1 + (1 - σ) / θ := by
    have : -1 < (1 - σ) / θ := by rw [lt_div_iff₀ hθ]; linarith
    linarith
  rw [priceIndex, price_moment hθ hσ hΦ, gammaConst,
    mul_rpow (Real.Gamma_pos_of_pos ha).le (rpow_nonneg hΦ.le _), ← rpow_mul hΦ.le]
  congr 2
  have : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ1)
  field_simp
  ring

theorem real_wage_aux {θ T w Φn γ : ℝ} (hθ : 0 < θ) (hT : 0 < T) (hw : 0 < w) (hΦ : 0 < Φn)
    (hγ : 0 < γ) :
    w / (γ * Φn ^ (-1 / θ)) = γ⁻¹ * (T / (T * w ^ (-θ) / Φn)) ^ (1 / θ) := by
  have hwθ : 0 < w ^ (-θ) := rpow_pos_of_pos hw _
  have e1 : T / (T * w ^ (-θ) / Φn) = Φn * w ^ θ := by
    rw [rpow_neg hw.le]; field_simp
  rw [e1, mul_rpow hΦ.le (rpow_nonneg hw.le _), ← rpow_mul hw.le, mul_one_div_cancel hθ.ne',
    rpow_one, neg_div, rpow_neg hΦ.le, one_div]
  field_simp

omit [DecidableEq ι] in
/-- **Welfare and the domestic trade share (ACR).** Destination `n ∈ s` buys
from sources with `Φ_k = T_k (w_k d_k)^{−θ}`, with no internal trade cost
`d_n = 1`. With the trade share `π_nn = Φ_n/Σ_k Φ_k` (`trade_share`) and the
price index `P_n` (`priceIndex_eq`), the real wage is
`w_n/P_n = γ^{−1} (T_n/π_nn)^{1/θ}`. -/
theorem real_wage {θ σ : ℝ} (hθ : 0 < θ) (hσ : σ < 1 + θ) (hσ1 : σ ≠ 1) (T w d : ι → ℝ)
    (hT : ∀ k ∈ s, 0 < T k) (hw : ∀ k ∈ s, 0 < w k) (hd : ∀ k ∈ s, 0 < d k) {n : ι}
    (hn : n ∈ s) (hdn : d n = 1) :
    w n / priceIndex θ σ (∑ k ∈ s, T k * (w k * d k) ^ (-θ)) =
      (gammaConst θ σ)⁻¹ *
        (T n / (T n * (w n * d n) ^ (-θ) / ∑ k ∈ s, T k * (w k * d k) ^ (-θ))) ^ (1 / θ) := by
  have hΦ : 0 < ∑ k ∈ s, T k * (w k * d k) ^ (-θ) :=
    Finset.sum_pos (fun k hk => mul_pos (hT k hk) (rpow_pos_of_pos (mul_pos (hw k hk) (hd k hk)) _))
      ⟨n, hn⟩
  rw [priceIndex_eq hθ hσ hσ1 hΦ, hdn, mul_one]
  exact real_wage_aux hθ (hT n hn) (hw n hn) hΦ (gammaConst_pos hθ hσ)

end EatonKortum
end Econ

end
