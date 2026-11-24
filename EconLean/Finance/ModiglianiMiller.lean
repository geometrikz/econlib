/-
# The Modigliani–Miller theorems

Modigliani and Miller (1958), "The Cost of Capital, Corporation Finance and
the Theory of Investment", AER; Stiglitz (1969); Duffie, *Dynamic Asset
Pricing Theory*, §1.F; Berk–DeMarzo, *Corporate Finance*, ch. 14.

**Setting.** Finitely many states `s`; a firm's operating cash flow is
`X_s`. Financial claims are state-contingent payoffs, valued by a strictly
positive state-price vector `m` (`value z = Σ_s m_s z_s`). By the
fundamental theorem of asset pricing (`Econ.AssetPricing.Market.ftap`), such
`m` exists whenever the securities market admits no arbitrage.

**Results.**
* `mm_I`: **capital-structure irrelevance**: whatever claims `d`, `e` split
  the cash flow (`d + e = X`), the total value of the firm is the value of
  `X`. In particular, for debt with face value `F`
  (`debt = min(X, F)`, `equity = max(X − F, 0)`) firm value does not depend
  on `F` (`mm_I_debt`).
* `mm_I_market`: in a securities market with no arbitrage, if the cash flow
  and both claims are traded, the cost of the claims adds up to the cost of
  the cash flow.
* `mm_II`: for debt of any riskiness, expected returns under any probability
  weights satisfy `r_E = r_A + (r_A − r_D) D/E`, with `r_D` the expected
  return on debt: the expected return on equity rises linearly with leverage
  `D/E`; `mm_II_mono`: strictly when `r_A > r_D`.

**Deviations.** Limited liability (`X ≥ 0`, `F ≥ 0`) is not imposed (the
identities do not need it). No taxes, bankruptcy costs or agency costs (the frictions
that break MM); one period.
-/
module

public import EconLean.Finance.AssetPricing

@[expose] public section

noncomputable section

namespace Econ
namespace MM

open Finset

variable {σ : Type*} [Fintype σ]

/-- Value of a state-contingent payoff at state prices `m`. -/
def value (m z : σ → ℝ) : ℝ := ∑ s, m s * z s

/-- Debt with face value `F`. -/
def debt (F : ℝ) (X : σ → ℝ) : σ → ℝ := fun s => min (X s) F

/-- Levered equity. -/
def equity (F : ℝ) (X : σ → ℝ) : σ → ℝ := fun s => max (X s - F) 0

/-- **MM I as an accounting identity**: valuation is linear, so any split of
the cash flow is worth the cash flow. The economic content (that claims are
priced by a common state-price vector, which no arbitrage guarantees) is in
`mm_I_market`. -/
theorem mm_I (m X d e : σ → ℝ) (hsplit : ∀ s, d s + e s = X s) :
    value m d + value m e = value m X := by
  simp only [value, ← sum_add_distrib, ← mul_add, hsplit]

omit [Fintype σ] in
theorem debt_add_equity (F : ℝ) (X : σ → ℝ) (s : σ) : debt F X s + equity F X s = X s := by
  simp only [debt, equity]
  rcases le_total (X s) F with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

/-- Firm value does not depend on the face value of debt. -/
theorem mm_I_debt (m X : σ → ℝ) (F F' : ℝ) :
    value m (debt F X) + value m (equity F X) = value m (debt F' X) + value m (equity F' X) := by
  rw [mm_I m X _ _ (debt_add_equity F X), mm_I m X _ _ (debt_add_equity F' X)]

/-- **MM I in a securities market.** With no arbitrage, if portfolios `hX`,
`hd`, `he` deliver the cash flow and two claims that split it, their costs
add up. -/
theorem mm_I_market {ι : Type*} [Fintype ι] (M : Econ.AssetPricing.Market σ ι)
    (hna : M.NoArbitrage) (hX hd he : ι → ℝ)
    (hsplit : ∀ s, M.payoff hd s + M.payoff he s = M.payoff hX s) :
    M.cost hd + M.cost he = M.cost hX := by
  obtain ⟨m, hm⟩ := M.ftap.1 hna
  rw [M.cost_eq hm, M.cost_eq hm, M.cost_eq hm]
  exact mm_I m _ _ _ hsplit

/-- **MM II** (Berk–DeMarzo form). Let `π` be probability weights, `V`, `D`,
`E` the values of the firm, its (possibly risky) debt and its equity
(`V = D + E` by MM I). With expected returns `r_A = E_π[X]/V`,
`r_D = E_π[min(X, F)]/D`, `r_E = E_π[max(X − F, 0)]/E`,
`r_E = r_A + (r_A − r_D) D/E`. -/
theorem mm_II (m X π : σ → ℝ) (F : ℝ) (hD : value m (debt F X) ≠ 0)
    (hE : value m (equity F X) ≠ 0) (hV : value m X ≠ 0) :
    (∑ s, π s * equity F X s) / value m (equity F X) =
      (∑ s, π s * X s) / value m X +
        ((∑ s, π s * X s) / value m X - (∑ s, π s * debt F X s) / value m (debt F X)) *
          (value m (debt F X) / value m (equity F X)) := by
  have hV' : value m X = value m (debt F X) + value m (equity F X) :=
    (mm_I m X _ _ (debt_add_equity F X)).symm
  have hsum : ∑ s, π s * equity F X s = ∑ s, π s * X s - ∑ s, π s * debt F X s := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun s _ => by rw [← debt_add_equity F X s]; ring
  rw [hsum, hV']
  rw [hV'] at hV
  field_simp
  ring

/-- **Leverage raises the expected return on equity**: holding `r_A > r_D`
fixed, the MM II equity return `r_A + (r_A − r_D) D/E` is strictly increasing
in leverage `D/E`. -/
theorem mm_II_mono {rA rD ℓ ℓ' : ℝ} (h : rD < rA) (hℓ : ℓ < ℓ') :
    rA + (rA - rD) * ℓ < rA + (rA - rD) * ℓ' := by
  nlinarith

end MM
end Econ

end
