/-
# The granular origins of aggregate fluctuations

Gabaix (2011), "The Granular Origins of Aggregate Fluctuations",
Econometrica; Carvalho–Gabaix (2013), AER.

**Setting.** `N` firms with sales shares `s_i` (summing to one) receive
productivity shocks `ε_i` that are mean zero, uncorrelated, with common
variance `σ²` (on a finite probability space, `Econ.CAPM.Prob`). Aggregate
(GDP) growth is the share-weighted sum `Σ s_i ε_i` (Hulten's theorem).

**Results.**
* `var_agg`: aggregate volatility is `σ_GDP = σ h` with
  `h² = Σ s_i²` the sales Herfindahl index.
* `herfindahl_ge`: `h² ≥ 1/N`, with equality for equal shares
  (`herfindahl_equal`): with many small firms, volatility vanishes like
  `σ/√N` (the diversification argument).
* `granular_bound`: but for any firm `k`, `Var(GDP) ≥ σ² s_k²`: if the
  largest firm's share does not vanish (a fat-tailed size distribution),
  aggregate volatility does not vanish however many firms there are.

* `var_equal`: with equal shares `Var(GDP) = σ²/N`.
* `zipf_herfindahl`, `var_zipf_ge`: with Zipf shares `s_i ∝ 1/i`,
  `h² ≥ 1/(1 + log N)²`, so `Var(GDP) ≥ σ²/(1 + log N)²`: volatility decays
  only like `σ/log N` (Gabaix's key rate), not `σ/√N`.
* `zipf_herfindahl_le`, `var_zipf_le`: conversely `h² ≤ 2/(log(N + 1))²`,
  so under Zipf's law `h` is of exact order `1/log N`.

**Deviations.** Shares are normalized to sum to one; Gabaix's Domar weights
(sales/GDP) sum to more than one, which only strengthens the lower bounds.
Volatility bounds are stated for a given `N`; the asymptotic `∼` form is
not stated as a limit.
-/
module

public import EconLean.Finance.CAPM
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

noncomputable section

namespace Econ
namespace Granular

open Finset

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] (P : Econ.CAPM.Prob σ)

/-- Aggregate growth. -/
def agg (s : ι → ℝ) (ε : ι → σ → ℝ) : σ → ℝ := fun ω => ∑ i, s i * ε i ω

omit [DecidableEq ι] in
theorem E_agg (s : ι → ℝ) (ε : ι → σ → ℝ) : P.E (agg s ε) = ∑ i, s i * P.E (ε i) := by
  simp only [Econ.CAPM.Prob.E, agg, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun ω _ => by ring

/-- **Aggregate variance with uncorrelated shocks.** -/
theorem var_agg (s : ι → ℝ) (ε : ι → σ → ℝ) {v : ℝ} (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    P.Var (agg s ε) = v * ∑ i, s i ^ 2 := by
  have hE : P.E (agg s ε) = 0 := by simp [E_agg P, hmean]
  simp only [Econ.CAPM.Prob.Var, Econ.CAPM.Prob.Cov, hE, mul_zero, sub_zero]
  have : P.E (fun ω => agg s ε ω * agg s ε ω) =
      ∑ i, ∑ j, s i * s j * P.E (fun ω => ε i ω * ε j ω) := by
    simp only [Econ.CAPM.Prob.E, agg, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun ω _ => by ring
  rw [this]
  simp only [hcov, mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] in
/-- **Herfindahl bound**: `Σ s² ≥ 1/N`. -/
theorem herfindahl_ge (s : ι → ℝ) (h1 : ∑ i, s i = 1) :
    1 / (Fintype.card ι : ℝ) ≤ ∑ i, s i ^ 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := s)
  rw [h1, one_pow, card_univ] at hcs
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)).eq_or_lt with h | h
  · rw [← h]; simp; positivity
  · rw [div_le_iff₀ h]; linarith

omit [DecidableEq ι] in
/-- Equal shares attain the bound: `h² = 1/N`. -/
theorem herfindahl_equal [Nonempty ι] :
    ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) ^ 2 = 1 / (Fintype.card ι : ℝ) := by
  have : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Fintype ι] in
/-- The common variance is nonnegative. -/
theorem v_nonneg (ε : ι → σ → ℝ) {v : ℝ}
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) (k : ι) : 0 ≤ v := by
  have := hcov k k
  simp only [↓reduceIte] at this
  rw [← this]
  exact sum_nonneg fun ω _ => mul_nonneg (P.pos ω).le (mul_self_nonneg _)

/-- **The granular bound.** Aggregate variance is at least `σ² s_k²` for
every firm `k`. -/
theorem granular_bound (s : ι → ℝ) (ε : ι → σ → ℝ) {v : ℝ}
    (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0)
    (k : ι) : v * s k ^ 2 ≤ P.Var (agg s ε) := by
  have hv := v_nonneg P ε hcov k
  rw [var_agg P s ε hmean hcov]
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (f := fun i => s i ^ 2) (fun i _ => sq_nonneg _) (mem_univ k)) hv

/-! ### Equal shares versus a Zipf size distribution -/

/-- **Diversification with equal shares**: `Var(GDP) = σ²/N`. -/
theorem var_equal {N : ℕ} (hN : 0 < N) (ε : Fin N → σ → ℝ) {v : ℝ}
    (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    P.Var (agg (fun _ => 1 / (N : ℝ)) ε) = v / N := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [var_agg P _ ε hmean hcov, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Zipf shares: firm `i` (ranked `i + 1`) has share proportional to
`1/(i + 1)`, normalized by the harmonic number `H_N`. -/
def zipf (N : ℕ) (i : Fin N) : ℝ := 1 / ((i : ℝ) + 1) / (harmonic N : ℝ)

theorem harmonic_eq_sum (N : ℕ) : (harmonic N : ℝ) = ∑ i : Fin N, 1 / ((i : ℝ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / ((i : ℝ) + 1)), harmonic]
  push_cast
  exact sum_congr rfl fun i _ => by rw [one_div]

theorem harmonic_pos {N : ℕ} (hN : 0 < N) : (0 : ℝ) < harmonic N := by
  rw [harmonic_eq_sum]
  exact sum_pos (fun i _ => by positivity) ⟨⟨0, hN⟩, mem_univ _⟩

theorem zipf_sum {N : ℕ} (hN : 0 < N) : ∑ i, zipf N i = 1 := by
  simp only [zipf, ← sum_div, ← harmonic_eq_sum]
  exact div_self (harmonic_pos hN).ne'

/-- **Zipf Herfindahl**: `h² ≥ 1/(1 + log N)²`, decaying only like `1/(log N)²`
rather than `1/N`. -/
theorem zipf_herfindahl {N : ℕ} (hN : 0 < N) :
    1 / (1 + Real.log N) ^ 2 ≤ ∑ i, zipf N i ^ 2 := by
  have hH := harmonic_pos hN
  have hle : (harmonic N : ℝ) ≤ 1 + Real.log N := by exact_mod_cast harmonic_le_one_add_log N
  have h0 : zipf N ⟨0, hN⟩ = 1 / (harmonic N : ℝ) := by simp [zipf]
  calc 1 / (1 + Real.log N) ^ 2 ≤ 1 / (harmonic N : ℝ) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hH.le hle 2)
    _ = zipf N ⟨0, hN⟩ ^ 2 := by rw [h0, div_pow, one_pow]
    _ ≤ ∑ i, zipf N i ^ 2 :=
        single_le_sum (f := fun i => zipf N i ^ 2) (fun i _ => sq_nonneg _) (mem_univ _)

/-- **Granular volatility under Zipf's law**: `Var(GDP) ≥ σ²/(1 + log N)²`,
so aggregate volatility decays like `σ/log N`, not `σ/√N`. -/
theorem var_zipf_ge {N : ℕ} (hN : 0 < N) (ε : Fin N → σ → ℝ) {v : ℝ}
    (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    v / (1 + Real.log N) ^ 2 ≤ P.Var (agg (zipf N) ε) := by
  have hv := v_nonneg P ε hcov ⟨0, hN⟩
  rw [var_agg P _ ε hmean hcov, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (zipf_herfindahl hN) hv

theorem sum_inv_sq_le (N : ℕ) : ∑ i ∈ range N, (1 / ((i : ℝ) + 1)) ^ 2 ≤ 2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : (0 : ℝ) < n + 1 := by positivity
    have key : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ h1.ne' (by positivity), div_pow, one_pow, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith

/-- **Zipf Herfindahl, upper bound**: `h² ≤ 2/(log(N + 1))²`. Together with
`zipf_herfindahl`, `h ≍ 1/log N`. -/
theorem zipf_herfindahl_le {N : ℕ} (hN : 0 < N) :
    ∑ i, zipf N i ^ 2 ≤ 2 / Real.log (N + 1) ^ 2 := by
  have hH := harmonic_pos hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N + 1) := Real.log_pos (by linarith)
  have hle : Real.log (N + 1) ≤ (harmonic N : ℝ) := by
    have := log_add_one_le_harmonic N; push_cast at this ⊢; exact_mod_cast this
  have hs : ∑ i : Fin N, (1 / ((i : ℝ) + 1)) ^ 2 ≤ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (1 / ((i : ℝ) + 1)) ^ 2)]
    have := sum_inv_sq_le N
    have : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
    linarith
  calc ∑ i, zipf N i ^ 2 = (∑ i : Fin N, (1 / ((i : ℝ) + 1)) ^ 2) / (harmonic N : ℝ) ^ 2 := by
        simp only [zipf, div_pow, ← sum_div]
    _ ≤ 2 / (harmonic N : ℝ) ^ 2 := div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ 2 / Real.log (N + 1) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlog.le hle 2)

/-- **Zipf volatility, upper bound**: `Var(GDP) ≤ 2σ²/(log(N + 1))²`. -/
theorem var_zipf_le {N : ℕ} (hN : 0 < N) (ε : Fin N → σ → ℝ) {v : ℝ}
    (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    P.Var (agg (zipf N) ε) ≤ 2 * v / Real.log (N + 1) ^ 2 := by
  have hv := v_nonneg P ε hcov ⟨0, hN⟩
  rw [var_agg P _ ε hmean hcov, mul_comm 2 v, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (zipf_herfindahl_le hN) hv

end Granular
end Econ

end
