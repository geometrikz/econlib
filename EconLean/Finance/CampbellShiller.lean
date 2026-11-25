/-
# The Campbell–Shiller present-value identity and return predictability

Campbell and Shiller (1988), "The Dividend-Price Ratio and Expectations of
Future Dividends and Discount Factors", RFS; Cochrane (2008), "The Dog That
Did Not Bark", RFS; Cochrane, *Asset Pricing*, §20.1.

**Setting.** Log-linearizing the definition of the return around the mean
log price–dividend ratio gives the (approximate, here exact by assumption)
**Campbell–Shiller identity** `r_{t+1} = k + ρ pd_{t+1} + Δd_{t+1} − pd_t`
(`Identity`), with `ρ ∈ [0, 1)` (in the approximation `ρ ∈ (0, 1)` and `k`
is a function of `ρ`; here `k` is a free constant), `pd` the log
price–dividend ratio, `Δd` log dividend growth and `r` the log return.

**Results.**
* `pd_hasSum`, `pd_eq`: if `pd` and `Δd` are bounded (no rational
  bubble; returns are then bounded too, `bdd_r`), then `pd_t = k/(1 − ρ) + Σ_j ρ^j Δd_{t+1+j} − Σ_j ρ^j r_{t+1+j}`:
  a high price–dividend ratio must be followed by high dividend growth or
  low returns.
* `var_decomp`: across states of the world at a fixed date (a finite
  probability space, `IsProb`),
  `Var(pd_t) = Cov(pd_t, Σ ρ^j Δd) − Cov(pd_t, Σ ρ^j r)`: variation in the
  price–dividend ratio is entirely accounted for by forecasts of long-run
  dividend growth and returns. In regression form, `b_d^{lr} − b_r^{lr} = 1`
  in `pd` units (Cochrane writes `b_r^{lr} − b_d^{lr} = 1` for `dp`, with
  time-series rather than cross-state moments).
* `returns_predictable` (a corollary): if long-run dividend growth is unforecastable by
  `pd_t` (zero covariance) and `pd_t` varies, then `pd_t` forecasts long-run
  returns with a negative covariance equal to `−Var(pd_t)`.

**Deviations.** The log-linear identity is taken as exact (its derivation
is a first-order approximation); the probability space is finite and the
whole path is bounded state by state; the covariances are with long-run
sums rather than regression coefficients on one-period variables.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace CampbellShiller

open Filter Topology Finset

/-- The Campbell–Shiller log-linear return identity along a path. -/
def Identity (k ρ : ℝ) (pd dd r : ℕ → ℝ) : Prop :=
  ∀ t, r (t + 1) = k + ρ * pd (t + 1) + dd (t + 1) - pd t

/-- A path is bounded. -/
def Bdd (x : ℕ → ℝ) : Prop := ∃ M, ∀ t, |x t| ≤ M

theorem summable_of_bdd {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {x : ℕ → ℝ} (hx : Bdd x) (t : ℕ) :
    Summable fun j => ρ ^ j * x (t + 1 + j) := by
  obtain ⟨M, hM⟩ := hx
  refine Summable.of_norm_bounded (g := fun j => M * ρ ^ j)
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left M) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 j), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM _) (pow_nonneg hρ0 j)

/-- Bounded prices and dividend growth give bounded returns. -/
theorem bdd_r {k ρ : ℝ} {pd dd r : ℕ → ℝ} (h : Identity k ρ pd dd r) (hpd : Bdd pd)
    (hdd : Bdd dd) : Bdd r := by
  obtain ⟨M₁, h₁⟩ := hpd
  obtain ⟨M₂, h₂⟩ := hdd
  refine ⟨max |r 0| (|k| + |ρ| * M₁ + M₂ + M₁), fun t => ?_⟩
  rcases t with _ | t
  · exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    rw [h t]
    have e1 := abs_sub (k + ρ * pd (t + 1) + dd (t + 1)) (pd t)
    have e2 := abs_add_le (k + ρ * pd (t + 1)) (dd (t + 1))
    have e3 := abs_add_le k (ρ * pd (t + 1))
    have e4 : |ρ * pd (t + 1)| ≤ |ρ| * M₁ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₁ _) (abs_nonneg _)
    linarith [h₁ t, h₂ (t + 1)]

/-- **The present-value identity** (as a sum). -/
theorem pd_hasSum {k ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {pd dd r : ℕ → ℝ}
    (h : Identity k ρ pd dd r) (hpd : Bdd pd) (hdd : Bdd dd) (t : ℕ) :
    HasSum (fun j => ρ ^ j * (k + dd (t + 1 + j) - r (t + 1 + j))) (pd t) := by
  -- iterate `n` times
  have iter : ∀ n, pd t = ∑ j ∈ range n, ρ ^ j * (k + dd (t + 1 + j) - r (t + 1 + j)) +
      ρ ^ n * pd (t + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, sum_range_succ]
      have := h (t + n)
      rw [show t + n + 1 = t + 1 + n by ring] at this
      rw [show t + (n + 1) = t + 1 + n by ring, pow_succ]
      linear_combination (ρ ^ n) * this
  have hsum : Summable fun j => ρ ^ j * (k + dd (t + 1 + j) - r (t + 1 + j)) := by
    have hk : Bdd fun s => k + dd s - r s := by
      obtain ⟨M₁, h₁⟩ := hdd
      obtain ⟨M₂, h₂⟩ := bdd_r h ⟨_, (Classical.choose_spec hpd)⟩ ⟨M₁, h₁⟩
      exact ⟨|k| + M₁ + M₂, fun s => by
        have := abs_sub (k + dd s) (r s)
        have := abs_add_le k (dd s)
        linarith [h₁ s, h₂ s]⟩
    exact summable_of_bdd hρ0 hρ1 hk t
  rw [hsum.hasSum_iff_tendsto_nat]
  obtain ⟨M, hM⟩ := hpd
  have hrem : Tendsto (fun n => ρ ^ n * pd (t + n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => M * ρ ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul M
    apply squeeze_zero_norm _ hg
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 n), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (pow_nonneg hρ0 n)
  have : Tendsto (fun n => pd t - ρ ^ n * pd (t + n)) atTop (𝓝 (pd t - 0)) :=
    tendsto_const_nhds.sub hrem
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  rw [iter n]; ring

/-- **The present-value identity**:
`pd_t = k/(1 − ρ) + Σ ρ^j Δd_{t+1+j} − Σ ρ^j r_{t+1+j}`. -/
theorem pd_eq {k ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {pd dd r : ℕ → ℝ}
    (h : Identity k ρ pd dd r) (hpd : Bdd pd) (hdd : Bdd dd) (t : ℕ) :
    pd t = k / (1 - ρ) + ∑' j, ρ ^ j * dd (t + 1 + j) - ∑' j, ρ ^ j * r (t + 1 + j) := by
  have h1 := pd_hasSum hρ0 hρ1 h hpd hdd t
  have hr := bdd_r h hpd hdd
  have hk : HasSum (fun j : ℕ => ρ ^ j * k) (k / (1 - ρ)) := by
    have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right k
    simpa [div_eq_mul_inv, mul_comm] using this
  have h2 := (hk.add (summable_of_bdd hρ0 hρ1 hdd t).hasSum).sub
    (summable_of_bdd hρ0 hρ1 hr t).hasSum
  refine h1.unique ?_
  convert h2 using 1
  funext j; ring

/-! ### Variance decomposition across states -/

variable {Ω : Type*} [Fintype Ω]

/-- Probability weights. -/
def IsProb (p : Ω → ℝ) : Prop := (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1

/-- Mean under probabilities `p`. -/
def mean (p : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, p ω * X ω

/-- Covariance under probabilities `p`. -/
def cov (p : Ω → ℝ) (X Y : Ω → ℝ) : ℝ := mean p (fun ω => (X ω - mean p X) * (Y ω - mean p Y))

theorem cov_eq (p : Ω → ℝ) (hp : ∑ ω, p ω = 1) (X Y : Ω → ℝ) :
    cov p X Y = mean p (fun ω => X ω * Y ω) - mean p X * mean p Y := by
  simp only [cov, mean]
  have e : ∀ ω, p ω * ((X ω - ∑ ω, p ω * X ω) * (Y ω - ∑ ω, p ω * Y ω)) =
      p ω * (X ω * Y ω) - (∑ ω, p ω * Y ω) * (p ω * X ω) - (∑ ω, p ω * X ω) * (p ω * Y ω) +
      (∑ ω, p ω * X ω) * (∑ ω, p ω * Y ω) * p ω := fun ω => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hp]
  ring

/-- **Variance decomposition of the price–dividend ratio.** State by state
(`ω`), paths satisfy the identity and are bounded; then the variance of
`pd_t` equals its covariance with long-run dividend growth minus its
covariance with long-run returns. -/
theorem var_decomp {k ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (p : Ω → ℝ) (hp : IsProb p)
    {pd dd r : Ω → ℕ → ℝ} (h : ∀ ω, Identity k ρ (pd ω) (dd ω) (r ω))
    (hpd : ∀ ω, Bdd (pd ω)) (hdd : ∀ ω, Bdd (dd ω)) (t : ℕ) :
    cov p (fun ω => pd ω t) (fun ω => pd ω t) =
      cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * dd ω (t + 1 + j)) -
        cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * r ω (t + 1 + j)) := by
  set X := fun ω => pd ω t
  set G := fun ω => ∑' j, ρ ^ j * dd ω (t + 1 + j)
  set Rr := fun ω => ∑' j, ρ ^ j * r ω (t + 1 + j)
  have hX : ∀ ω, X ω = k / (1 - ρ) + G ω - Rr ω := fun ω =>
    pd_eq hρ0 hρ1 (h ω) (hpd ω) (hdd ω) t
  have hmX : mean p X = k / (1 - ρ) + mean p G - mean p Rr := by
    simp only [mean, hX, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, ← sum_mul, hp.2,
      one_mul]
  simp only [cov, mean] at hmX ⊢
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun ω _ => ?_
  rw [hX ω, hmX]
  ring

/-- **Returns must be predictable.** If `pd_t` does not forecast long-run
dividend growth, it forecasts long-run returns, with covariance `−Var(pd_t)`,
strictly negative whenever `pd_t` varies. -/
theorem returns_predictable {k ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (p : Ω → ℝ)
    (hp : IsProb p) {pd dd r : Ω → ℕ → ℝ} (h : ∀ ω, Identity k ρ (pd ω) (dd ω) (r ω))
    (hpd : ∀ ω, Bdd (pd ω)) (hdd : ∀ ω, Bdd (dd ω)) (t : ℕ)
    (hg : cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * dd ω (t + 1 + j)) = 0)
    (hvar : 0 < cov p (fun ω => pd ω t) (fun ω => pd ω t)) :
    cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * r ω (t + 1 + j)) =
        -cov p (fun ω => pd ω t) (fun ω => pd ω t) ∧
      cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * r ω (t + 1 + j)) < 0 := by
  have := var_decomp hρ0 hρ1 p hp h hpd hdd t
  rw [hg] at this
  constructor <;> linarith

end CampbellShiller
end Econ

end
