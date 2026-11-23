/-
# The AK model of endogenous growth

Acemoglu, *Introduction to Modern Economic Growth*, ch. 11; Barro–Sala-i-Martin
ch. 4; Rebelo (1991).

With output `Y = A K`, the return to capital never falls, so growth does not
die out as in Solow.

**Solow-style AK** (`kpath`): with a constant saving rate `s` and depreciation
`δ`, `K_{t+1} = s A K_t + (1 − δ) K_t`. Capital grows at the constant rate
`sA − δ` from any starting point (`growthRate_eq`): there are no transitional
dynamics and no convergence. With `sA > δ` capital grows without bound
(`tendsto_atTop`).

**Optimal saving** (`Plan`, `optimal_finite`, `optimal`). A planner with log
utility and discount factor `β ∈ (0,1)` chooses consumption `c_t > 0` subject to
`k_{t+1} = R k_t − c_t ≥ 0`, where `R = 1 + A − δ > 0` is the gross return. The
optimum consumes the constant fraction `1 − β` of wealth `R k_t`:
`c*_t = (1 − β) R (βR)^t k₀`, so consumption, capital and output all grow at
the gross rate `βR` forever (`cstar_succ`, `kstar_succ`). The growth rate is
positive iff `β (1 + A − δ) > 1`.

**The Lean.** `optimal_finite` is a finite-horizon verification inequality:
for any feasible plan and horizon `T`,
`Σ_{t<T} βᵗ log c_t ≤ Σ_{t<T} βᵗ log c*_t + β^T/(1 − β)`. It uses
`log x ≤ log y + (x − y)/y` and the present-value budget
`Σ_{t<T} c_t / R^{t+1} = k₀ − k_T / R^T`. Letting `T → ∞` gives `optimal`.

**Deviations.** Log utility (CRRA with `σ = 1`); discrete time. `optimal`
compares plans whose lifetime utility converges (`HasSum`). This is harmless:
`k_t ≥ 0` forces `c_t ≤ R^{t+1} k₀`, so the positive part always converges and
a plan without a sum has utility `−∞`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

noncomputable section

namespace Econ
namespace AK

open Filter Topology Real Finset

/-! ## Solow-style AK -/

/-- Capital under a constant saving rate: `K_{t+1} = s A K_t + (1 − δ) K_t`. -/
def kpath (s A δ k₀ : ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => s * A * kpath s A δ k₀ t + (1 - δ) * kpath s A δ k₀ t

theorem kpath_eq (s A δ k₀ : ℝ) (t : ℕ) : kpath s A δ k₀ t = (1 + s * A - δ) ^ t * k₀ := by
  induction t with
  | zero => show k₀ = _; ring
  | succ t ih => simp only [kpath, ih, pow_succ]; ring

/-- **Constant growth, no transitional dynamics:** the growth rate of capital
is `sA − δ` in every period, whatever the capital stock. -/
theorem growthRate_eq (s A δ k₀ : ℝ) (t : ℕ) (hk : kpath s A δ k₀ t ≠ 0) :
    (kpath s A δ k₀ (t + 1) - kpath s A δ k₀ t) / kpath s A δ k₀ t = s * A - δ := by
  rw [div_eq_iff hk]; rw [show kpath s A δ k₀ (t + 1) = s * A * kpath s A δ k₀ t + (1 - δ) * kpath s A δ k₀ t from rfl]; ring

/-- **Sustained growth:** if `sA > δ`, capital grows without bound. -/
theorem tendsto_atTop {s A δ k₀ : ℝ} (hk : 0 < k₀) (h : δ < s * A) :
    Tendsto (kpath s A δ k₀) atTop atTop := by
  have h1 : 1 < 1 + s * A - δ := by linarith
  have e : kpath s A δ k₀ = fun t => (1 + s * A - δ) ^ t * k₀ := funext (kpath_eq s A δ k₀)
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const hk

/-! ## Optimal saving with log utility -/

/-- A feasible consumption plan from capital `k₀` with gross return `R`. -/
structure Plan (R k₀ : ℝ) where
  c : ℕ → ℝ
  k : ℕ → ℝ
  k_zero : k 0 = k₀
  law : ∀ t, k (t + 1) = R * k t - c t
  c_pos : ∀ t, 0 < c t
  k_nonneg : ∀ t, 0 ≤ k t

/-- Optimal capital `k*_t = (βR)^t k₀`. -/
def kstar (β R k₀ : ℝ) (t : ℕ) : ℝ := (β * R) ^ t * k₀

/-- Optimal consumption `c*_t = (1 − β) R k*_t`. -/
def cstar (β R k₀ : ℝ) (t : ℕ) : ℝ := (1 - β) * R * kstar β R k₀ t

/-- The optimal plan is feasible. -/
def optPlan {β R k₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hR : 0 < R) (hk : 0 < k₀) : Plan R k₀ where
  c := cstar β R k₀
  k := kstar β R k₀
  k_zero := by simp [kstar]
  law t := by simp only [cstar, kstar, pow_succ]; ring
  c_pos t := by
    have : 0 < 1 - β := by linarith
    unfold cstar kstar; positivity
  k_nonneg t := by unfold kstar; positivity

/-- Consumption grows at the gross rate `βR`. -/
theorem cstar_succ (β R k₀ : ℝ) (t : ℕ) : cstar β R k₀ (t + 1) = β * R * cstar β R k₀ t := by
  simp only [cstar, kstar, pow_succ]; ring

/-- Capital (and so output `A k`) grows at the gross rate `βR`. -/
theorem kstar_succ (β R k₀ : ℝ) (t : ℕ) : kstar β R k₀ (t + 1) = β * R * kstar β R k₀ t := by
  simp only [kstar, pow_succ]; ring

/-- The present-value budget: `Σ_{t<T} c_t / R^{t+1} = k₀ − k_T / R^T`. -/
theorem pv_budget {R k₀ : ℝ} (hR : 0 < R) (P : Plan R k₀) (T : ℕ) :
    ∑ t ∈ range T, P.c t / R ^ (t + 1) = k₀ - P.k T / R ^ T := by
  induction T with
  | zero => simp [P.k_zero]
  | succ T ih =>
    rw [sum_range_succ, ih, P.law T]
    have : R ^ T ≠ 0 := (pow_pos hR T).ne'
    field_simp
    ring

/-- **Finite-horizon verification.** For any feasible plan and any `T`,
`Σ_{t<T} βᵗ log c_t ≤ Σ_{t<T} βᵗ log c*_t + β^T/(1 − β)`. -/
theorem optimal_finite {β R k₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hR : 0 < R) (hk : 0 < k₀)
    (P : Plan R k₀) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * log (P.c t) ≤
      ∑ t ∈ range T, β ^ t * log (cstar β R k₀ t) + β ^ T / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith
  set P' := optPlan hβ₀ hβ₁ hR hk
  -- `βᵗ / c*_t = 1/((1 − β) k₀ R^{t+1})`
  have hw : ∀ t, β ^ t / cstar β R k₀ t = 1 / ((1 - β) * k₀) * (1 / R ^ (t + 1)) := fun t => by
    have : 0 < β ^ t := pow_pos hβ₀ t
    simp only [cstar, kstar, mul_pow, pow_succ]
    field_simp
  -- pointwise: `βᵗ log c ≤ βᵗ log c* + βᵗ (c − c*)/c*`
  have hpt : ∀ t, β ^ t * log (P.c t) ≤ β ^ t * log (cstar β R k₀ t) +
      1 / ((1 - β) * k₀) * (P.c t / R ^ (t + 1) - cstar β R k₀ t / R ^ (t + 1)) := fun t => by
    have hc := P.c_pos t
    have hc' : 0 < cstar β R k₀ t := P'.c_pos t
    have hlog : log (P.c t) ≤ log (cstar β R k₀ t) + (P.c t - cstar β R k₀ t) / cstar β R k₀ t := by
      have := log_le_sub_one_of_pos (div_pos hc hc')
      rw [log_div hc.ne' hc'.ne'] at this
      have e : P.c t / cstar β R k₀ t - 1 = (P.c t - cstar β R k₀ t) / cstar β R k₀ t := by
        field_simp [hc'.ne']
      linarith
    have := mul_le_mul_of_nonneg_left hlog (pow_pos hβ₀ t).le
    have e : β ^ t * ((P.c t - cstar β R k₀ t) / cstar β R k₀ t) =
        1 / ((1 - β) * k₀) * (P.c t / R ^ (t + 1) - cstar β R k₀ t / R ^ (t + 1)) := by
      rw [show β ^ t * ((P.c t - cstar β R k₀ t) / cstar β R k₀ t) =
        β ^ t / cstar β R k₀ t * (P.c t - cstar β R k₀ t) by ring, hw t]; ring
    linarith
  have hsum := sum_le_sum fun t (_ : t ∈ range T) => hpt t
  have hb' : ∑ t ∈ range T, cstar β R k₀ t / R ^ (t + 1) = k₀ - kstar β R k₀ T / R ^ T :=
    pv_budget hR P' T
  rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, pv_budget hR P, hb'] at hsum
  have hkT : kstar β R k₀ T / R ^ T = β ^ T * k₀ := by
    have : R ^ T ≠ 0 := (pow_pos hR T).ne'
    simp only [kstar, mul_pow]; field_simp
  have hPk : 0 ≤ P.k T / R ^ T := div_nonneg (P.k_nonneg T) (pow_pos hR T).le
  have : 1 / ((1 - β) * k₀) * (k₀ - P.k T / R ^ T - (k₀ - kstar β R k₀ T / R ^ T)) ≤
      β ^ T / (1 - β) := by
    rw [hkT]
    have : 1 / ((1 - β) * k₀) * (k₀ - P.k T / R ^ T - (k₀ - β ^ T * k₀)) =
        β ^ T / (1 - β) - 1 / ((1 - β) * k₀) * (P.k T / R ^ T) := by
      field_simp; ring
    rw [this]
    have : 0 ≤ 1 / ((1 - β) * k₀) * (P.k T / R ^ T) := by positivity
    linarith
  linarith

/-- Lifetime utility of the optimal plan is a convergent series. -/
theorem summable_cstar {β R k₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hR : 0 < R) (hk : 0 < k₀) :
    Summable fun t => β ^ t * log (cstar β R k₀ t) := by
  have h1β : 0 < 1 - β := by linarith
  have e : ∀ t : ℕ, β ^ t * log (cstar β R k₀ t) =
      log ((1 - β) * R * k₀) * β ^ t + log (β * R) * ((t : ℝ) ^ 1 * β ^ t) := fun t => by
    have hβR : 0 < β * R := mul_pos hβ₀ hR
    simp only [cstar, kstar]
    rw [show (1 - β) * R * ((β * R) ^ t * k₀) = (1 - β) * R * k₀ * (β * R) ^ t by ring,
      log_mul (by positivity) (by positivity), log_pow]
    ring
  simp_rw [e]
  have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ₀]; exact hβ₁
  exact ((summable_geometric_of_lt_one hβ₀.le hβ₁).mul_left _).add
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left _)

/-- **Optimality of `c*`.** If a feasible plan's lifetime utility
`Σ βᵗ log c_t` converges to `W`, then `W` is at most the optimum's lifetime
utility. -/
theorem optimal {β R k₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hR : 0 < R) (hk : 0 < k₀)
    (P : Plan R k₀) {W : ℝ} (hW : HasSum (fun t => β ^ t * log (P.c t)) W) :
    W ≤ ∑' t, β ^ t * log (cstar β R k₀ t) := by
  have h1β : 0 < 1 - β := by linarith
  have hs := (summable_cstar hβ₀ hβ₁ hR hk).hasSum.tendsto_sum_nat
  have ht : Tendsto (fun T : ℕ => β ^ T / (1 - β)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ₀.le hβ₁).div_const (1 - β)
  have := hs.add ht
  rw [add_zero] at this
  exact le_of_tendsto_of_tendsto' hW.tendsto_sum_nat this
    fun T => optimal_finite hβ₀ hβ₁ hR hk P T

/-- **Positive growth** iff `βR > 1`, i.e. `β (1 + A − δ) > 1`. -/
theorem cstar_strictMono_iff {β R k₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hR : 0 < R)
    (hk : 0 < k₀) : StrictMono (cstar β R k₀) ↔ 1 < β * R := by
  have h1β : 0 < 1 - β := by linarith
  have hc : ∀ t, 0 < cstar β R k₀ t := (optPlan hβ₀ hβ₁ hR hk).c_pos
  constructor
  · intro h
    have := h (Nat.lt_succ_self 0)
    rw [cstar_succ] at this
    have h0 := hc 0
    nlinarith
  · intro h
    refine strictMono_nat_of_lt_succ fun t => ?_
    rw [cstar_succ]
    have := hc t
    nlinarith

end AK
end Econ

end
