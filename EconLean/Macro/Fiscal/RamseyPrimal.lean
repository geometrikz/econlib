/-
# The Ramsey problem in primal form and Chamley–Judd

Lucas and Stokey (1983); Chari and Kehoe (1999), "Optimal Fiscal and Monetary
Policy", Handbook of Macroeconomics, §2; Chamley (1986); Judd (1985);
Ljungqvist–Sargent ch. 16.

**The primal Ramsey problem.** Capital evolves by the resource constraint
`k_{t+1} = F(k_t) − c_t − g_t` (`Feasible`), where `F(k)` is output plus
undepreciated capital and `g` is government spending. In the primal approach
the implementability constraint (the household's present-value budget, with
the household's first-order conditions substituted in) is attached to the
objective with multiplier `Φ ≥ 0`, giving the pseudo-utility
`W(c) = u(c) + Φ · (u'(c) c + …)`. For given `Φ`, the Ramsey allocation
maximizes `Σ βᵗ W(c_t)` over feasible allocations from the given `k₀`
(`IsOptimal`).

**Results.**
* `planner_euler`: at an optimum, wherever `W` and `F` are differentiable,
  `W'(c_t) = β W'(c_{t+1}) F'(k_{t+1})`: the planner faces the undistorted
  return. This is **derived** by a one-period variation (save `ε` more at `t`,
  consume the proceeds at `t + 1`), not assumed.
* `isRamseyFOC`: if the allocation is decentralized by capital-income taxes
  `τ` (the household Euler equation holds with after-tax return), the pair of
  conditions `ChamleyJudd.IsRamseyFOC` holds with `Wc = W'(c)` and
  `r_{t+1} = F'(k_{t+1}) − 1`.
* `chamley_judd_primal`: combining the two, if the Ramsey allocation
  converges to an interior steady state, the limiting capital tax is zero.

**Deviations.** `W` is the same function at every date: the canonical
pseudo-utility has an extra date-0 term (the initial capital levy), so the
date-0 Euler equation differs; nothing ties `W` or `uc` to a primitive
utility `u`, and the household Euler equation is a hypothesis
(decentralization). The multiplier `Φ` on implementability is taken as given (the
inner problem of the Lagrangian; the outer choice of `Φ` does not affect the
first-order conditions used here). Feasible paths have non-negative consumption and capital; `IsOptimal`
compares against all such paths with summable discounted pseudo-utility, and
the Euler equation is derived at interior dates. `nonvacuous` exhibits an
interior optimum satisfying all hypotheses of `chamley_judd_primal`. Labour is inelastic and the initial-period tax levy is not
modelled.
-/
module

public import EconLean.Macro.Fiscal.ChamleyJudd
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

noncomputable section

namespace Econ
namespace RamseyPrimal

open Filter Topology

/-- A primal Ramsey problem with given multiplier on implementability. -/
structure Problem where
  /-- Discount factor. -/
  β : ℝ
  /-- Pseudo-utility `W(c) = u(c) + Φ·(implementability term)`. -/
  W : ℝ → ℝ
  /-- Output plus undepreciated capital. -/
  F : ℝ → ℝ
  /-- Government spending path. -/
  g : ℕ → ℝ
  hβ : 0 < β

namespace Problem

variable (P : Problem)

/-- Feasibility: the resource constraint, non-negative consumption and
non-negative capital (no borrowing against the future: the planner cannot run
capital below zero). -/
def Feasible (c k : ℕ → ℝ) : Prop :=
  (∀ t, k (t + 1) = P.F (k t) - c t - P.g t) ∧ (∀ t, 0 ≤ c t) ∧ ∀ t, 0 ≤ k t

/-- Discounted pseudo-utility. -/
def value (c : ℕ → ℝ) : ℝ := ∑' t, P.β ^ t * P.W (c t)

/-- The Ramsey allocation (for the given multiplier): feasible, with summable
value, and no feasible allocation from the same `k₀` with summable value does
better. -/
def IsOptimal (c k : ℕ → ℝ) : Prop :=
  P.Feasible c k ∧ Summable (fun t => P.β ^ t * P.W (c t)) ∧
    ∀ c' k', P.Feasible c' k' → k' 0 = k 0 → Summable (fun t => P.β ^ t * P.W (c' t)) →
      P.value c' ≤ P.value c

/-- The one-period variation: save `ε` more at date `s`, consume the extra
output at `s + 1`, then rejoin the original path. -/
def varK (k : ℕ → ℝ) (s : ℕ) (ε : ℝ) : ℕ → ℝ := fun t => if t = s + 1 then k t + ε else k t

def varC (c k : ℕ → ℝ) (s : ℕ) (ε : ℝ) : ℕ → ℝ := fun t =>
  if t = s then c t - ε
  else if t = s + 1 then P.F (k (s + 1) + ε) - k (s + 2) - P.g (s + 1)
  else c t

variable {P}

theorem feasible_var {c k : ℕ → ℝ} (h : P.Feasible c k) (s : ℕ) {ε : ℝ}
    (hε₀ : ε ≤ c s) (hε₁ : 0 ≤ k (s + 1) + ε)
    (hε₂ : 0 ≤ P.F (k (s + 1) + ε) - k (s + 2) - P.g (s + 1)) :
    P.Feasible (P.varC c k s ε) (varK k s ε) := by
  obtain ⟨hr, hc, hk⟩ := h
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simp only [varK, varC]
    by_cases h1 : t = s
    · subst h1; simp [hr t]; ring
    · by_cases h2 : t = s + 1
      · subst h2; simp; ring
      · simp [h1, h2, hr t]
  · simp only [varC]
    split_ifs with h1 h2
    · subst h1; linarith
    · exact hε₂
    · exact hc t
  · simp only [varK]
    split_ifs with h1
    · subst h1; exact hε₁
    · exact hk t

theorem varC_eq {c k : ℕ → ℝ} (h : P.Feasible c k) (s : ℕ) :
    P.varC c k s 0 = c := by
  funext t
  simp only [varC]
  split_ifs with h1 h2
  · simp
  · subst h2; rw [add_zero, h.1 (s + 1)]; ring
  · rfl

/-- The value change from the variation involves only dates `s` and `s + 1`. -/
theorem value_var {c k : ℕ → ℝ} (hs : Summable fun t => P.β ^ t * P.W (c t)) (s : ℕ) (ε : ℝ) :
    Summable (fun t => P.β ^ t * P.W (P.varC c k s ε t)) ∧
    P.value (P.varC c k s ε) - P.value c =
      P.β ^ s * (P.W (c s - ε) - P.W (c s)) +
      P.β ^ (s + 1) * (P.W (P.F (k (s + 1) + ε) - k (s + 2) - P.g (s + 1)) - P.W (c (s + 1))) := by
  set d : ℕ → ℝ := fun t => P.β ^ t * P.W (P.varC c k s ε t) - P.β ^ t * P.W (c t)
  have hd : ∀ t ∉ ({s, s + 1} : Finset ℕ), d t = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [d, varC, ht.1, ht.2]
  have hds : Summable d := summable_of_ne_finset_zero hd
  have hsum : Summable (fun t => P.β ^ t * P.W (P.varC c k s ε t)) := by
    have := hds.add hs
    simpa [d] using this
  refine ⟨hsum, ?_⟩
  rw [value, value, ← hsum.tsum_sub hs, tsum_eq_sum hd]
  have hne : s ≠ s + 1 := by omega
  rw [Finset.sum_pair hne]
  simp only [d, varC]
  simp
  ring

/-- **The planner's Euler equation**, derived from optimality by a one-period
variation, at dates where consumption and capital are interior. -/
theorem planner_euler {c k : ℕ → ℝ} (h : P.IsOptimal c k) (s : ℕ)
    (hc₀ : 0 < c s) (hc₁ : 0 < c (s + 1)) (hk : 0 < k (s + 1)) {Wc₀ Wc₁ Fk : ℝ}
    (hW₀ : HasDerivAt P.W Wc₀ (c s)) (hW₁ : HasDerivAt P.W Wc₁ (c (s + 1)))
    (hF : HasDerivAt P.F Fk (k (s + 1))) :
    Wc₀ = P.β * Wc₁ * Fk := by
  obtain ⟨hfeas, hsum, hopt⟩ := h
  -- `J(ε)` = value change from the variation
  set J : ℝ → ℝ := fun ε => P.β ^ s * (P.W (c s - ε) - P.W (c s)) +
      P.β ^ (s + 1) * (P.W (P.F (k (s + 1) + ε) - k (s + 2) - P.g (s + 1)) - P.W (c (s + 1)))
  -- for small `ε` the variation stays feasible
  have hcont : ∀ᶠ ε in 𝓝 (0 : ℝ), -c (s + 1) < P.F (k (s + 1) + ε) - P.F (k (s + 1)) := by
    have hc : ContinuousAt (fun ε => P.F (k (s + 1) + ε) - P.F (k (s + 1))) 0 := by
      have := hF.continuousAt
      have h2 : ContinuousAt (fun ε : ℝ => k (s + 1) + ε) 0 := by fun_prop
      have h3 : ContinuousAt (fun ε => P.F (k (s + 1) + ε)) 0 :=
        ContinuousAt.comp (g := P.F) (by simpa using this) h2
      exact h3.sub continuousAt_const
    have := hc.eventually (Ioi_mem_nhds (a := -c (s + 1)) (by simp; linarith))
    simpa using this
  have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < c s ∧ -k (s + 1) < ε :=
    Filter.Eventually.and (Iio_mem_nhds hc₀) (Ioi_mem_nhds (show -k (s + 1) < 0 by linarith))
  have hmax : IsLocalMax J 0 := by
    filter_upwards [hcont, hsmall] with ε hε hε'
    obtain ⟨hs', he⟩ := value_var (k := k) hsum s ε
    have hFk : P.F (k (s + 1)) - k (s + 2) - P.g (s + 1) = c (s + 1) := by
      rw [hfeas.1 (s + 1)]; ring
    have hle := hopt _ _ (feasible_var hfeas s hε'.1.le (by linarith)
      (by linarith)) (by simp [varK]) hs'
    have hJ0 : J 0 = 0 := by
      simp only [J, sub_zero, add_zero]
      rw [hFk]
      ring
    show J ε ≤ J 0
    rw [hJ0]; simp only [J]; linarith
  -- derivative of `J` at 0
  have hc1 : P.F (k (s + 1) + 0) - k (s + 2) - P.g (s + 1) = c (s + 1) := by
    rw [add_zero, hfeas.1 (s + 1)]; ring
  have d1 : HasDerivAt (fun ε => P.W (c s - ε)) (Wc₀ * (-1)) 0 := by
    have hl : HasDerivAt (fun ε : ℝ => c s - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c s)
    exact HasDerivAt.comp 0 (by simpa using hW₀) hl
  have d2 : HasDerivAt (fun ε => P.W (P.F (k (s + 1) + ε) - k (s + 2) - P.g (s + 1)))
      (Wc₁ * (Fk * 1)) 0 := by
    have hl : HasDerivAt (fun ε : ℝ => k (s + 1) + ε) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (k (s + 1))
    have hF' : HasDerivAt (fun ε => P.F (k (s + 1) + ε)) (Fk * 1) 0 :=
      HasDerivAt.comp 0 (by simpa using hF) hl
    have hF'' := (hF'.sub_const (k (s + 2))).sub_const (P.g (s + 1))
    exact HasDerivAt.comp 0 (by rw [hc1]; exact hW₁) hF''
  have hJ : HasDerivAt J (P.β ^ s * (Wc₀ * (-1)) + P.β ^ (s + 1) * (Wc₁ * (Fk * 1))) 0 :=
    (HasDerivAt.const_mul (P.β ^ s) (HasDerivAt.sub_const (P.W (c s)) d1)).add
      (HasDerivAt.const_mul (P.β ^ (s + 1)) (HasDerivAt.sub_const (P.W (c (s + 1))) d2))
  have h0 := hmax.hasDerivAt_eq_zero hJ
  have hb : P.β ^ s ≠ 0 := pow_ne_zero _ P.hβ.ne'
  have : P.β ^ s * (P.β * Wc₁ * Fk - Wc₀) = 0 := by rw [pow_succ] at h0; linear_combination h0
  have := (mul_eq_zero.1 this).resolve_left hb
  linarith

/-- **Decentralized Ramsey allocation.** If the optimum is supported by
capital-income taxes `τ` (household Euler with after-tax net return
`r = F' − 1`), the Ramsey first-order conditions of
`ChamleyJudd.IsRamseyFOC` hold, with `Wc_t = W'(c_t)`. -/
theorem isRamseyFOC {c k : ℕ → ℝ} (h : P.IsOptimal c k) (hc : ∀ t, 0 < c t)
    (hk : ∀ t, 0 < k (t + 1)) {uc Wc Fk τ : ℕ → ℝ}
    (hW : ∀ t, HasDerivAt P.W (Wc t) (c t)) (hF : ∀ t, HasDerivAt P.F (Fk t) (k t))
    (hhh : ∀ t, uc t = P.β * uc (t + 1) * (1 + (1 - τ (t + 1)) * (Fk (t + 1) - 1))) :
    ChamleyJudd.IsRamseyFOC P.β uc Wc (fun t => Fk t - 1) τ := fun t =>
  ⟨hhh t, by
    have := planner_euler h t (hc t) (hc (t + 1)) (hk t) (hW t) (hW (t + 1)) (hF (t + 1))
    rw [this]; ring⟩

/-- **Chamley–Judd from the Ramsey problem.** If the decentralized Ramsey
allocation converges to an interior steady state (`uc`, `W'(c)` converge to
positive limits, the net return to a nonzero limit and taxes to `τ*`), the
long-run capital-income tax is zero. -/
theorem chamley_judd_primal {c k : ℕ → ℝ} (h : P.IsOptimal c k) (hc : ∀ t, 0 < c t)
    (hk : ∀ t, 0 < k (t + 1)) {uc Wc Fk τ : ℕ → ℝ}
    (hW : ∀ t, HasDerivAt P.W (Wc t) (c t)) (hF : ∀ t, HasDerivAt P.F (Fk t) (k t))
    (hhh : ∀ t, uc t = P.β * uc (t + 1) * (1 + (1 - τ (t + 1)) * (Fk (t + 1) - 1)))
    {ucs Wcs rs τs : ℝ} (hucs : 0 < ucs) (hWcs : 0 < Wcs) (hrs : rs ≠ 0)
    (huc : Tendsto uc atTop (𝓝 ucs)) (hWc : Tendsto Wc atTop (𝓝 Wcs))
    (hr : Tendsto (fun t => Fk t - 1) atTop (𝓝 rs)) (hτ : Tendsto τ atTop (𝓝 τs)) :
    τs = 0 :=
  ChamleyJudd.chamley_judd P.hβ (isRamseyFOC h hc hk hW hF hhh) hucs hWcs hrs huc hWc hr hτ

/-- **Non-vacuity.** With `β = 1/2`, `W(c) = c`, `F(k) = 2k` and no spending,
the constant plan `c ≡ 1`, `k ≡ 1` is a Ramsey optimum with interior
consumption and capital, and with `uc ≡ 1`, `τ ≡ 0` it satisfies every
hypothesis of `chamley_judd_primal` (here `W' ≡ 1`, `F' ≡ 2`, net return `1`). -/
theorem nonvacuous :
    let P : Problem := ⟨1 / 2, id, fun k => 2 * k, fun _ => 0, by norm_num⟩
    P.IsOptimal (fun _ => 1) (fun _ => 1) ∧
      (1 : ℝ) = P.β * 1 * (1 + (1 - 0) * (2 - 1)) := by
  intro P
  have hgeo : Summable fun t : ℕ => ((1 : ℝ) / 2) ^ t :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine ⟨⟨⟨fun t => by simp [P]; norm_num, fun t => by norm_num, fun t => by norm_num⟩,
    by simpa [P] using hgeo, fun c' k' hc' hk0 hs => ?_⟩, by norm_num [P]⟩
  obtain ⟨hr, hcn, hkn⟩ := hc'
  have hv : P.value (fun _ => 1) = 2 := by
    simp only [value, P, id, mul_one]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  rw [hv]
  simp only [value, P, id]
  refine Real.tsum_le_of_sum_range_le (fun t => mul_nonneg (by positivity) (hcn t)) fun m => ?_
  -- telescoping: `Σ_{t<m} 2⁻ᵗ c'_t = 2 k'_0 − 2·2⁻ᵐ k'_m`
  have tele : ∀ m, ∑ t ∈ Finset.range m, (1 / 2 : ℝ) ^ t * c' t =
      2 * k' 0 - 2 * (1 / 2) ^ m * k' m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have := hr m
      simp only [P] at this
      rw [pow_succ]
      have e : c' m = 2 * k' m - k' (m + 1) := by linarith
      rw [e]; ring
  rw [tele, hk0]
  have := hkn m
  have : 0 ≤ 2 * (1 / 2 : ℝ) ^ m * k' m := by positivity
  linarith

end Problem
end RamseyPrimal
end Econ

end
