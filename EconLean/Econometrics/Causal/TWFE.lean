/-
# Two-way fixed effects with staggered treatment: negative weights

de Chaisemartin–D'Haultfœuille (2020), "Two-Way Fixed Effects Estimators with
Heterogeneous Treatment Effects", *American Economic Review* 110(9),
Theorem 1 (and the decomposition in §III); Goodman-Bacon (2021), *Journal of
Econometrics* 225 (the same phenomenon from the "forbidden comparisons" side).

**The economics.** Empirical work routinely estimates
`Y_{g,t} = a_g + l_t + β D_{g,t} + error`
on a panel of groups `g` and periods `t`, and reads `β` as "the treatment
effect". de Chaisemartin and D'Haultfœuille show that under parallel trends
`β` is a *weighted sum* of the cell-level effects `τ_{g,t}` over treated cells,
`β = Σ_{g,t} w_{g,t} τ_{g,t}`,  `w_{g,t} = ε_{g,t} D_{g,t} / Σ ε D`,
where `ε` is the residual from regressing `D` on group and period fixed effects.
The weights sum to one but **can be negative**: with staggered adoption,
early-treated groups in late periods get negative weight. Then `β` can be
negative even though every treatment effect is positive.

**Setting (sharp design, population level).**
* Finite sets of groups `G` and periods `T`; data are population cell means.
* `D g t` is the treatment of cell `(g, t)` (the theorem does not even need it
  to be binary; weights vanish on untreated cells when it is).
* Parallel trends, cell-level form: the untreated outcome is additive,
  `Y₀ g t = α g + λ t` (dCDH Assumption 4 for cell means).
* Observed outcome `Y g t = Y₀ g t + D g t · τ g t`.
* `β` is any least-squares coefficient: `(a, l, β)` minimise
  `Σ_{g,t} (Y g t − a g − l t − β D g t)²`.

**Documented deviations.** dCDH work with individual-level data and cell sizes
`N_{g,t}`; we take all cells to have equal weight (balanced panel, equal cell
sizes), where their weights reduce to ours. Their parallel-trends assumption is
on expectations of potential outcomes; ours is on the population cell means,
which is the same thing at the population level. For non-binary `D` the
outcome equation `Y = Y₀ + D·τ` imposes a linear dose response; dCDH treat
binary `D`.

**Proof idea.** The normal equations say the residual `r` sums to zero in each
row and each column and is orthogonal to `D`. The double-demeaned treatment `ε`
is a combination of `D`, row effects and column effects, so it is orthogonal to
`r`; and `ε` has zero row and column sums, so it is orthogonal to any
`a g + l t`. Taking `Σ ε · Y` two ways gives `β Σ ε D = Σ ε D τ`.
-/
module

public import EconLean.Econometrics.OLS
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Econ.Causal.TWFE

open Finset

variable {G T : Type*} [Fintype G] [Fintype T]

/-! ## The TWFE regression -/

/-- Residual of the TWFE fit `(a, l, b)` in cell `(g, t)`. -/
def resid (Y D : G → T → ℝ) (a : G → ℝ) (l : T → ℝ) (b : ℝ) (g : G) (t : T) : ℝ :=
  Y g t - a g - l t - b * D g t

/-- Sum of squared residuals of the TWFE fit (equal cell weights). -/
def ssr (Y D : G → T → ℝ) (a : G → ℝ) (l : T → ℝ) (b : ℝ) : ℝ :=
  ∑ g, ∑ t, resid Y D a l b g t ^ 2

/-- `(a, l, b)` is a least-squares fit of `Y` on group effects, period effects and
`D`; `b` is then "the TWFE coefficient". -/
def IsTWFE (Y D : G → T → ℝ) (a : G → ℝ) (l : T → ℝ) (b : ℝ) : Prop :=
  ∀ a' l' b', ssr Y D a l b ≤ ssr Y D a' l' b'

/-- Normal equations of the TWFE regression: residuals sum to zero within every
group, within every period, and are orthogonal to the treatment. -/
def NormalEq (Y D : G → T → ℝ) (a : G → ℝ) (l : T → ℝ) (b : ℝ) : Prop :=
  (∀ g, ∑ t, resid Y D a l b g t = 0) ∧ (∀ t, ∑ g, resid Y D a l b g t = 0) ∧
    ∑ g, ∑ t, D g t * resid Y D a l b g t = 0

/-- First-order condition: if moving the residuals in direction `v` never lowers
the sum of squares, then the residuals are orthogonal to `v`. -/
lemma sum_mul_eq_zero_of_forall {r v : G → T → ℝ}
    (h : ∀ c : ℝ, ∑ g, ∑ t, r g t ^ 2 ≤ ∑ g, ∑ t, (r g t - c * v g t) ^ 2) :
    ∑ g, ∑ t, r g t * v g t = 0 := by
  have hs : 0 ≤ ∑ g, ∑ t, v g t ^ 2 :=
    sum_nonneg fun g _ => sum_nonneg fun t _ => sq_nonneg _
  refine OLS.eq_zero_of_forall_quadratic_nonneg hs fun c => ?_
  have hc := h c
  have expand : ∑ g, ∑ t, (r g t - c * v g t) ^ 2 = ∑ g, ∑ t, r g t ^ 2
      + (-2 * c * ∑ g, ∑ t, r g t * v g t + c ^ 2 * ∑ g, ∑ t, v g t ^ 2) := by
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by ring
  linarith

/-- Residuals satisfying the normal equations are orthogonal to every
`A g + L t + B · D g t`. -/
lemma sum_resid_mul_eq_zero {Y D : G → T → ℝ} {a : G → ℝ} {l : T → ℝ} {b : ℝ}
    (h : NormalEq Y D a l b) (A : G → ℝ) (L : T → ℝ) (B : ℝ) :
    ∑ g, ∑ t, resid Y D a l b g t * (A g + L t + B * D g t) = 0 := by
  obtain ⟨hrow, hcol, hD⟩ := h
  simp only [mul_add, sum_add_distrib]
  have h1 : ∑ g, ∑ t, resid Y D a l b g t * A g = 0 :=
    sum_eq_zero fun g _ => by rw [← sum_mul, hrow g, zero_mul]
  have h2 : ∑ g, ∑ t, resid Y D a l b g t * L t = 0 := by
    rw [sum_comm]
    exact sum_eq_zero fun t _ => by rw [← sum_mul, hcol t, zero_mul]
  have h3 : ∑ g, ∑ t, resid Y D a l b g t * (B * D g t)
      = B * ∑ g, ∑ t, D g t * resid Y D a l b g t := by
    simp only [mul_sum]
    exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by ring
  rw [h1, h2, h3, hD]
  ring

/-- **Least squares ⟺ normal equations** for the TWFE regression. -/
theorem isTWFE_iff_normalEq (Y D : G → T → ℝ) (a : G → ℝ) (l : T → ℝ) (b : ℝ)
    [DecidableEq G] [DecidableEq T] :
    IsTWFE Y D a l b ↔ NormalEq Y D a l b := by
  constructor
  · intro h
    refine ⟨fun g₀ => ?_, fun t₀ => ?_, ?_⟩
    · -- perturb the group effect of `g₀`
      have := sum_mul_eq_zero_of_forall (r := resid Y D a l b)
        (v := fun g _ => if g = g₀ then 1 else 0) fun c => by
          have hc := h (fun g => a g + c * (if g = g₀ then 1 else 0)) l b
          exact hc.trans_eq (sum_congr rfl fun g _ => sum_congr rfl fun t _ => by
            simp only [resid]; ring)
      rw [sum_comm] at this
      simpa [mul_ite, sum_ite_eq'] using this
    · -- perturb the period effect of `t₀`
      have := sum_mul_eq_zero_of_forall (r := resid Y D a l b)
        (v := fun _ t => if t = t₀ then 1 else 0) fun c => by
          have hc := h a (fun t => l t + c * (if t = t₀ then 1 else 0)) b
          exact hc.trans_eq (sum_congr rfl fun g _ => sum_congr rfl fun t _ => by
            simp only [resid]; ring)
      simpa [mul_ite, sum_ite_eq'] using this
    · -- perturb the treatment coefficient
      have := sum_mul_eq_zero_of_forall (r := resid Y D a l b) (v := D) fun c => by
        have hc := h a l (b + c)
        exact hc.trans_eq (sum_congr rfl fun g _ => sum_congr rfl fun t _ => by
          simp only [resid]; ring)
      rw [← this]
      exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => mul_comm _ _
  · intro h a' l' b'
    -- `resid' = resid + δ` with `δ = (a − a') g + (l − l') t + (b − b') D`.
    have horth := sum_resid_mul_eq_zero h (fun g => a g - a' g) (fun t => l t - l' t) (b - b')
    have expand : ssr Y D a' l' b' = ssr Y D a l b
        + 2 * ∑ g, ∑ t, resid Y D a l b g t * ((a g - a' g) + (l t - l' t) + (b - b') * D g t)
        + ∑ g, ∑ t, ((a g - a' g) + (l t - l' t) + (b - b') * D g t) ^ 2 := by
      simp only [ssr, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by simp only [resid]; ring
    rw [expand, horth]
    have : 0 ≤ ∑ g, ∑ t, ((a g - a' g) + (l t - l' t) + (b - b') * D g t) ^ 2 :=
      sum_nonneg fun g _ => sum_nonneg fun t _ => sq_nonneg _
    linarith

/-! ## Double-demeaned treatment and the weights -/

/-- Group mean of `D`. -/
noncomputable def rowMean (D : G → T → ℝ) (g : G) : ℝ := (∑ t, D g t) / Fintype.card T

/-- Period mean of `D`. -/
noncomputable def colMean (D : G → T → ℝ) (t : T) : ℝ := (∑ g, D g t) / Fintype.card G

/-- Grand mean of `D`. -/
noncomputable def grandMean (D : G → T → ℝ) : ℝ :=
  (∑ g, ∑ t, D g t) / (Fintype.card G * Fintype.card T)

/-- The residual of `D` on group and period fixed effects (balanced panel):
`ε = D − D̄_g − D̄_t + D̄`. -/
noncomputable def eps (D : G → T → ℝ) (g : G) (t : T) : ℝ :=
  D g t - rowMean D g - colMean D t + grandMean D

/-- The dCDH weight on cell `(g, t)`: `ε_{g,t} D_{g,t} / Σ ε D`. -/
noncomputable def weight (D : G → T → ℝ) (g : G) (t : T) : ℝ :=
  eps D g t * D g t / ∑ g', ∑ t', eps D g' t' * D g' t'

variable [Nonempty G] [Nonempty T]

lemma sum_eps_row (D : G → T → ℝ) (g : G) : ∑ t, eps D g t = 0 := by
  have hT : (Fintype.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [eps, rowMean, colMean, grandMean, sum_add_distrib, sum_sub_distrib, sum_const,
    card_univ, nsmul_eq_mul, ← sum_div]
  rw [sum_comm (f := fun t g => D g t)]
  field_simp
  ring

lemma sum_eps_col (D : G → T → ℝ) (t : T) : ∑ g, eps D g t = 0 := by
  have hT : (Fintype.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [eps, rowMean, colMean, grandMean, sum_add_distrib, sum_sub_distrib, sum_const,
    card_univ, nsmul_eq_mul, ← sum_div]
  field_simp
  ring

/-- `ε` is orthogonal to every additive two-way pattern `A g + L t`. -/
lemma sum_eps_mul_additive (D : G → T → ℝ) (A : G → ℝ) (L : T → ℝ) :
    ∑ g, ∑ t, eps D g t * (A g + L t) = 0 := by
  simp only [mul_add, sum_add_distrib]
  have h1 : ∑ g, ∑ t, eps D g t * A g = 0 :=
    sum_eq_zero fun g _ => by rw [← sum_mul, sum_eps_row, zero_mul]
  have h2 : ∑ g, ∑ t, eps D g t * L t = 0 := by
    rw [sum_comm]
    exact sum_eq_zero fun t _ => by rw [← sum_mul, sum_eps_col, zero_mul]
  rw [h1, h2, add_zero]

/-- The denominator `Σ ε D` equals `Σ ε²`. So it is nonzero exactly when
treatment is not itself additive in group and period (`ε ≢ 0`). -/
theorem sum_eps_mul_D (D : G → T → ℝ) :
    ∑ g, ∑ t, eps D g t * D g t = ∑ g, ∑ t, eps D g t ^ 2 := by
  have h := sum_eps_mul_additive D (rowMean D) (fun t => colMean D t - grandMean D)
  have : ∑ g, ∑ t, eps D g t * D g t
      = ∑ g, ∑ t, eps D g t ^ 2
        + ∑ g, ∑ t, eps D g t * (rowMean D g + (colMean D t - grandMean D)) := by
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by
      simp only [eps]; ring
  rw [this, h, add_zero]

omit [Nonempty G] [Nonempty T] in
/-- The weights sum to one. -/
theorem sum_weight (D : G → T → ℝ) (hden : ∑ g, ∑ t, eps D g t * D g t ≠ 0) :
    ∑ g, ∑ t, weight D g t = 1 := by
  simp only [weight, ← sum_div]
  exact div_self hden

omit [Nonempty G] [Nonempty T] in
/-- Untreated cells get zero weight. -/
theorem weight_eq_zero_of_untreated (D : G → T → ℝ) {g : G} {t : T} (h : D g t = 0) :
    weight D g t = 0 := by
  simp [weight, h]

/-- **de Chaisemartin–D'Haultfœuille (2020), Theorem 1** (sharp design, equal
cell sizes). Under parallel trends (`Y₀` additive in group and period), every
TWFE coefficient `b` is the weighted sum `Σ w_{g,t} τ_{g,t}` of the cell
treatment effects, with the weights `w = ε D / Σ ε D` (which sum to one,
vanish on untreated cells, and may be negative). -/
theorem twfe_eq_weighted_sum [DecidableEq G] [DecidableEq T] (D τ : G → T → ℝ)
    (α : G → ℝ) (lam : T → ℝ) {a : G → ℝ} {l : T → ℝ} {b : ℝ}
    (hmin : IsTWFE (fun g t => α g + lam t + D g t * τ g t) D a l b)
    (hden : ∑ g, ∑ t, eps D g t * D g t ≠ 0) :
    b = ∑ g, ∑ t, weight D g t * τ g t := by
  set Y : G → T → ℝ := fun g t => α g + lam t + D g t * τ g t with hY
  have hne := (isTWFE_iff_normalEq Y D a l b).mp hmin
  -- `Σ ε r = 0`: `ε` is a combination of row effects, column effects and `D`.
  have h_er : ∑ g, ∑ t, eps D g t * resid Y D a l b g t = 0 := by
    have := sum_resid_mul_eq_zero hne (fun g => -rowMean D g)
      (fun t => grandMean D - colMean D t) 1
    rw [← this]
    exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by simp only [eps]; ring
  -- First way: `Σ ε Y = b Σ ε D` (using the fitted model).
  have h1 : ∑ g, ∑ t, eps D g t * Y g t = b * ∑ g, ∑ t, eps D g t * D g t := by
    have hsplit : ∑ g, ∑ t, eps D g t * Y g t
        = ∑ g, ∑ t, eps D g t * (a g + l t) + b * ∑ g, ∑ t, eps D g t * D g t
          + ∑ g, ∑ t, eps D g t * resid Y D a l b g t := by
      simp only [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by simp only [resid]; ring
    rw [hsplit, sum_eps_mul_additive, h_er]
    ring
  -- Second way: `Σ ε Y = Σ ε D τ` (using parallel trends).
  have h2 : ∑ g, ∑ t, eps D g t * Y g t = ∑ g, ∑ t, eps D g t * D g t * τ g t := by
    have hsplit : ∑ g, ∑ t, eps D g t * Y g t
        = ∑ g, ∑ t, eps D g t * (α g + lam t) + ∑ g, ∑ t, eps D g t * D g t * τ g t := by
      simp only [← sum_add_distrib]
      exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by simp only [hY]; ring
    rw [hsplit, sum_eps_mul_additive, zero_add]
  have key : b * ∑ g, ∑ t, eps D g t * D g t = ∑ g, ∑ t, eps D g t * D g t * τ g t :=
    h1.symm.trans h2
  simp only [weight, div_mul_eq_mul_div, ← sum_div]
  rw [eq_div_iff hden, key]

/-! ## The negative-weights example

Two groups adopting at different dates (staggered adoption) over three periods:
the *early* group `0` is treated in periods 1 and 2, the *late* group `1` only
in period 2. Effects grow over time for the early group
(`τ = 1` in period 1, `τ = 4` in period 2) and the late group has `τ = 1`.
Every treatment effect is positive, yet the TWFE coefficient is `−1/2`,
because the early group's period-2 cell gets weight `−1/2`.
-/

namespace Example

/-- Staggered adoption: early group treated from period 1, late group from 2. -/
def D : Fin 2 → Fin 3 → ℝ := ![![0, 1, 1], ![0, 0, 1]]

/-- Treatment effects: growing for the early group. -/
def τ : Fin 2 → Fin 3 → ℝ := ![![1, 1, 4], ![1, 1, 1]]

/-- Observed outcomes with zero untreated outcomes (`α = λ = 0`). -/
def Y : Fin 2 → Fin 3 → ℝ := fun g t => (fun _ => 0) g + (fun _ => 0) t + D g t * τ g t

lemma eps_values : eps D 0 1 = 1 / 3 ∧ eps D 0 2 = -1 / 6 ∧ eps D 1 2 = 1 / 6 := by
  simp only [eps, rowMean, colMean, grandMean, D, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fintype.card_fin]
  norm_num [Matrix.cons_val]

lemma den : ∑ g, ∑ t, eps D g t * D g t = 1 / 3 := by
  simp only [eps, rowMean, colMean, grandMean, D, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fintype.card_fin]
  norm_num [Matrix.cons_val]

/-- The early group's last period gets a negative weight. -/
theorem weight_negative : weight D 0 2 = -1 / 2 := by
  rw [weight, den, eps_values.2.1]
  norm_num [D, Matrix.cons_val]

/-- All treated cells have positive treatment effects. -/
theorem effects_pos : ∀ g t, D g t = 1 → 0 < τ g t := by
  intro g t
  fin_cases g <;> fin_cases t <;> norm_num [D, τ]

/-- A least-squares fit exists, with TWFE coefficient `−1/2`. -/
theorem isTWFE_example :
    IsTWFE Y D ![2, 1 / 2] ![-5 / 4, -1 / 2, 7 / 4] (-1 / 2) := by
  rw [isTWFE_iff_normalEq]
  refine ⟨fun g => ?_, fun t => ?_, ?_⟩
  · fin_cases g <;>
      simp [resid, Y, D, τ, Fin.sum_univ_succ] <;> norm_num
  · fin_cases t <;>
      simp [resid, Y, D, τ, Fin.sum_univ_succ] <;> norm_num
  · simp [resid, Y, D, τ, Fin.sum_univ_succ]
    norm_num

/-- **Sign reversal.** In this staggered design every treatment effect is
positive, yet every TWFE coefficient equals `−1/2 < 0`. -/
theorem twfe_negative {a : Fin 2 → ℝ} {l : Fin 3 → ℝ} {b : ℝ} (h : IsTWFE Y D a l b) :
    b = -1 / 2 := by
  rw [twfe_eq_weighted_sum D τ (fun _ => 0) (fun _ => 0) h (by rw [den]; norm_num)]
  simp only [weight, eps, rowMean, colMean, grandMean, D, τ, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fintype.card_fin]
  norm_num [Matrix.cons_val]

end Example

end Econ.Causal.TWFE
