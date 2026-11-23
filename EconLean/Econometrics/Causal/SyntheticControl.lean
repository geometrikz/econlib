/-
# Synthetic control: exact recovery in the linear factor model

Abadie, Diamond and Hainmueller (2010), *JASA* 105, §2.3 and Appendix B; Abadie
(2021), *JEL* 59, §3.

**The economics.** One unit (unit 1) is treated after period `T₀`; `J` donor
units never are. Untreated potential outcomes follow the linear factor model

  `Y_jt(0) = δ_t + θ_t ⬝ Z_j + λ_t ⬝ μ_j`,

with observed covariates `Z_j`, unobserved factor loadings `μ_j`, and common
time effects `δ_t`, `θ_t`, `λ_t`. A synthetic control is a weight vector `w`
over donors (ADH: `w_j ≥ 0`, `∑ w_j = 1`) that reproduces the treated unit's
covariates and pre-treatment outcomes. ADH show that, in the noiseless case,
if `∑_{t ≤ T₀} λ_tᵀ λ_t` is nonsingular, then such weights reproduce the treated
unit's untreated outcome in *every* period, so `Y_1t − ∑ w_j Y_jt` is the
treatment effect `α_1t` after `T₀` (ADH 2010, eq. (2) and the argument after
it). With noise, ADH bound the bias; that stochastic bound is not formalised.

**Encoding.** Donors `J`, periods `T`, pre-treatment periods `pre : Set T`.
Nonsingularity of `∑_{t∈pre} λ_tᵀλ_t` is equivalent to: `λ_t ⬝ v = 0` for all
`t ∈ pre` only for `v = 0`, which is how it is stated. Exactness needs only
`∑ w_j = 1`; nonnegativity is not used, so the theorems apply to ADH weights in
particular. Without the rank condition, exact pre-treatment fit does not pin
down the counterfactual (`not_exact_without_rank`).
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ.Causal.SyntheticControl

open Matrix

variable {J T r F : Type*} [Fintype J] [Fintype r] [Fintype F]

/-- Linear factor model for untreated potential outcomes:
`Y_t(0) = δ_t + θ_t ⬝ Z + λ_t ⬝ μ` for a unit with covariates `Z` and loadings `μ`. -/
structure FactorModel (T r F : Type*) where
  /-- Common time effect. -/
  δ : T → ℝ
  /-- Time-varying coefficients on observed covariates. -/
  θ : T → r → ℝ
  /-- Common factors. -/
  lam : T → F → ℝ

namespace FactorModel

/-- Untreated potential outcome of a unit with covariates `z` and loadings `m`. -/
def y0 (M : FactorModel T r F) (z : r → ℝ) (m : F → ℝ) (t : T) : ℝ :=
  M.δ t + M.θ t ⬝ᵥ z + M.lam t ⬝ᵥ m

/-- The rank condition: the pre-treatment factors determine the loadings, i.e.
`∑_{t ∈ pre} λ_tᵀ λ_t` is nonsingular. -/
def PreRank (M : FactorModel T r F) (pre : Set T) : Prop :=
  ∀ v : F → ℝ, (∀ t ∈ pre, M.lam t ⬝ᵥ v = 0) → v = 0

/-- Weighted donor average of untreated outcomes, for weights summing to one. -/
theorem sum_weight_y0 (M : FactorModel T r F) {w : J → ℝ} (hw : ∑ j, w j = 1)
    (Z : J → r → ℝ) (μ : J → F → ℝ) (t : T) :
    ∑ j, w j * M.y0 (Z j) (μ j) t = M.y0 (∑ j, w j • Z j) (∑ j, w j • μ j) t := by
  simp only [y0, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul,
    dotProduct_sum, dotProduct_smul, smul_eq_mul]

/-- **Synthetic control is exact in the noiseless factor model** (ADH 2010,
§2.3). If donor weights sum to one, match the treated unit's covariates, and
reproduce its untreated outcomes in every pre-treatment period, and the
pre-treatment factors have full rank, then the weights reproduce its untreated
outcome in every period. -/
theorem exact (M : FactorModel T r F) {pre : Set T} (hrank : M.PreRank pre)
    {w : J → ℝ} (hw : ∑ j, w j = 1) {Z : J → r → ℝ} {μ : J → F → ℝ} {Z₁ : r → ℝ}
    {μ₁ : F → ℝ} (hZ : ∑ j, w j • Z j = Z₁)
    (hfit : ∀ t ∈ pre, ∑ j, w j * M.y0 (Z j) (μ j) t = M.y0 Z₁ μ₁ t) (t : T) :
    ∑ j, w j * M.y0 (Z j) (μ j) t = M.y0 Z₁ μ₁ t := by
  have hμ : ∑ j, w j • μ j = μ₁ := by
    have h0 := hrank (∑ j, w j • μ j - μ₁) fun s hs => by
      have := hfit s hs
      rw [sum_weight_y0 M hw, hZ] at this
      simp only [y0] at this
      rw [dotProduct_sub]; linarith
    exact sub_eq_zero.mp h0
  rw [sum_weight_y0 M hw, hZ, hμ]

/-- **The synthetic-control estimator recovers the treatment effect.** If the
treated unit's observed outcome in period `t` is `Y_1t(0) + α_t` and the donors'
observed outcomes are their untreated outcomes, then under the hypotheses of
`exact`, `Y_1t − ∑ w_j Y_jt = α_t`. -/
theorem estimator_eq_effect (M : FactorModel T r F) {pre : Set T} (hrank : M.PreRank pre)
    {w : J → ℝ} (hw : ∑ j, w j = 1) {Z : J → r → ℝ} {μ : J → F → ℝ} {Z₁ : r → ℝ}
    {μ₁ : F → ℝ} (hZ : ∑ j, w j • Z j = Z₁)
    (hfit : ∀ t ∈ pre, ∑ j, w j * M.y0 (Z j) (μ j) t = M.y0 Z₁ μ₁ t)
    {Y₁ : T → ℝ} {Y : J → T → ℝ} {α : T → ℝ} (hY₁ : ∀ t, Y₁ t = M.y0 Z₁ μ₁ t + α t)
    (hY : ∀ j t, Y j t = M.y0 (Z j) (μ j) t) (t : T) :
    Y₁ t - ∑ j, w j * Y j t = α t := by
  simp only [hY, hY₁, exact M hrank hw hZ hfit t]; ring

/-- **Observable version** (ADH 2010, eq. (2)). Pre-treatment fit is stated on
*observed* outcomes, with no anticipation (`α_t = 0` before treatment): if the
weights reproduce the treated unit's observed pre-treatment outcomes and
covariates, the synthetic-control estimate equals `α_t` in every period. -/
theorem estimator_eq_effect_observed (M : FactorModel T r F) {pre : Set T}
    (hrank : M.PreRank pre) {w : J → ℝ} (hw : ∑ j, w j = 1) {Z : J → r → ℝ} {μ : J → F → ℝ}
    {Z₁ : r → ℝ} {μ₁ : F → ℝ} (hZ : ∑ j, w j • Z j = Z₁)
    {Y₁ : T → ℝ} {Y : J → T → ℝ} {α : T → ℝ} (hY₁ : ∀ t, Y₁ t = M.y0 Z₁ μ₁ t + α t)
    (hY : ∀ j t, Y j t = M.y0 (Z j) (μ j) t) (hnoant : ∀ t ∈ pre, α t = 0)
    (hfit : ∀ t ∈ pre, Y₁ t = ∑ j, w j * Y j t) (t : T) :
    Y₁ t - ∑ j, w j * Y j t = α t := by
  refine estimator_eq_effect M hrank hw hZ (fun s hs => ?_) hY₁ hY t
  have := hfit s hs
  rw [hY₁ s, hnoant s hs, add_zero] at this
  simp only [hY] at this
  exact this.symm

end FactorModel

/-! ### Witnesses -/

namespace Example

/-- One factor, no covariates, two periods; the factor is `0` before treatment
(`false`) and `1` after (`true`). -/
def Mbad : FactorModel Bool Unit Unit where
  δ := fun _ => 0
  θ := fun _ _ => 0
  lam := fun t _ => if t then 1 else 0

/-- **Without the rank condition exact pre-treatment fit is not enough**: one
donor with weight `1` fits the treated unit perfectly before treatment (and
matches its covariates), yet its post-treatment untreated outcome differs. -/
theorem not_exact_without_rank :
    ¬ Mbad.PreRank {false} ∧ (∑ _j : Unit, (1 : ℝ)) = 1 ∧
    (∑ _j : Unit, (1 : ℝ) • (0 : Unit → ℝ)) = 0 ∧
    (∀ t ∈ ({false} : Set Bool),
      ∑ _j : Unit, (1 : ℝ) * Mbad.y0 0 (fun _ => 0) t = Mbad.y0 0 (fun _ => 1) t) ∧
    ∑ _j : Unit, (1 : ℝ) * Mbad.y0 0 (fun _ => 0) true ≠ Mbad.y0 0 (fun _ => 1) true := by
  refine ⟨fun h => ?_, by simp, by simp, ?_, ?_⟩
  · have := congrFun (h (fun _ => 1) fun t ht => by
      simp only [Set.mem_singleton_iff] at ht; subst ht; simp [Mbad]) ()
    simp at this
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht; subst ht
    simp [FactorModel.y0, Mbad]
  · simp [FactorModel.y0, Mbad]

/-- One factor equal to `1` in both periods. -/
def Mgood : FactorModel Bool Unit Unit where
  δ := fun t => if t then 2 else 1
  θ := fun _ _ => 0
  lam := fun _ _ => 1

/-- **Non-vacuity**: the hypotheses of `FactorModel.exact` are satisfiable with
non-degenerate weights. Two donors with loadings `0` and `2`, equal weights,
and a treated unit with loading `1`. -/
theorem exact_witness :
    Mgood.PreRank {false} ∧ (∑ j : Fin 2, ![(1 : ℝ) / 2, 1 / 2] j) = 1 ∧
    (∑ j : Fin 2, ![(1 : ℝ) / 2, 1 / 2] j • (0 : Unit → ℝ)) = 0 ∧
    (∀ t ∈ ({false} : Set Bool), ∑ j : Fin 2, ![(1 : ℝ) / 2, 1 / 2] j *
      Mgood.y0 0 (fun _ => ![0, 2] j) t = Mgood.y0 0 (fun _ => 1) t) := by
  refine ⟨fun v hv => ?_, by norm_num, by simp, ?_⟩
  · funext u; cases u
    simpa [Mgood] using hv false rfl
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht; subst ht
    simp [FactorModel.y0, Mgood, Fin.sum_univ_two]; norm_num

end Example

end Econ.Causal.SyntheticControl
