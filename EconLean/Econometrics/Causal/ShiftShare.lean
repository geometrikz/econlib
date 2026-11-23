/-
# Shift-share (Bartik) instruments

Borusyak, Hull and Jaravel (2022), *ReStud* 89, "Quasi-Experimental Shift-Share
Research Designs", Prop. 1 and §3; Goldsmith-Pinkham, Sorkin and Swift (2020),
*AER* 110, "Bartik Instruments: What, When, Why, and How", Prop. 1 and §3.

**The economics.** Locations `l` have exposure shares `s_ln` to industries `n`
and regression weights `e_l`. The shift-share instrument is
`z_l = ∑_n s_ln g_n` for industry shocks `g_n`. In `y_l = β x_l + ε_l` the
shift-share IV estimator is `β̂ = ∑_l e_l z_l y_l / ∑_l e_l z_l x_l`.

* **BHJ equivalence** (Prop. 1). For any location variable `v`,
  `∑_l e_l z_l v_l = ∑_n s_n g_n v̄_n`, where `s_n = ∑_l e_l s_ln` is industry
  `n`'s total exposure and `v̄_n = ∑_l e_l s_ln v_l / s_n` its exposure-weighted
  average. Hence `β̂` equals the industry-level IV estimator that instruments
  `x̄_n` with `g_n` in a regression of `ȳ_n` on `x̄_n`, weighted by `s_n`.
* **BHJ identification** (§3, Assumption 1). If shocks are as good as random,
  `E[g_n] = μ` for every `n` holding the shares, weights and unobservables fixed,
  then `E[∑_l e_l z_l ε_l] = μ ∑_l e_l S_l ε_l` with `S_l = ∑_n s_ln`. So the
  exclusion restriction holds when shares are complete (`S_l = 1`) and
  `∑_l e_l ε_l = 0` (a constant is included), or when `μ = 0`.
* **GPSS Rotemberg decomposition** (Prop. 1 / eq. (5)). With one shock
  vector, `β̂ = ∑_n α_n β̂_n`, where `β̂_n = ∑_l s_ln y_l / ∑_l s_ln x_l` is
  the just-identified IV estimate using share `n` alone as the instrument and
  `α_n = g_n ∑_l s_ln x_l / ∑_n' g_n' ∑_l s_ln' x_l`. The weights sum to one but
  can be negative (`Example.rotemberg_negative`).

**Encoding and scope.** Finite sets of locations `L` and industries `N`. The
identification statement conditions on everything but the shocks by treating
shares, weights and `ε` as fixed and the shocks as random variables
`g : Ω → N → ℝ`. Large-sample consistency is not formalised. The GPSS
decomposition is stated without controls and with equal location weights;
with controls it applies to the residualised `x`, `y` (Frisch–Waugh–Lovell,
`OLS.fwl`).
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ.Causal.ShiftShare

open MeasureTheory

variable {L N : Type*} [Fintype L] [Fintype N]

/-- The shift-share instrument `z_l = ∑_n s_ln g_n`. -/
def bartik (s : L → N → ℝ) (g : N → ℝ) (l : L) : ℝ :=
  ∑ n, s l n * g n

/-- Industry exposure `s_n = ∑_l e_l s_ln`. -/
def exposure (e : L → ℝ) (s : L → N → ℝ) (n : N) : ℝ :=
  ∑ l, e l * s l n

/-- Exposure-weighted industry average `v̄_n = ∑_l e_l s_ln v_l / s_n`. -/
noncomputable def shockAvg (e : L → ℝ) (s : L → N → ℝ) (v : L → ℝ) (n : N) : ℝ :=
  (∑ l, e l * s l n * v l) / exposure e s n

/-- The shift-share IV estimator `∑ e z y / ∑ e z x`. -/
noncomputable def ssiv (e : L → ℝ) (s : L → N → ℝ) (g : N → ℝ) (x y : L → ℝ) : ℝ :=
  (∑ l, e l * bartik s g l * y l) / ∑ l, e l * bartik s g l * x l

/-- The industry-level IV estimator: regress `ȳ_n` on `x̄_n` with instrument `g_n`
and weights `s_n`. -/
noncomputable def shockIV (e : L → ℝ) (s : L → N → ℝ) (g : N → ℝ) (x y : L → ℝ) : ℝ :=
  (∑ n, exposure e s n * g n * shockAvg e s y n) /
    ∑ n, exposure e s n * g n * shockAvg e s x n

/-- **Location-level moments are industry-level moments** (BHJ eq. (4)):
`∑_l e_l z_l v_l = ∑_n s_n g_n v̄_n`, provided every industry has nonzero
exposure. -/
theorem sum_bartik_mul {e : L → ℝ} {s : L → N → ℝ} (hs : ∀ n, exposure e s n ≠ 0)
    (g : N → ℝ) (v : L → ℝ) :
    ∑ l, e l * bartik s g l * v l = ∑ n, exposure e s n * g n * shockAvg e s v n := by
  have h : ∀ n, exposure e s n * g n * shockAvg e s v n = ∑ l, e l * s l n * v l * g n := by
    intro n
    rw [shockAvg, ← Finset.sum_mul]
    field_simp [hs n]
  simp only [h, bartik, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun l _ => by ring

/-- **BHJ Proposition 1**: the shift-share IV estimator equals the industry-level
IV estimator. -/
theorem ssiv_eq_shockIV {e : L → ℝ} {s : L → N → ℝ} (hs : ∀ n, exposure e s n ≠ 0)
    (g : N → ℝ) (x y : L → ℝ) : ssiv e s g x y = shockIV e s g x y := by
  rw [ssiv, shockIV, sum_bartik_mul hs, sum_bartik_mul hs]

/-- In `y = βx + ε` the shift-share IV estimator has error
`∑ e z ε / ∑ e z x` (first stage nonzero). -/
theorem ssiv_sub {e : L → ℝ} {s : L → N → ℝ} {g : N → ℝ} {x ε : L → ℝ} (β : ℝ)
    (hfs : ∑ l, e l * bartik s g l * x l ≠ 0) :
    ssiv e s g x (fun l => β * x l + ε l) - β =
      (∑ l, e l * bartik s g l * ε l) / ∑ l, e l * bartik s g l * x l := by
  have h : ∑ l, e l * bartik s g l * (β * x l + ε l)
      = β * ∑ l, e l * bartik s g l * x l + ∑ l, e l * bartik s g l * ε l := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [ssiv, h]
  field_simp
  ring

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **BHJ identification** (§3): with shocks as good as random, `E[g_n] = m` for
all `n`, the expected instrument–error moment is `m ∑_l e_l S_l ε_l`, where
`S_l = ∑_n s_ln` is location `l`'s total share. -/
theorem integral_sum_bartik_mul {e : L → ℝ} {s : L → N → ℝ} {ε : L → ℝ} {g : Ω → N → ℝ}
    (hg : ∀ n, Integrable (fun ω => g ω n) μ) {m : ℝ} (hmean : ∀ n, ∫ ω, g ω n ∂μ = m) :
    ∫ ω, ∑ l, e l * bartik s (g ω) l * ε l ∂μ = m * ∑ l, e l * (∑ n, s l n) * ε l := by
  have hexp : ∀ ω, ∑ l, e l * bartik s (g ω) l * ε l
      = ∑ l, ∑ n, (e l * s l n * ε l) * g ω n := by
    intro ω
    simp only [bartik, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun n _ => by ring
  simp only [hexp]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun n _ => (hg n).const_mul _]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun n _ => (hg n).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, hmean]; ring

/-- **Exclusion restriction under complete shares** (BHJ §3): if shocks are as
good as random, shares sum to one in every location and the weighted errors sum
to zero, the instrument is orthogonal to the error in expectation. -/
theorem integral_sum_bartik_mul_eq_zero {e : L → ℝ} {s : L → N → ℝ} {ε : L → ℝ}
    {g : Ω → N → ℝ} (hg : ∀ n, Integrable (fun ω => g ω n) μ) {m : ℝ}
    (hmean : ∀ n, ∫ ω, g ω n ∂μ = m) (hcomplete : ∀ l, ∑ n, s l n = 1)
    (hε : ∑ l, e l * ε l = 0) :
    ∫ ω, ∑ l, e l * bartik s (g ω) l * ε l ∂μ = 0 := by
  rw [integral_sum_bartik_mul hg hmean]
  simp [hcomplete, hε]

end Random

section Rotemberg

/-- The just-identified IV estimate using share `n` as the only instrument:
`β̂_n = ∑_l s_ln y_l / ∑_l s_ln x_l`. -/
noncomputable def shareIV (s : L → N → ℝ) (x y : L → ℝ) (n : N) : ℝ :=
  (∑ l, s l n * y l) / ∑ l, s l n * x l

/-- Rotemberg weight `α_n = g_n ∑_l s_ln x_l / ∑_n' g_n' ∑_l s_ln' x_l`. -/
noncomputable def rotemberg (s : L → N → ℝ) (g : N → ℝ) (x : L → ℝ) (n : N) : ℝ :=
  g n * (∑ l, s l n * x l) / ∑ n', g n' * ∑ l, s l n' * x l

/-- The first stage of the Bartik IV is `∑_n g_n ∑_l s_ln x_l`. -/
lemma sum_bartik_mul_eq (s : L → N → ℝ) (g : N → ℝ) (v : L → ℝ) :
    ∑ l, bartik s g l * v l = ∑ n, g n * ∑ l, s l n * v l := by
  simp only [bartik, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun l _ => by ring

/-- Rotemberg weights sum to one when the first stage is nonzero. -/
theorem sum_rotemberg {s : L → N → ℝ} {g : N → ℝ} {x : L → ℝ}
    (hfs : ∑ n, g n * ∑ l, s l n * x l ≠ 0) : ∑ n, rotemberg s g x n = 1 := by
  simp only [rotemberg, ← Finset.sum_div]
  exact div_self hfs

/-- **GPSS Rotemberg decomposition** (GPSS 2020, Prop. 1): the Bartik IV
estimator (equal location weights, no controls) is the Rotemberg-weighted sum of
the share-by-share just-identified IV estimates, provided every share has a
nonzero first stage. -/
theorem bartik_eq_sum_rotemberg {s : L → N → ℝ} {g : N → ℝ} {x y : L → ℝ}
    (hk : ∀ n, ∑ l, s l n * x l ≠ 0) :
    ssiv (fun _ => 1) s g x y = ∑ n, rotemberg s g x n * shareIV s x y n := by
  have h1 : ∀ v : L → ℝ, ∑ l, (fun _ => (1 : ℝ)) l * bartik s g l * v l
      = ∑ n, g n * ∑ l, s l n * v l := fun v => by
    simp only [one_mul]; exact sum_bartik_mul_eq s g v
  rw [ssiv, h1, h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [rotemberg, shareIV]
  field_simp [hk n]

end Rotemberg

namespace Example

/-- Two locations, each fully exposed to one industry. -/
def s : Fin 2 → Fin 2 → ℝ := fun l n => if l = n then 1 else 0

/-- **Rotemberg weights can be negative** (GPSS §3): with shocks `g = (2, −1)`
and `x = (1, 1)` every share has a nonzero first stage, the weights are
`(2, −1)`, and they sum to one. -/
theorem rotemberg_negative :
    (∀ n, ∑ l, s l n * ![1, 1] l ≠ 0) ∧ rotemberg s ![2, -1] ![1, 1] 0 = 2 ∧
      rotemberg s ![2, -1] ![1, 1] 1 = -1 := by
  refine ⟨fun n => ?_, ?_, ?_⟩
  · fin_cases n <;> simp [s]
  · simp [rotemberg, s, Fin.sum_univ_two]; norm_num
  · simp [rotemberg, s, Fin.sum_univ_two]; norm_num

end Example

end Econ.Causal.ShiftShare
