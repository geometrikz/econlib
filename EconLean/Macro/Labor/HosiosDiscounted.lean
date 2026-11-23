/-
# The Hosios condition with discounting

Pissarides, *Equilibrium Unemployment Theory* (2000), §8.1; Hosios (1990);
Ljungqvist–Sargent, *Recursive Macroeconomic Theory*, ch. 28 (discrete-time
matching).

`Macro/Labor/DMP.lean` proves the Hosios condition for a planner who maximizes
steady-state net output, which is the `r → 0` case. Here we prove it for any
interest rate `r > 0`, with a planner who maximizes the **present value** of
net output along the whole transition path, starting from any unemployment rate.

**The model (discrete time).** Each period a fraction `s` of jobs separates and
an unemployed worker finds a job with probability `f(θ) = A θ^{1−η}`, where
`θ = v/u` is tightness. Unemployment moves by `u' = u + s (1 − u) − f(θ) u`.
Net output in a period is `y (1 − u) + b u − c θ u` (production, the value of
non-work, minus vacancy costs `c v = c θ u`). Payoffs are discounted by
`δ = 1/(1 + r)`.

**Decentralized equilibrium** (`IsSearchEqm`). Bellman equations for a filled
job `J`, an employed worker `E` and an unemployed worker `U` at a constant wage
`w`; Nash bargaining with worker power `β` (`(1 − β)(E − U) = β J`); free entry
of vacancies (`c = δ q(θ) J`). `isSearchEqm_iff`: an equilibrium exists at `θ`
iff `θ` solves the job-creation condition of `DMP.lean` with interest rate
`r = 1/δ − 1`. So existence, uniqueness and comparative statics carry over.

**The planner** chooses any path of tightness `θ₀, θ₁, …` (`Feasible`: each
`θₜ ≥ 0` and `f(θₜ) ≤ 1`, so unemployment stays in `[0, 1]`).
`isOptimal_stationary`: the stationary path at the equilibrium tightness with
`β = η` is optimal from every initial unemployment rate; `welfare_lt`: any
feasible path that starts with a different tightness does strictly worse when
`u₀ > 0`. The proof is a verification argument: the value function is linear,
`V(u) = α − λ u`, where `λ` is the social value of moving a worker from
unemployment into a job.

**Hosios** (`hosios`): for every `r > 0`, the equilibrium path is optimal iff
`β = η`.

**Deviations.** Discrete time: the job-finding rate is a probability, hence the
feasibility constraint `f(θ) ≤ 1`, which `hosios` assumes at the efficient
tightness (the example at the end shows it holds for a standard calibration).
`IsSearchEqm` does not itself require `f(θ), q(θ) ≤ 1`. It requires `θ > 0`,
which also rules out Lean's junk value `q(0) = A·0^{−η} = 0`. Strict
inferiority (`welfare_lt`) is proved for paths whose *first-period* tightness
differs from `θp`. Cobb–Douglas matching; wages are constant along the stationary equilibrium
(we compare the stationary equilibrium path to all planner paths).
-/
module

public import EconLean.Macro.Labor.DMP
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

noncomputable section

namespace Econ
namespace DMP

open Set Filter Topology Real Finset

/-- A discrete-time matching economy: the DMP primitives plus a discount
factor `δ ∈ (0, 1)`. -/
structure Discrete extends Economy where
  /-- Discount factor, `δ = 1/(1 + r)`. -/
  δ : ℝ
  hδ₀ : 0 < δ
  hδ₁ : δ < 1
  /-- In discrete time the separation rate is a probability. -/
  hs₁ : s ≤ 1

namespace Discrete

variable (D : Discrete)

/-- The interest rate `r = 1/δ − 1`. -/
def rate : ℝ := 1 / D.δ - 1

theorem rate_pos : 0 < D.rate := by
  have := D.hδ₀; have := D.hδ₁
  unfold rate; rw [sub_pos, lt_div_iff₀ D.hδ₀]; linarith

theorem findRate_nonneg {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ D.findRate θ :=
  mul_nonneg D.hA.le (rpow_nonneg hθ _)

/-! ## Decentralized equilibrium -/

/-- A **stationary search equilibrium** at tightness `θ` with worker bargaining
power `β`: values `J` (filled job), `E` (employed), `U` (unemployed) and the
wage `w` satisfy the Bellman equations, Nash bargaining and free entry. Matches
formed this period produce from next period on. -/
structure IsSearchEqm (β θ J E U w : ℝ) : Prop where
  pos : 0 < θ
  firm : J = D.y - w + D.δ * (1 - D.s) * J
  worker : E = w + D.δ * ((1 - D.s) * E + D.s * U)
  unemployed : U = D.b + D.δ * (D.findRate θ * E + (1 - D.findRate θ) * U)
  nash : (1 - β) * (E - U) = β * J
  freeEntry : D.c = D.δ * D.fillRate θ * J

/-- The job-creation condition at `r = 1/δ − 1`, multiplied by `δ q(θ)`. -/
theorem jc_rate {β θ : ℝ} (hθ : 0 < θ) :
    D.jc D.rate β θ * (D.δ * D.fillRate θ) =
      D.c * (1 - D.δ * (1 - D.s) + D.δ * β * D.findRate θ) := by
  have hP : 0 < θ ^ D.η := rpow_pos_of_pos hθ _
  have hq : D.fillRate θ * θ ^ D.η = D.A := by
    simp only [Economy.fillRate, rpow_neg hθ.le]; field_simp
  have hf : D.findRate θ = θ * D.fillRate θ := D.findRate_eq hθ
  have hA := D.hA; have hδ := D.hδ₀
  have hq0 : 0 < D.fillRate θ := mul_pos D.hA (rpow_pos_of_pos hθ _)
  rw [hf]; simp only [Economy.jc, rate]
  rw [← hq]
  field_simp
  ring

/-- **Equilibrium = job creation at `r = 1/δ − 1`.** A search equilibrium
exists at `θ` iff `θ` solves the job-creation condition of `DMP.lean` with
interest rate `r = 1/δ − 1`. -/
theorem isSearchEqm_iff {β θ : ℝ} (hβ₀ : 0 ≤ β) :
    (∃ J E U w, D.IsSearchEqm β θ J E U w) ↔ D.IsEquilibrium D.rate β θ := by
  have hδ := D.hδ₀; have hδ1 := D.hδ₁; have hs := D.hs
  constructor
  · rintro ⟨J, E, U, w, h⟩
    refine ⟨h.pos, ?_⟩
    have hq : 0 < D.fillRate θ := mul_pos D.hA (rpow_pos_of_pos h.pos _)
    have hk := D.jc_rate (β := β) h.pos
    have hf := D.findRate_nonneg (θ := θ) h.pos.le
    have key : D.c * (1 - D.δ * (1 - D.s) + D.δ * β * D.findRate θ) =
        D.δ * D.fillRate θ * ((1 - β) * (D.y - D.b)) := by
      rw [h.freeEntry]
      have := h.firm; have := h.worker; have := h.unemployed; have := h.nash
      linear_combination (D.δ * D.fillRate θ) * ((1 - β) * h.firm + (1 - β) * h.worker
        - (1 - β) * h.unemployed - (1 - D.δ * (1 - D.s) + D.δ * D.findRate θ) * h.nash)
    have hpos : 0 < D.δ * D.fillRate θ := mul_pos hδ hq
    rw [← hk] at key
    exact mul_right_cancel₀ hpos.ne' (key.trans (mul_comm _ _))
  · rintro ⟨hθ, hjc⟩
    have hq : 0 < D.fillRate θ := mul_pos D.hA (rpow_pos_of_pos hθ _)
    have hf := D.findRate_nonneg (θ := θ) hθ.le
    set f := D.findRate θ
    set K := 1 - D.δ * (1 - D.s) + D.δ * β * f
    have hK : 0 < K := by
      have : D.δ * (1 - D.s) < 1 := by nlinarith
      have : 0 ≤ D.δ * β * f := by positivity
      linarith
    set S := (D.y - D.b) / K
    have hS : S * K = D.y - D.b := div_mul_cancel₀ _ hK.ne'
    have hc : D.c * K = D.δ * D.fillRate θ * ((1 - β) * (D.y - D.b)) := by
      rw [← D.jc_rate hθ, hjc]; ring
    refine ⟨(1 - β) * S, (D.b + D.δ * f * (β * S)) / (1 - D.δ) + β * S,
      (D.b + D.δ * f * (β * S)) / (1 - D.δ), D.y - (1 - D.δ * (1 - D.s)) * ((1 - β) * S),
      ⟨hθ, by ring, ?_, ?_, by ring, ?_⟩⟩
    · have h1 : (1 - D.δ) ≠ 0 := by linarith
      field_simp
      linear_combination (1 - D.δ) * hS
    · have h1 : (1 - D.δ) ≠ 0 := by linarith
      field_simp
      ring
    · rw [← mul_left_inj' hK.ne', hc, mul_assoc, mul_assoc, ← hS]; ring

/-- **Existence and uniqueness of the search equilibrium.** -/
theorem existsUnique_searchEqm {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    ∃! θ, ∃ J E U w, D.IsSearchEqm β θ J E U w := by
  simp_rw [D.isSearchEqm_iff hβ₀]
  exact D.existsUnique_equilibrium D.rate_pos.le hβ₀ hβ₁

/-! ## The planner -/

/-- Unemployment next period. -/
def next (u θ : ℝ) : ℝ := u + D.s * (1 - u) - D.findRate θ * u

/-- The unemployment path from `u₀` under the tightness path `θ`. -/
def upath (u₀ : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => u₀
  | t + 1 => D.next (upath u₀ θ t) (θ t)

/-- Net output in a period: `y (1 − u) + b u − c θ u`. -/
def reward (u θ : ℝ) : ℝ := D.y * (1 - u) + D.b * u - D.c * θ * u

/-- A tightness path is feasible if `θₜ ≥ 0` and the job-finding rate is a
probability, `f(θₜ) ≤ 1` (matches cannot exceed the unemployed). -/
def Feasible (θ : ℕ → ℝ) : Prop := ∀ t, 0 ≤ θ t ∧ D.findRate (θ t) ≤ 1

/-- Present value of net output from `u₀` under `θ`. -/
def welfare (u₀ : ℝ) (θ : ℕ → ℝ) : ℝ := ∑' t, D.δ ^ t * D.reward (D.upath u₀ θ t) (θ t)

/-- `θ` is optimal from `u₀`: feasible, and no feasible path gives more welfare. -/
def IsOptimal (u₀ : ℝ) (θ : ℕ → ℝ) : Prop :=
  D.Feasible θ ∧ ∀ θ', D.Feasible θ' → D.welfare u₀ θ' ≤ D.welfare u₀ θ

theorem upath_mem {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1) {θ : ℕ → ℝ} (hθ : D.Feasible θ) :
    ∀ t, D.upath u₀ θ t ∈ Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact hu
  | succ t ih =>
    obtain ⟨h0, h1⟩ := ih
    have hf := D.findRate_nonneg (hθ t).1
    have hsf := (hθ t).2
    have hs := D.hs
    have hs1 := D.hs₁
    simp only [upath, next]
    -- `u' = s (1 − u) + (1 − f) u` is a convex combination of `s` and `1 − f`
    constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 hsf), mul_nonneg (sub_nonneg.2 h1) hs.le,
      mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hs1), mul_nonneg h0 hf]

/-- Feasible tightness is bounded. -/
theorem le_bound {θ : ℝ} (h0 : 0 ≤ θ) (h1 : D.findRate θ ≤ 1) :
    θ ≤ (1 / D.A) ^ (1 - D.η)⁻¹ := by
  have hη : 0 < 1 - D.η := by linarith [D.hη₁]
  have hle : θ ^ (1 - D.η) ≤ 1 / D.A := by
    rw [le_div_iff₀ D.hA]; simp only [Economy.findRate] at h1; linarith
  calc θ = (θ ^ (1 - D.η)) ^ (1 - D.η)⁻¹ := (rpow_rpow_inv h0 hη.ne').symm
    _ ≤ (1 / D.A) ^ (1 - D.η)⁻¹ :=
      rpow_le_rpow (rpow_nonneg h0 _) hle (inv_nonneg.2 hη.le)

theorem summable_welfare {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1) {θ : ℕ → ℝ} (hθ : D.Feasible θ) :
    Summable fun t => D.δ ^ t * D.reward (D.upath u₀ θ t) (θ t) := by
  set M := |D.y| + |D.b| + D.c * (1 / D.A) ^ (1 - D.η)⁻¹
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one D.hδ₀.le D.hδ₁).mul_right M) fun t => ?_
  obtain ⟨u0, u1⟩ := D.upath_mem hu hθ t
  have hb := D.le_bound (hθ t).1 (hθ t).2
  have hθ0 := (hθ t).1
  set u := D.upath u₀ θ t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos D.hδ₀ t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos D.hδ₀ t).le
  have hc := D.hc
  unfold reward
  have e1 : |D.y * (1 - u)| ≤ |D.y| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith)
  have e2 : |D.b * u| ≤ |D.b| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith)
  have e3 : |D.c * θ t * u| ≤ D.c * (1 / D.A) ^ (1 - D.η)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    calc D.c * θ t * u ≤ D.c * θ t * 1 := by gcongr
      _ ≤ D.c * (1 / D.A) ^ (1 - D.η)⁻¹ := by rw [mul_one]; gcongr
  calc |D.y * (1 - u) + D.b * u - D.c * θ t * u|
      ≤ |D.y * (1 - u) + D.b * u| + |D.c * θ t * u| := abs_sub _ _
    _ ≤ |D.y * (1 - u)| + |D.b * u| + |D.c * θ t * u| := by gcongr; exact abs_add_le _ _
    _ ≤ M := by linarith

/-! ### The verification argument -/

section Verification

variable {θp : ℝ}

/-- The social value of employment, `λ = (y − b)/(1 − δ(1 − s) + δ η f(θp))`. -/
def shadow (θp : ℝ) : ℝ :=
  (D.y - D.b) / (1 - D.δ * (1 - D.s) + D.δ * D.η * D.findRate θp)

/-- The planner's value function `V(u) = α − λ u`, `α = (y − δ λ s)/(1 − δ)`. -/
def value (θp u : ℝ) : ℝ :=
  (D.y - D.δ * D.shadow θp * D.s) / (1 - D.δ) - D.shadow θp * u

/-- The one-period gap: `r(u, θ) + δ V(u') − V(u)`. -/
def gap (θp u θ : ℝ) : ℝ := D.reward u θ + D.δ * D.value θp (D.next u θ) - D.value θp u

theorem gap_eq (hp : D.IsEquilibrium D.rate D.η θp) (u θ : ℝ) :
    D.gap θp u θ = u * ((D.δ * D.shadow θp * D.findRate θ - D.c * θ) -
      (D.δ * D.shadow θp * D.findRate θp - D.c * θp)) := by
  have hθ := hp.1
  have hf := D.findRate_nonneg hθ.le
  have hδ := D.hδ₀; have hδ1 := D.hδ₁; have hη := D.hη₀
  have hK : 0 < 1 - D.δ * (1 - D.s) + D.δ * D.η * D.findRate θp := by
    have : D.δ * (1 - D.s) < 1 := by nlinarith [D.hs]
    have : 0 ≤ D.δ * D.η * D.findRate θp := by positivity
    linarith
  have hlam : D.shadow θp * (1 - D.δ * (1 - D.s) + D.δ * D.η * D.findRate θp) = D.y - D.b :=
    div_mul_cancel₀ _ hK.ne'
  -- planner's FOC: `c θp = δ λ (1 − η) f(θp)`
  have hc : D.c * θp = D.δ * D.shadow θp * (1 - D.η) * D.findRate θp := by
    have hk := D.jc_rate (β := D.η) hθ
    rw [hp.2] at hk
    have hfq : D.findRate θp = θp * D.fillRate θp := D.findRate_eq hθ
    have hq : 0 < D.fillRate θp := mul_pos D.hA (rpow_pos_of_pos hθ _)
    -- `c K = δ q (1 − η)(y − b) = δ q (1 − η) λ K`
    have : D.c = D.δ * D.fillRate θp * (1 - D.η) * D.shadow θp := by
      apply mul_right_cancel₀ hK.ne'
      rw [← hk, mul_assoc _ (D.shadow θp), hlam]; ring
    rw [this, hfq]; ring
  have h1 : (1 - D.δ) ≠ 0 := by linarith
  simp only [gap, value, reward, next]
  field_simp
  linear_combination (1 - D.δ) * u * hlam - (1 - D.δ) * u * hc

/-- Concavity of `f`: `f(θ) ≤ f(θp) + f'(θp)(θ − θp)`, strictly if `θ ≠ θp`. -/
theorem findRate_tangent (hθp : 0 < θp) {θ : ℝ} (hθ : 0 ≤ θ) :
    D.findRate θ ≤ D.findRate θp + (1 - D.η) * D.fillRate θp * (θ - θp) ∧
    (θ ≠ θp → D.findRate θ < D.findRate θp + (1 - D.η) * D.fillRate θp * (θ - θp)) := by
  have hp1 : 0 < 1 - D.η := by linarith [D.hη₁]
  have hp2 : 1 - D.η < 1 := by linarith [D.hη₀]
  have hx : -1 ≤ θ / θp - 1 := by have := div_nonneg hθ hθp.le; linarith
  have hθeq : θ = θp * (1 + (θ / θp - 1)) := by field_simp; ring
  have hP := rpow_pos_of_pos hθp (1 - D.η)
  have hrw : D.findRate θ = D.A * θp ^ (1 - D.η) * (1 + (θ / θp - 1)) ^ (1 - D.η) := by
    simp only [Economy.findRate]
    conv_lhs => rw [hθeq]
    rw [mul_rpow hθp.le (by linarith), mul_assoc]
  have hrhs : D.findRate θp + (1 - D.η) * D.fillRate θp * (θ - θp) =
      D.A * θp ^ (1 - D.η) * (1 + (1 - D.η) * (θ / θp - 1)) := by
    simp only [Economy.findRate, Economy.fillRate]
    rw [rpow_sub hθp, rpow_neg hθp.le, rpow_one]
    field_simp
  have hAP : 0 < D.A * θp ^ (1 - D.η) := mul_pos D.hA hP
  rw [hrw, hrhs]
  refine ⟨mul_le_mul_of_nonneg_left (rpow_one_add_le_one_add_mul_self hx hp1.le hp2.le) hAP.le,
    fun hne => mul_lt_mul_of_pos_left
      (rpow_one_add_lt_one_add_mul_self hx ?_ hp1 hp2) hAP⟩
  intro h
  apply hne
  have : θ / θp = 1 := by linarith
  field_simp at this; linarith

theorem shadow_pos (hp : D.IsEquilibrium D.rate D.η θp) : 0 < D.shadow θp := by
  have hf := D.findRate_nonneg hp.1.le
  have hδ := D.hδ₀; have hδ1 := D.hδ₁; have hη := D.hη₀
  have : D.δ * (1 - D.s) < 1 := by nlinarith [D.hs]
  have : 0 ≤ D.δ * D.η * D.findRate θp := by positivity
  exact div_pos (by linarith [D.hyb]) (by linarith)

/-- The planner's first-order condition `δ λ f'(θp) = c`. -/
theorem foc (hp : D.IsEquilibrium D.rate D.η θp) :
    D.δ * D.shadow θp * ((1 - D.η) * D.fillRate θp) = D.c := by
  have hθ := hp.1
  have hq : 0 < D.fillRate θp := mul_pos D.hA (rpow_pos_of_pos hθ _)
  have hf := D.findRate_nonneg hθ.le
  have hδ := D.hδ₀; have hδ1 := D.hδ₁; have hη := D.hη₀
  have hK : 0 < 1 - D.δ * (1 - D.s) + D.δ * D.η * D.findRate θp := by
    have : D.δ * (1 - D.s) < 1 := by nlinarith [D.hs]
    have : 0 ≤ D.δ * D.η * D.findRate θp := by positivity
    linarith
  have hlam : D.shadow θp * (1 - D.δ * (1 - D.s) + D.δ * D.η * D.findRate θp) = D.y - D.b :=
    div_mul_cancel₀ _ hK.ne'
  have hk := D.jc_rate (β := D.η) hθ
  rw [hp.2] at hk
  apply mul_right_cancel₀ hK.ne'
  rw [← hk, ← hlam]; ring

theorem gap_le (hp : D.IsEquilibrium D.rate D.η θp) {u θ : ℝ} (hu : 0 ≤ u) (hθ : 0 ≤ θ) :
    D.gap θp u θ ≤ 0 := by
  rw [D.gap_eq hp]
  have ht := (D.findRate_tangent hp.1 hθ).1
  have hfoc := D.foc hp
  have hlam := D.shadow_pos hp
  have hδ := D.hδ₀
  apply mul_nonpos_of_nonneg_of_nonpos hu
  have := mul_le_mul_of_nonneg_left ht (mul_pos hδ hlam).le
  have h2 : D.δ * D.shadow θp * (D.findRate θp + (1 - D.η) * D.fillRate θp * (θ - θp)) =
      D.δ * D.shadow θp * D.findRate θp + D.c * (θ - θp) := by rw [← hfoc]; ring
  linarith

theorem gap_lt (hp : D.IsEquilibrium D.rate D.η θp) {u θ : ℝ} (hu : 0 < u) (hθ : 0 ≤ θ)
    (hne : θ ≠ θp) : D.gap θp u θ < 0 := by
  rw [D.gap_eq hp]
  have ht := (D.findRate_tangent hp.1 hθ).2 hne
  have hfoc := D.foc hp
  have hlam := D.shadow_pos hp
  have hδ := D.hδ₀
  apply mul_neg_of_pos_of_neg hu
  have := mul_lt_mul_of_pos_left ht (mul_pos hδ hlam)
  have h2 : D.δ * D.shadow θp * (D.findRate θp + (1 - D.η) * D.fillRate θp * (θ - θp)) =
      D.δ * D.shadow θp * D.findRate θp + D.c * (θ - θp) := by rw [← hfoc]; ring
  linarith

theorem gap_self (hp : D.IsEquilibrium D.rate D.η θp) (u : ℝ) : D.gap θp u θp = 0 := by
  rw [D.gap_eq hp]; ring

/-- Telescoping: discounted rewards up to `T` plus the discounted continuation
value equal `V(u₀)` plus the discounted gaps. -/
theorem telescope (u₀ : ℝ) (θ : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ range T, D.δ ^ t * D.reward (D.upath u₀ θ t) (θ t) +
      D.δ ^ T * D.value θp (D.upath u₀ θ T) =
    D.value θp u₀ + ∑ t ∈ range T, D.δ ^ t * D.gap θp (D.upath u₀ θ t) (θ t) := by
  induction T with
  | zero => simp [upath]
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ]
    simp only [gap, upath] at ih ⊢
    rw [pow_succ]
    linarith

theorem tendsto_tail {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1)
    {θ : ℕ → ℝ} (hθ : D.Feasible θ) :
    Tendsto (fun T => D.δ ^ T * D.value θp (D.upath u₀ θ T)) atTop (𝓝 0) := by
  set B := |(D.y - D.δ * D.shadow θp * D.s) / (1 - D.δ)| + |D.shadow θp|
  have hb : ∀ T, |D.value θp (D.upath u₀ θ T)| ≤ B := fun T => by
    obtain ⟨h0, h1⟩ := D.upath_mem hu hθ T
    unfold value
    calc _ ≤ |(D.y - D.δ * D.shadow θp * D.s) / (1 - D.δ)| + |D.shadow θp * D.upath u₀ θ T| :=
          abs_sub _ _
      _ ≤ B := by
          rw [abs_mul]
          have : |D.upath u₀ θ T| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          have := mul_le_mul_of_nonneg_left this (abs_nonneg (D.shadow θp))
          linarith
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one D.hδ₀.le D.hδ₁
  have h0' : Tendsto (fun T => D.δ ^ T * B) atTop (𝓝 0) := by simpa using h0.mul_const B
  refine squeeze_zero_norm (fun T => ?_) h0'
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos D.hδ₀ T)]
  exact mul_le_mul_of_nonneg_left (hb T) (pow_pos D.hδ₀ T).le

/-- Welfare of a feasible path: `W = V(u₀) + Σ δᵗ gapₜ`, as a limit. -/
theorem tendsto_gaps {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1)
    {θ : ℕ → ℝ} (hθ : D.Feasible θ) :
    Tendsto (fun T => D.value θp u₀ + ∑ t ∈ range T, D.δ ^ t * D.gap θp (D.upath u₀ θ t) (θ t))
      atTop (𝓝 (D.welfare u₀ θ)) := by
  have h1 := (D.summable_welfare hu hθ).hasSum.tendsto_sum_nat
  have h2 := h1.add (D.tendsto_tail (θp := θp) hu hθ)
  rw [add_zero] at h2
  exact h2.congr fun T => D.telescope u₀ θ T

/-- The stationary path at `θp` attains `V(u₀)`. -/
theorem welfare_stationary (hp : D.IsEquilibrium D.rate D.η θp)
    (hfp : D.findRate θp ≤ 1) {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1) :
    D.welfare u₀ (fun _ => θp) = D.value θp u₀ := by
  have hθ : D.Feasible fun _ => θp := fun _ => ⟨hp.1.le, hfp⟩
  have h := D.tendsto_gaps (θp := θp) hu hθ
  simp only [D.gap_self hp, mul_zero, sum_const_zero, add_zero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Every feasible path gives at most `V(u₀)`. -/
theorem welfare_le (hp : D.IsEquilibrium D.rate D.η θp) {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1)
    {θ : ℕ → ℝ} (hθ : D.Feasible θ) : D.welfare u₀ θ ≤ D.value θp u₀ := by
  refine le_of_tendsto_of_tendsto' (D.tendsto_gaps (θp := θp) hu hθ) tendsto_const_nhds fun T => ?_
  have : ∑ t ∈ range T, D.δ ^ t * D.gap θp (D.upath u₀ θ t) (θ t) ≤ 0 :=
    sum_nonpos fun t _ => mul_nonpos_of_nonneg_of_nonpos (pow_pos D.hδ₀ t).le
      (D.gap_le hp (D.upath_mem hu hθ t).1 (hθ t).1)
  linarith

/-- A feasible path whose first-period tightness differs from `θp` gives
strictly less than `V(u₀)` when `u₀ > 0`. -/
theorem welfare_lt_value (hp : D.IsEquilibrium D.rate D.η θp) {u₀ : ℝ} (hu : u₀ ∈ Ioc (0 : ℝ) 1)
    {θ : ℕ → ℝ} (hθ : D.Feasible θ) (hne : θ 0 ≠ θp) : D.welfare u₀ θ < D.value θp u₀ := by
  have hu' : u₀ ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
  have g0 : D.gap θp u₀ (θ 0) < 0 := D.gap_lt hp hu.1 (hθ 0).1 hne
  have hle : D.welfare u₀ θ ≤ D.value θp u₀ + D.gap θp u₀ (θ 0) := by
    refine le_of_tendsto_of_tendsto (D.tendsto_gaps (θp := θp) hu' hθ) tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    rw [sum_range_succ']
    have : ∑ t ∈ range n, D.δ ^ (t + 1) * D.gap θp (D.upath u₀ θ (t + 1)) (θ (t + 1)) ≤ 0 :=
      sum_nonpos fun t _ => mul_nonpos_of_nonneg_of_nonpos (pow_pos D.hδ₀ _).le
        (D.gap_le hp (D.upath_mem hu' hθ _).1 (hθ _).1)
    have e : D.gap θp (D.upath u₀ θ 0) (θ 0) = D.gap θp u₀ (θ 0) := rfl
    rw [pow_zero, one_mul, e]
    linarith
  linarith

end Verification

/-! ## Efficiency and the Hosios condition -/

/-- **The efficient path.** Let `θp` solve the job-creation condition at
`r = 1/δ − 1` with `β = η`, and be feasible. Then staying at `θp` forever is
optimal from every initial unemployment rate `u₀ ∈ [0, 1]`. -/
theorem isOptimal_stationary {θp : ℝ} (hp : D.IsEquilibrium D.rate D.η θp)
    (hfp : D.findRate θp ≤ 1) {u₀ : ℝ} (hu : u₀ ∈ Icc (0 : ℝ) 1) :
    D.IsOptimal u₀ (fun _ => θp) :=
  ⟨fun _ => ⟨hp.1.le, hfp⟩, fun _ hθ => (D.welfare_le hp hu hθ).trans
    (D.welfare_stationary hp hfp hu).ge⟩

/-- **Any other first-period tightness is strictly worse.** -/
theorem welfare_lt {θp : ℝ} (hp : D.IsEquilibrium D.rate D.η θp)
    (hfp : D.findRate θp ≤ 1) {u₀ : ℝ} (hu : u₀ ∈ Ioc (0 : ℝ) 1) {θ : ℕ → ℝ}
    (hθ : D.Feasible θ) (hne : θ 0 ≠ θp) : D.welfare u₀ θ < D.welfare u₀ (fun _ => θp) := by
  rw [D.welfare_stationary hp hfp ⟨hu.1.le, hu.2⟩]
  exact D.welfare_lt_value hp hu hθ hne

/-- **The Hosios condition with discounting.** Take any interest rate
`r = 1/δ − 1 > 0` and worker bargaining power `β ∈ [0, 1)`. Let `θe` be the
search equilibrium tightness and `θp` the tightness that solves the
job-creation condition with `β = η`, and suppose `θp` is feasible. Then, from any
initial unemployment rate `u₀ ∈ (0, 1]`, the equilibrium path is optimal iff
`β = η`. -/
theorem hosios {β θe θp u₀ : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (he : ∃ J E U w, D.IsSearchEqm β θe J E U w)
    (hp : D.IsEquilibrium D.rate D.η θp) (hfp : D.findRate θp ≤ 1)
    (hu : u₀ ∈ Ioc (0 : ℝ) 1) :
    D.IsOptimal u₀ (fun _ => θe) ↔ β = D.η := by
  rw [D.isSearchEqm_iff hβ₀] at he
  have hη₀ := D.hη₀; have hη₁ := D.hη₁
  constructor
  · intro hopt
    have heq : θe = θp := by
      by_contra hne
      have h1 := D.welfare_lt hp hfp hu hopt.1 hne
      have h2 := hopt.2 _ (fun _ => ⟨hp.1.le, hfp⟩)
      linarith
    subst heq
    by_contra hβ
    rcases lt_or_gt_of_ne hβ with h | h
    · exact (D.equilibrium_strictAnti_β D.rate_pos.le hβ₀ h he hp).ne' rfl
    · exact (D.equilibrium_strictAnti_β D.rate_pos.le hη₀.le h hp he).ne' rfl
  · rintro rfl
    have : θe = θp := (D.existsUnique_equilibrium D.rate_pos.le hβ₀ hβ₁).unique he hp
    subst this
    exact D.isOptimal_stationary hp hfp ⟨hu.1.le, hu.2⟩

/-- **Non-vacuity.** With `A = 1/4`, `η = 1/2`, `s = 1/10`, `c = 1`, `y = 1`,
`b = 0` and `δ = 9/10`, the efficient tightness exists and is feasible, so
`hosios` applies. -/
example : ∃ θp, (⟨⟨1 / 4, 1 / 2, 1 / 10, 1, 1, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩, 9 / 10, by norm_num, by norm_num, by norm_num⟩ : Discrete).IsEquilibrium
      (Discrete.rate ⟨⟨1 / 4, 1 / 2, 1 / 10, 1, 1, 0, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num⟩, 9 / 10, by norm_num, by norm_num, by norm_num⟩) (1 / 2) θp ∧
      1 / 4 * θp ^ (1 - 1 / 2 : ℝ) ≤ 1 := by
  set D : Discrete := ⟨⟨1 / 4, 1 / 2, 1 / 10, 1, 1, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩, 9 / 10, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨θp, hp, -⟩ := D.existsUnique_equilibrium D.rate_pos.le (β := 1 / 2) (by norm_num)
    (by norm_num)
  refine ⟨θp, hp, ?_⟩
  obtain ⟨hθ, hjc⟩ := hp
  have hr := D.rate_pos
  -- `jc ≥ β c θ`, so `θ/2 ≤ 1/2`
  have h1 : θp ≤ 1 := by
    have : 0 ≤ D.c * (D.rate + D.s) * θp ^ D.η / D.A := by
      have := rpow_nonneg hθ.le D.η
      have : 0 < D.rate + D.s := by linarith [D.hs]
      have := D.hc; have := D.hA; positivity
    simp only [Economy.jc] at hjc
    have e1 : D.c = 1 := rfl
    have e2 : D.y - D.b = 1 := by norm_num [D]
    rw [e1, e2] at hjc
    linarith
  have : θp ^ (1 - 1 / 2 : ℝ) ≤ 1 := rpow_le_one hθ.le h1 (by norm_num)
  linarith

end Discrete

end DMP
end Econ

end
