/-
# Romer (1990): expanding varieties

Romer, "Endogenous Technological Change", JPE 1990; Acemoglu, *Introduction to
Modern Economic Growth*, §13.1 (the lab-equipment model); Jones–Vollrath ch. 4–5.

**Technology.** Final output uses labour `L` and `N` varieties of machines:

    Y = (1/(1 − a)) Σ_ν x_ν^{1−a} L^a,       a ∈ (0, 1) the labour share.

A machine costs `ψ = 1 − a` units of output to produce. One unit of output
spent on R&D creates `η` new varieties, and each variety is a perpetual patent
held by a monopolist.

**Equilibrium.**
* Final-good firms demand `x(p) = p^{−1/a} L` of a machine priced `p`
  (`demand_optimal`).
* The monopolist's best price is the markup `p = ψ/(1 − a) = 1`
  (`monopoly_price`), selling `x = L` and earning flow profit `π = a L`.
* Free entry into R&D makes a patent worth `1/η`. With a constant interest rate
  `r`, its value is `π / r`, so `r = η a L` (`freeEntry_iff`).
* On a balanced growth path with log utility, consumption grows at the gross
  rate `β (1 + r)` (the household's Euler equation). We **define**
  `eulerGrowth = β (1 + η a L)`, the Euler-implied growth factor at the
  free-entry interest rate. `household_optimal` derives it: a log-utility
  household whose wealth earns `1 + η a L` optimally lets consumption grow at
  `eulerGrowth`. We do not construct the full decentralized dynamic
  equilibrium (wage income, market clearing) in Lean.

**The planner** chooses machines and consumption every period
(`PlannerPlan`). Its static choice is `x_S = (1 − a)^{−1/a} L > L`
(`planner_static`; the monopoly markup means too few machines), with net
output per variety `a (1 − a)^{−1/a} L`. Its dynamic problem is then an AK
model with gross return `R_S = 1 + η a (1 − a)^{−1/a} L`, so its optimum grows
at `β R_S` (`planner_optimal`, `plannerPlan_attains`).

**Results.** `eulerGrowth_lt_optimal`: the Euler-implied equilibrium growth
factor is strictly below the planner's optimal growth factor, because the
private return to R&D (`η a L`) is below the social return
(`η a (1 − a)^{−1/a} L`). `eulerGrowth_strictMono_L`: equilibrium growth rises with the
size of the labour force.

The planner uses the same machine intensity for every variety (`netOutput`
is per variety); by concavity an asymmetric choice would do no better, but
that is not proved here. Nothing requires `eulerGrowth > 1`, so the formula
can describe shrinking consumption.

`PlannerPlan` allows negative R&D (varieties converted back into output). That
relaxes the planner's problem, so `planner_optimal` bounds the true problem
too. The optimal plan has non-negative R&D exactly when `β R_S ≥ 1`
(`plannerPlan_rd_nonneg`). Optimality is among plans whose lifetime utility
converges (`HasSum`). This is harmless: consumption is bounded by
`R^{t+1} k₀`, so the positive part always converges and any other plan has
utility `−∞`.

**Deviations.** Discrete time; log utility. The equilibrium growth rate uses
the household's log-utility Euler equation along a balanced growth path,
`g = β(1 + r)`, as in the textbook. That is a definition here, while the
planner's growth rate is proved optimal.
-/
module

public import EconLean.Macro.Growth.AK
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace Romer

open Real Finset

/-- **Tangent line for `x^q`, `0 < q < 1`:** `x^q ≤ y^q + q y^{q−1}(x − y)`
for `x ≥ 0`, `y > 0`, strictly if `x ≠ y`. -/
theorem rpow_tangent {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ q ≤ y ^ q + q * y ^ (q - 1) * (x - y) ∧
    (x ≠ y → x ^ q < y ^ q + q * y ^ (q - 1) * (x - y)) := by
  have hs : -1 ≤ x / y - 1 := by have := div_nonneg hx hy.le; linarith
  have hxeq : x = y * (1 + (x / y - 1)) := by field_simp; ring
  have hP := rpow_pos_of_pos hy q
  have hl : x ^ q = y ^ q * (1 + (x / y - 1)) ^ q := by
    conv_lhs => rw [hxeq]
    rw [mul_rpow hy.le (by linarith)]
  have hr : y ^ q + q * y ^ (q - 1) * (x - y) = y ^ q * (1 + q * (x / y - 1)) := by
    rw [rpow_sub hy, rpow_one]; field_simp
  rw [hl, hr]
  refine ⟨mul_le_mul_of_nonneg_left (rpow_one_add_le_one_add_mul_self hs hq₀.le hq₁.le) hP.le,
    fun hne => mul_lt_mul_of_pos_left (rpow_one_add_lt_one_add_mul_self hs ?_ hq₀ hq₁) hP⟩
  intro h; apply hne
  have : x / y = 1 := by linarith
  field_simp at this; linarith

/-- The economy. -/
structure Economy where
  /-- Labour share in final output (Acemoglu's `β`). -/
  a : ℝ
  /-- Labour force. -/
  L : ℝ
  /-- Productivity of R&D: new varieties per unit of output spent. -/
  η : ℝ
  /-- Discount factor. -/
  β : ℝ
  ha₀ : 0 < a
  ha₁ : a < 1
  hL : 0 < L
  hη : 0 < η
  hβ₀ : 0 < β
  hβ₁ : β < 1

namespace Economy

variable (E : Economy)

/-- Marginal cost of a machine, `ψ = 1 − a`. -/
def ψ : ℝ := 1 - E.a

/-- A final-good firm's profit from using `x` units of one machine priced `p`. -/
def finalProfit (p x : ℝ) : ℝ := 1 / (1 - E.a) * x ^ (1 - E.a) * E.L ^ E.a - p * x

/-- Demand for a machine priced `p`: `x(p) = p^{−1/a} L`. -/
def demand (p : ℝ) : ℝ := p ^ (-(1 / E.a)) * E.L

theorem demand_pos {p : ℝ} (hp : 0 < p) : 0 < E.demand p :=
  mul_pos (rpow_pos_of_pos hp _) E.hL

/-- `x(p)^{−a} L^a = p`: the first-order condition of the final-good firm. -/
theorem demand_foc {p : ℝ} (hp : 0 < p) : E.demand p ^ (-E.a) * E.L ^ E.a = p := by
  have ha := E.ha₀
  unfold demand
  rw [mul_rpow (rpow_pos_of_pos hp _).le E.hL.le, ← rpow_mul hp.le, mul_assoc,
    ← rpow_add E.hL]
  simp only [neg_add_cancel, rpow_zero, mul_one]
  rw [show -(1 / E.a) * -E.a = 1 by field_simp, rpow_one]

/-- **Machine demand.** At price `p > 0`, `x(p)` maximizes the final-good
firm's profit, uniquely. -/
theorem demand_optimal {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    E.finalProfit p x ≤ E.finalProfit p (E.demand p) ∧
    (x ≠ E.demand p → E.finalProfit p x < E.finalProfit p (E.demand p)) := by
  have h1a : 0 < 1 - E.a := by linarith [E.ha₁]
  have hq₁ : 1 - E.a < 1 := by linarith [E.ha₀]
  have hd := E.demand_pos hp
  obtain ⟨h1, h2⟩ := rpow_tangent h1a hq₁ hx hd
  have hLa := rpow_pos_of_pos E.hL E.a
  have hc : 0 < 1 / (1 - E.a) * E.L ^ E.a := by positivity
  -- `(1/(1−a)) L^a (1−a) x_d^{−a} = p`
  have hfoc : 1 / (1 - E.a) * E.L ^ E.a * ((1 - E.a) * E.demand p ^ (1 - E.a - 1)) = p := by
    rw [show 1 - E.a - 1 = -E.a by ring]
    calc _ = E.demand p ^ (-E.a) * E.L ^ E.a := by field_simp
      _ = p := E.demand_foc hp
  unfold finalProfit
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hc.le
    nlinarith
  · intro hne
    have := mul_lt_mul_of_pos_left (h2 hne) hc
    nlinarith

/-- A monopolist's profit at price `p`: `(p − ψ) x(p)`. -/
def monoProfit (p : ℝ) : ℝ := (p - E.ψ) * E.demand p

/-- **The monopoly price is the markup `ψ/(1 − a) = 1`**, uniquely; flow profit
is then `π = a L`. -/
theorem monopoly_price {p : ℝ} (hp : 0 < p) :
    E.monoProfit p ≤ E.monoProfit 1 ∧ (p ≠ 1 → E.monoProfit p < E.monoProfit 1) ∧
    E.monoProfit 1 = E.a * E.L := by
  have ha := E.ha₀
  have hρ : 1 < 1 / E.a := by rw [lt_div_iff₀ ha]; linarith [E.ha₁]
  have hs : -1 ≤ p - 1 := by linarith
  have hpp : 0 < p ^ (-(1 / E.a)) := rpow_pos_of_pos hp _
  have hinv : p ^ (1 / E.a) * p ^ (-(1 / E.a)) = 1 := by
    rw [← rpow_add hp, add_neg_cancel, rpow_zero]
  have h1 : E.monoProfit 1 = E.a * E.L := by simp [monoProfit, demand, ψ]
  -- Bernoulli: `p^{1/a} ≥ 1 + (p − 1)/a`, i.e. `p − (1 − a) ≤ a p^{1/a}`
  have hb := one_add_mul_self_le_rpow_one_add hs hρ.le
  rw [show 1 + (p - 1) = p by ring] at hb
  have key : p - E.ψ ≤ E.a * p ^ (1 / E.a) := by
    unfold ψ
    have : E.a * (1 + 1 / E.a * (p - 1)) = E.a + (p - 1) := by field_simp
    nlinarith
  refine ⟨?_, fun hne => ?_, h1⟩
  · rw [h1]; unfold monoProfit demand
    have := mul_le_mul_of_nonneg_right key (mul_pos hpp E.hL).le
    calc (p - E.ψ) * (p ^ (-(1 / E.a)) * E.L) ≤ E.a * p ^ (1 / E.a) * (p ^ (-(1 / E.a)) * E.L) :=
          this
      _ = E.a * E.L := by rw [show E.a * p ^ (1 / E.a) * (p ^ (-(1 / E.a)) * E.L) =
          E.a * (p ^ (1 / E.a) * p ^ (-(1 / E.a))) * E.L by ring, hinv, mul_one]
  · have hb' := one_add_mul_self_lt_rpow_one_add hs (sub_ne_zero.2 hne) hρ
    rw [show 1 + (p - 1) = p by ring] at hb'
    have key' : p - E.ψ < E.a * p ^ (1 / E.a) := by
      unfold ψ
      have : E.a * (1 + 1 / E.a * (p - 1)) = E.a + (p - 1) := by field_simp
      nlinarith
    rw [h1]; unfold monoProfit demand
    have := mul_lt_mul_of_pos_right key' (mul_pos hpp E.hL)
    calc (p - E.ψ) * (p ^ (-(1 / E.a)) * E.L) < E.a * p ^ (1 / E.a) * (p ^ (-(1 / E.a)) * E.L) :=
          this
      _ = E.a * E.L := by rw [show E.a * p ^ (1 / E.a) * (p ^ (-(1 / E.a)) * E.L) =
          E.a * (p ^ (1 / E.a) * p ^ (-(1 / E.a))) * E.L by ring, hinv, mul_one]

/-- At the monopoly price the firm sells `x = L` machines. -/
theorem demand_one : E.demand 1 = E.L := by simp [demand]

/-- The equilibrium interest rate `r = η a L`. -/
def rEq : ℝ := E.η * E.a * E.L

/-- **Free entry into R&D.** With flow profit `π = a L` and interest rate
`r > 0`, a patent is worth `π / r`; free entry (`η · value = 1`) holds iff
`r = η a L`. -/
theorem freeEntry_iff {r : ℝ} (hr : 0 < r) : E.η * (E.monoProfit 1 / r) = 1 ↔ r = E.rEq := by
  rw [(E.monopoly_price one_pos).2.2, rEq, mul_div_assoc', div_eq_one_iff_eq hr.ne']
  constructor <;> intro h <;> linarith

/-- Equilibrium growth factor of consumption (and output) on the balanced
growth path, from the log-utility Euler equation `g = β (1 + r)`. -/
def eulerGrowth : ℝ := E.β * (1 + E.rEq)

/-- **The Euler growth rate comes from household optimization.** A household
with log utility whose wealth `k₀ > 0` earns the gross free-entry return
`1 + r = 1 + η a L` (an AK budget `k_{t+1} = (1 + r) k_t − c_t`) does best with
the plan `AK.cstar`, whose consumption grows at exactly `eulerGrowth`. (Wage
income is left out: this derives the Euler growth rate of a wealth-only
household, not the equilibrium path of output or varieties; the growth claim
is `AK.cstar_succ` at `R = 1 + η a L`.) -/
theorem household_optimal {k₀ : ℝ} (hk : 0 < k₀) :
    (∀ (P : AK.Plan (1 + E.rEq) k₀) {W : ℝ},
      HasSum (fun t => E.β ^ t * log (P.c t)) W →
        W ≤ ∑' t, E.β ^ t * log (AK.cstar E.β (1 + E.rEq) k₀ t)) ∧
    ∀ t, AK.cstar E.β (1 + E.rEq) k₀ (t + 1) = E.eulerGrowth * AK.cstar E.β (1 + E.rEq) k₀ t := by
  have hR : 0 < 1 + E.rEq := by
    have := E.hη; have := E.ha₀; have := E.hL; unfold rEq; positivity
  exact ⟨fun P _ hW => AK.optimal E.hβ₀ E.hβ₁ hR hk P hW, fun t => AK.cstar_succ _ _ _ t⟩

/-! ## The planner -/

/-- Net output per variety when each variety is used at intensity `x`. -/
def netOutput (x : ℝ) : ℝ := E.finalProfit E.ψ x

/-- The planner's machine intensity `x_S = (1 − a)^{−1/a} L`. -/
def xPlan : ℝ := E.demand E.ψ

theorem ψ_pos : 0 < E.ψ := by unfold ψ; linarith [E.ha₁]

/-- `x_S = (1 − a)^{−1/a} L > L`: the monopoly markup leads to too few
machines in equilibrium. -/
theorem xPlan_gt : E.demand 1 < E.xPlan := by
  have ha := E.ha₀
  rw [demand_one, xPlan, demand]
  have : 1 < E.ψ ^ (-(1 / E.a)) := by
    apply one_lt_rpow_of_pos_of_lt_one_of_neg E.ψ_pos
    · unfold ψ; linarith
    · have : 0 < 1 / E.a := by positivity
      linarith
  nlinarith [E.hL]

/-- Net output per variety at the planner's intensity: `a (1 − a)^{−1/a} L`. -/
theorem netOutput_xPlan : E.netOutput E.xPlan = E.a * E.xPlan := by
  have h1a : (1 - E.a) ≠ 0 := by linarith [E.ha₁]
  have hd := E.demand_pos E.ψ_pos
  have hfoc := E.demand_foc E.ψ_pos
  unfold netOutput finalProfit xPlan
  have e : E.demand E.ψ ^ (1 - E.a) = E.demand E.ψ ^ (-E.a) * E.demand E.ψ := by
    rw [← rpow_add_one hd.ne']; ring_nf
  rw [e]
  have : 1 / (1 - E.a) * (E.demand E.ψ ^ (-E.a) * E.demand E.ψ) * E.L ^ E.a =
      1 / (1 - E.a) * (E.demand E.ψ ^ (-E.a) * E.L ^ E.a) * E.demand E.ψ := by ring
  rw [this, hfoc]
  unfold ψ; field_simp; ring

/-- **The planner's static allocation.** `x_S` maximizes net output per
variety. -/
theorem planner_static {x : ℝ} (hx : 0 ≤ x) : E.netOutput x ≤ E.netOutput E.xPlan :=
  (E.demand_optimal E.ψ_pos hx).1

/-- The planner's gross return on R&D: `R_S = 1 + η a (1 − a)^{−1/a} L`. -/
def RPlan : ℝ := 1 + E.η * E.netOutput E.xPlan

theorem RPlan_pos : 0 < E.RPlan := by
  have := E.demand_pos E.ψ_pos
  rw [RPlan, netOutput_xPlan]
  have := E.hη; have := E.ha₀
  unfold xPlan; positivity

/-- A feasible plan for the planner from `N₀` varieties: consumption `C_t > 0`,
machine intensities `x_t ≥ 0`, and the rest of net output spent on R&D:
`N_{t+1} = N_t + η (N_t · netOutput(x_t) − C_t) ≥ 0`. -/
structure PlannerPlan (N₀ : ℝ) where
  C : ℕ → ℝ
  x : ℕ → ℝ
  N : ℕ → ℝ
  N_zero : N 0 = N₀
  law : ∀ t, N (t + 1) = N t + E.η * (N t * E.netOutput (x t) - C t)
  C_pos : ∀ t, 0 < C t
  x_nonneg : ∀ t, 0 ≤ x t
  N_nonneg : ∀ t, 0 ≤ N t

/-- AK capital associated with a planner plan: `k_{t+1} = R_S k_t − C_t`,
`k₀ = N₀/η`. -/
def akCapital {N₀ : ℝ} (P : E.PlannerPlan N₀) : ℕ → ℝ
  | 0 => N₀ / E.η
  | t + 1 => E.RPlan * akCapital P t - P.C t

theorem akCapital_ge {N₀ : ℝ} (P : E.PlannerPlan N₀) (t : ℕ) : P.N t / E.η ≤ E.akCapital P t := by
  have hη := E.hη
  induction t with
  | zero => simp [akCapital, P.N_zero]
  | succ t ih =>
    show P.N (t + 1) / E.η ≤ E.RPlan * E.akCapital P t - P.C t
    rw [P.law t]
    have hx := E.planner_static (P.x_nonneg t)
    have hN := P.N_nonneg t
    have h1 : P.N t * E.netOutput (P.x t) ≤ P.N t * E.netOutput E.xPlan :=
      mul_le_mul_of_nonneg_left hx hN
    have h2 : E.RPlan * (P.N t / E.η) ≤ E.RPlan * E.akCapital P t :=
      mul_le_mul_of_nonneg_left ih E.RPlan_pos.le
    have e : E.RPlan * (P.N t / E.η) = P.N t / E.η + P.N t * E.netOutput E.xPlan := by
      unfold RPlan; field_simp
    have e2 : (P.N t + E.η * (P.N t * E.netOutput (P.x t) - P.C t)) / E.η =
        P.N t / E.η + P.N t * E.netOutput (P.x t) - P.C t := by field_simp; ring
    rw [e2]; linarith

/-- Every planner plan gives an AK plan with return `R_S` and the same
consumption. -/
def toAK {N₀ : ℝ} (P : E.PlannerPlan N₀) : AK.Plan E.RPlan (N₀ / E.η) where
  c := P.C
  k := E.akCapital P
  k_zero := rfl
  law _ := rfl
  c_pos := P.C_pos
  k_nonneg t := le_trans (div_nonneg (P.N_nonneg t) E.hη.le) (E.akCapital_ge P t)

/-- **Optimal growth.** For any feasible planner plan whose lifetime utility
`Σ βᵗ log C_t` converges to `W`, `W` is at most the lifetime utility of the
AK optimum with return `R_S`, which grows at the gross rate `β R_S`. -/
theorem planner_optimal {N₀ : ℝ} (hN : 0 < N₀) (P : E.PlannerPlan N₀) {W : ℝ}
    (hW : HasSum (fun t => E.β ^ t * log (P.C t)) W) :
    W ≤ ∑' t, E.β ^ t * log (AK.cstar E.β E.RPlan (N₀ / E.η) t) :=
  AK.optimal E.hβ₀ E.hβ₁ E.RPlan_pos (div_pos hN E.hη) (E.toAK P) hW

/-- **The optimum is attainable:** using `x_S` every period and consuming
`c*_t`, the variety count is `N_t = η k*_t`, which is a feasible planner plan. -/
def plannerPlan {N₀ : ℝ} (hN : 0 < N₀) : E.PlannerPlan N₀ where
  C := AK.cstar E.β E.RPlan (N₀ / E.η)
  x _ := E.xPlan
  N t := E.η * AK.kstar E.β E.RPlan (N₀ / E.η) t
  N_zero := by have := E.hη; simp [AK.kstar]; field_simp
  law t := by
    have := E.hη
    simp only [AK.cstar, AK.kstar, RPlan, pow_succ]
    ring
  C_pos := (AK.optPlan E.hβ₀ E.hβ₁ E.RPlan_pos (div_pos hN E.hη)).c_pos
  x_nonneg _ := (E.demand_pos E.ψ_pos).le
  N_nonneg t := mul_nonneg E.hη.le ((AK.optPlan E.hβ₀ E.hβ₁ E.RPlan_pos (div_pos hN E.hη)).k_nonneg t)

/-- The planner's optimal consumption grows at gross rate `β R_S`. -/
theorem plannerPlan_growth {N₀ : ℝ} (hN : 0 < N₀) (t : ℕ) :
    (E.plannerPlan hN).C (t + 1) = E.β * E.RPlan * (E.plannerPlan hN).C t :=
  AK.cstar_succ _ _ _ t

/-- With `β R_S ≥ 1` the optimal plan never shrinks the number of varieties:
R&D spending is non-negative. -/
theorem plannerPlan_rd_nonneg {N₀ : ℝ} (hN : 0 < N₀) (h : 1 ≤ E.β * E.RPlan) (t : ℕ) :
    (E.plannerPlan hN).N t ≤ (E.plannerPlan hN).N (t + 1) := by
  show E.η * AK.kstar E.β E.RPlan (N₀ / E.η) t ≤ E.η * AK.kstar E.β E.RPlan (N₀ / E.η) (t + 1)
  rw [AK.kstar_succ]
  have hk : 0 ≤ AK.kstar E.β E.RPlan (N₀ / E.η) t :=
    (AK.optPlan E.hβ₀ E.hβ₁ E.RPlan_pos (div_pos hN E.hη)).k_nonneg t
  have h2 : AK.kstar E.β E.RPlan (N₀ / E.η) t ≤ E.β * E.RPlan * AK.kstar E.β E.RPlan (N₀ / E.η) t :=
    le_mul_of_one_le_left hk h
  exact mul_le_mul_of_nonneg_left h2 E.hη.le

/-! ## Equilibrium versus optimum -/

/-- **The Euler-implied equilibrium growth factor is below the optimum.**
`eulerGrowth = β (1 + η a L)` (the household's Euler equation at the
free-entry rate; a definition) is strictly below the planner's optimal growth
factor `β R_S` (derived in `planner_optimal`): monopoly pricing makes the
private return to R&D fall short of the social return. -/
theorem eulerGrowth_lt_optimal : E.eulerGrowth < E.β * E.RPlan := by
  have h := E.xPlan_gt
  rw [demand_one] at h
  unfold eulerGrowth rEq RPlan
  rw [netOutput_xPlan]
  have := E.hη; have := E.ha₀; have := E.hβ₀
  have h3 : E.η * E.a * E.L < E.η * E.a * E.xPlan := mul_lt_mul_of_pos_left h (by positivity)
  nlinarith [mul_lt_mul_of_pos_left h3 E.hβ₀]

/-- **Scale effect (of the Euler formula).** The Euler-implied growth factor
at the free-entry interest rate, `β (1 + η a L)`, is strictly larger in the
same economy with a larger labour force `L' > L`. This is a property of the
formula, not of a constructed dynamic equilibrium. -/
theorem eulerGrowth_strictMono_L {L' : ℝ} (hL : E.L < L') :
    E.eulerGrowth < ({ E with L := L', hL := E.hL.trans hL } : Economy).eulerGrowth := by
  show E.β * (1 + E.η * E.a * E.L) < E.β * (1 + E.η * E.a * L')
  have := E.hη; have := E.ha₀; have := E.hβ₀
  have : E.η * E.a * E.L < E.η * E.a * L' := mul_lt_mul_of_pos_left hL (by positivity)
  nlinarith

end Economy

end Romer
end Econ

end
