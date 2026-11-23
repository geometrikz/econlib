/-
# Contract design for present-biased consumers (DellaVigna–Malmendier)

Reference. S. DellaVigna and U. Malmendier (2004), "Contract Design and
Self-Control: Theory and Evidence", *QJE* 119(2).

**The model** (investment good, e.g. a gym). A firm with per-visit cost `a`
offers a two-part tariff: a lump-sum fee `L` paid at `t = 0` and a per-use
price `p`. At `t = 1` the consumer draws an attendance cost `c` and attends
iff `βδb − p ≥ c`, where `b` is the benefit at `t = 2`, `δ` the discount
factor and `β` the present-bias parameter. At `t = 0` she believes her
future self uses `β̂ ∈ [β, 1]` (`β̂ = β`: sophisticate, `β̂ = 1`: fully naive).
She accepts the contract iff her *believed* surplus
`−L + E[(δb − p − c) 1{c ≤ β̂δb − p}]` is at least `ū`; the firm sets `L` to
make this bind and earns `L + (p − a) Pr(c ≤ βδb − p)`.

As in DM's closed-form example we take `c ~ U[0, 1]`, so attendance
probabilities are the thresholds themselves. On the region where both
thresholds lie in `[0, 1]`:

* `profit_eq`: profit is the concave quadratic
  `Π(p) = Π(p*) − (p − p*)²/2` with `p* = a − (1 − β)δb` (DM Proposition 1
  specialized to the uniform case), so `p*` is the unique optimal per-use
  price (`isMaxOn_pOpt`, `pOpt_unique`);
* `pOpt_lt_cost`: for `β < 1` the per-use price is **below marginal cost**;
* `overestimate`: naive consumers overestimate attendance by `(β̂ − β)δb`;
* `profit_lt_of_naive`: the firm's optimal profit strictly increases with
  naiveté `β̂`;
* `welfare_lt`: a strictly naive consumer's actual welfare is strictly below
  her reservation utility `ū` (a sophisticate gets exactly `ū`,
  `welfare_soph`).

**Scope (review 2026-11-23).** Optimality of `p*` is proved on `Region`, the
prices for which both attendance thresholds lie in `[0, 1]`, where DM's
first-order condition applies; it is a local (interior) optimum, not a global
one over all `p` (outside `Region` the clamped attendance probabilities make
profit piecewise). DM likewise characterize the interior FOC.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ.ContractDesign

/-- Primitives of the gym-contract problem. -/
structure Gym where
  /-- present bias -/
  β : ℝ
  /-- believed present bias `β̂` -/
  βh : ℝ
  /-- long-run discount factor -/
  δ : ℝ
  /-- future benefit of a visit -/
  b : ℝ
  /-- firm's cost per visit -/
  a : ℝ
  /-- consumer's reservation utility -/
  ū : ℝ

/-- `Pr(c ≤ t)` for `c ~ U[0, 1]`. -/
noncomputable def cdf (t : ℝ) : ℝ := max 0 (min 1 t)

/-- Expected surplus `E[(D − c) 1{c ≤ t}]` for `c ~ U[0, 1]`. -/
noncomputable def surplus (D t : ℝ) : ℝ := ∫ c in (0 : ℝ)..cdf t, (D - c)

theorem cdf_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : cdf t = t := by
  unfold cdf; rw [min_eq_right h1, max_eq_right h0]

theorem surplus_eq {D t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : surplus D t = t * D - t ^ 2 / 2 := by
  unfold surplus
  rw [cdf_of_mem h0 h1, intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  simp

namespace Gym

variable (G : Gym)

/-- Actual attendance threshold `βδb − p`. -/
def thr (p : ℝ) : ℝ := G.β * G.δ * G.b - p

/-- Believed attendance threshold `β̂δb − p`. -/
def thrh (p : ℝ) : ℝ := G.βh * G.δ * G.b - p

/-- The fee that makes the participation constraint bind. -/
noncomputable def fee (p : ℝ) : ℝ := surplus (G.δ * G.b - p) (G.thrh p) - G.ū

/-- Firm profit per consumer. -/
noncomputable def profit (p : ℝ) : ℝ := G.fee p + (p - G.a) * cdf (G.thr p)

/-- The consumer's actual (long-run) welfare under the contract. -/
noncomputable def welfare (p : ℝ) : ℝ := -G.fee p + surplus (G.δ * G.b - p) (G.thr p)

/-- Per-use prices for which both thresholds lie in `[0, 1]` (the uniform
distribution's interior). -/
def Region (p : ℝ) : Prop := 0 ≤ G.thr p ∧ G.thr p ≤ 1 ∧ 0 ≤ G.thrh p ∧ G.thrh p ≤ 1

/-- The optimal per-use price `p* = a − (1 − β)δb`. -/
def pOpt : ℝ := G.a - (1 - G.β) * G.δ * G.b

/-- **Profit is a concave quadratic** peaking at `p*`. -/
theorem profit_eq {p : ℝ} (hp : G.Region p) (hopt : G.Region G.pOpt) :
    G.profit p = G.profit G.pOpt - (p - G.pOpt) ^ 2 / 2 := by
  unfold profit fee
  rw [surplus_eq hp.2.2.1 hp.2.2.2, surplus_eq hopt.2.2.1 hopt.2.2.2, cdf_of_mem hp.1 hp.2.1,
    cdf_of_mem hopt.1 hopt.2.1]
  unfold thr thrh pOpt
  ring

/-- **DM Proposition 1 (uniform case).** `p*` maximizes profit on the
region. -/
theorem isMaxOn_pOpt (hopt : G.Region G.pOpt) : IsMaxOn G.profit {p | G.Region p} G.pOpt :=
  fun p hp => by
    show G.profit p ≤ G.profit G.pOpt
    rw [G.profit_eq hp hopt]
    nlinarith [sq_nonneg (p - G.pOpt)]

/-- `p*` is the unique optimal per-use price. -/
theorem pOpt_unique (hopt : G.Region G.pOpt) {p : ℝ} (hp : G.Region p) (hne : p ≠ G.pOpt) :
    G.profit p < G.profit G.pOpt := by
  rw [G.profit_eq hp hopt]
  have : 0 < (p - G.pOpt) ^ 2 := by positivity [sub_ne_zero.2 hne]
  linarith

/-- **Below-marginal-cost pricing** of an investment good under present
bias. -/
theorem pOpt_lt_cost (hβ : G.β < 1) (hB : 0 < G.δ * G.b) : G.pOpt < G.a := by
  unfold pOpt
  nlinarith

/-- With no present bias the per-use price equals marginal cost. -/
theorem pOpt_eq_cost (hβ : G.β = 1) : G.pOpt = G.a := by
  unfold pOpt; rw [hβ]; ring

/-- **Overestimation of attendance**: believed minus actual attendance is
`(β̂ − β)δb`. -/
theorem overestimate {p : ℝ} (hp : G.Region p) :
    cdf (G.thrh p) - cdf (G.thr p) = (G.βh - G.β) * G.δ * G.b := by
  rw [cdf_of_mem hp.2.2.1 hp.2.2.2, cdf_of_mem hp.1 hp.2.1]
  unfold thr thrh; ring

/-- **Firms profit from naiveté.** Two consumers who differ only in their
beliefs `β̂₁ < β̂₂ ≤ 1`: the firm's optimal profit is strictly higher for the
more naive one (the optimal per-use price is the same). -/
theorem profit_lt_of_naive (G' : Gym) (hβ : G'.β = G.β) (hδ : G'.δ = G.δ) (hb : G'.b = G.b)
    (ha : G'.a = G.a) (hu : G'.ū = G.ū) (hlt : G.βh < G'.βh) (hle : G'.βh ≤ 1)
    (hB : 0 < G.δ * G.b) (hopt : G.Region G.pOpt) (hopt' : G'.Region G'.pOpt) :
    G.profit G.pOpt < G'.profit G'.pOpt := by
  have hp : G'.pOpt = G.pOpt := by unfold pOpt; rw [hβ, hδ, hb, ha]
  unfold profit fee
  rw [surplus_eq hopt.2.2.1 hopt.2.2.2, surplus_eq hopt'.2.2.1 hopt'.2.2.2,
    cdf_of_mem hopt.1 hopt.2.1, cdf_of_mem hopt'.1 hopt'.2.1]
  have h1 := hopt'.2.2.1
  unfold thr thrh at *
  rw [hp, hβ, hδ, hb, ha, hu] at *
  rw [hp] at h1
  -- the believed surplus `t D − t²/2` is increasing in `t` up to `D`
  have hd : 0 < (G'.βh - G.βh) * (G.δ * G.b) := mul_pos (by linarith) hB
  have hle' : G'.βh * (G.δ * G.b) ≤ G.δ * G.b := by nlinarith
  nlinarith

/-- **Naive consumers are hurt.** If `β < β̂ ≤ 1`, actual welfare at any
interior contract with the binding fee is strictly below `ū`. -/
theorem welfare_lt {p : ℝ} (hp : G.Region p) (hβ : G.β < G.βh) (hβh : G.βh ≤ 1)
    (hB : 0 < G.δ * G.b) : G.welfare p < G.ū := by
  unfold welfare fee
  rw [surplus_eq hp.2.2.1 hp.2.2.2, surplus_eq hp.1 hp.2.1]
  have h0 := hp.1
  unfold thr thrh at *
  have hd : 0 < (G.βh - G.β) * (G.δ * G.b) := mul_pos (by linarith) hB
  have hle' : G.βh * (G.δ * G.b) ≤ G.δ * G.b := by nlinarith
  nlinarith

/-- A sophisticate (`β̂ = β`) gets exactly her reservation utility. -/
theorem welfare_soph (h : G.βh = G.β) (p : ℝ) : G.welfare p = G.ū := by
  unfold welfare fee thrh thr; rw [h]; ring

end Gym

end Econ.ContractDesign
