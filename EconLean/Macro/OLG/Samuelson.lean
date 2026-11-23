/-
# Samuelson's pure-exchange overlapping-generations economy

Samuelson (1958); Shell (1971); Ljungqvist–Sargent ch. 9 (§9.2–9.4);
Acemoglu §9.1; Blanchard–Fischer §4.4.

**The economics.** Time is `t = 0, 1, 2, …`. Each period one agent is born
(constant population) and lives two periods, with endowment `ω₁` when young
and `ω₂` when old, and utility `log c₁ + β log c₂`. At `t = 0` there is also an
*initial old* agent who lives only that period. Goods are perishable.

Without money the young can only trade with each other (the old will not be
around to repay), so in any competitive equilibrium net saving is zero and
everyone eats their endowment: **autarky**. The equilibrium gross interest rate
is the autarky rate `R_aut = ω₂ / (β ω₁)`.

When `ω₂ < β ω₁` (the young would like to save, so `R_aut < 1`, below the
economy's growth rate of `1`), autarky is **not Pareto optimal**: each young
generation handing `τ = (β ω₁ − ω₂)/(1 + β)` to the current old makes
*everyone*, including the initial old, strictly better off. The First Welfare
Theorem fails, because there are infinitely many agents and goods (Shell 1971).

**Money** implements this: if the initial old hold `M > 0` units of fiat money
and the price level is constant at `p = M / τ`, the young buy the money with
`τ` goods and sell it when old. This is a stationary monetary equilibrium,
and it Pareto-dominates autarky.

Main results:
* `isCompetitiveEquilibrium_iff`: the nonmonetary competitive equilibria are
  exactly autarky at the interest rate `R_t = ω₂ / (β ω₁)`.
* `firstWelfareTheorem_fails`, `competitiveEquilibrium_dominated`: if
  `ω₂ < β ω₁`, every competitive equilibrium allocation is strictly
  Pareto-dominated by a feasible allocation.
* `isMonetaryEquilibrium_iff`: a stationary monetary equilibrium with
  `M, p > 0` exists iff `ω₂ < β ω₁`, and then `p = M (1 + β)/(β ω₁ − ω₂)`.
* `monetaryEquilibrium_eq_golden_and_dominates`: its allocation strictly
  Pareto-dominates autarky.

Not yet formalized: Pareto *optimality* of the golden-rule/monetary allocation
and of autarky when `ω₂ ≥ β ω₁` (Balasko–Shell); non-stationary monetary
equilibria.

**Deviations from the textbook.** Log utility (Ljungqvist–Sargent's and
Acemoglu's leading example), constant population and stationary endowments.
Only *stationary* monetary equilibria are
covered (the continuum of non-stationary ones with `p_t → ∞`, converging to
autarky, is not). We prove the failure direction only; the converse (autarky is optimal when
`ω₂ ≥ β ω₁`, Balasko–Shell) is not formalized. The nonmonetary equilibrium is
written in its reduced form (the representative young agent's optimal net
saving is zero at the market interest rate), which is how market clearing
among identical young agents reads.
-/
module

public import EconLean.Macro.OLG.LogHousehold

@[expose] public section

noncomputable section

namespace Econ
namespace OLG

/-- A Samuelson exchange economy: endowments when young and old, and the
discount factor. -/
structure Samuelson where
  ω₁ : ℝ
  ω₂ : ℝ
  β : ℝ
  hω₁ : 0 < ω₁
  hω₂ : 0 < ω₂
  hβ : 0 < β

namespace Samuelson

variable (S : Samuelson)

/-- An allocation: `young t` is what generation `t` consumes when young (at
date `t`); `old t` is what the old alive at date `t` consume (generation
`t − 1`; `old 0` is the initial old). -/
structure Allocation where
  young : ℕ → ℝ
  old : ℕ → ℝ

/-- Feasible: consumption is positive and, at every date, the young and old
together consume no more than the endowment `ω₁ + ω₂`. -/
def IsFeasible (x : Allocation) : Prop :=
  ∀ t, 0 < x.young t ∧ 0 < x.old t ∧ x.young t + x.old t ≤ S.ω₁ + S.ω₂

/-- Lifetime utility of generation `t`. -/
def utility (x : Allocation) (t : ℕ) : ℝ := logU S.β (x.young t) (x.old (t + 1))

/-- `x` **Pareto-dominates** `y` (the usual notion): nobody (initial old or
any generation) is worse off, and somebody is strictly better off. -/
def ParetoDominates (x y : Allocation) : Prop :=
  y.old 0 ≤ x.old 0 ∧ (∀ t, S.utility y t ≤ S.utility x t) ∧
    (y.old 0 < x.old 0 ∨ ∃ t, S.utility y t < S.utility x t)

/-- `x` **strictly Pareto-dominates** `y`: the initial old (who care only
about `old 0`) and every generation are strictly better off. This is stronger
than `ParetoDominates` (see `StrictlyDominates.paretoDominates`), so it is the
stronger claim when we exhibit a dominating allocation. -/
def StrictlyDominates (x y : Allocation) : Prop :=
  y.old 0 < x.old 0 ∧ ∀ t, S.utility y t < S.utility x t

theorem StrictlyDominates.paretoDominates {x y : Allocation} (h : S.StrictlyDominates x y) :
    S.ParetoDominates x y :=
  ⟨h.1.le, fun t => (h.2 t).le, Or.inl h.1⟩

/-- Autarky: everyone consumes their endowment. -/
def autarky : Allocation := ⟨fun _ => S.ω₁, fun _ => S.ω₂⟩

theorem autarky_feasible : S.IsFeasible S.autarky :=
  fun _ => ⟨S.hω₁, S.hω₂, le_rfl⟩

/-- A **nonmonetary competitive equilibrium** with autarky consumption: at the
gross interest rate `R_t` on loans between young agents of date `t`, it is
optimal for each young agent to save nothing (so the loan market clears). -/
def IsEquilibrium (R : ℕ → ℝ) : Prop := ∀ t, 0 < R t ∧ IsOptimalSaving S.β S.ω₁ S.ω₂ (R t) 0

/-- The autarky interest rate `R_aut = ω₂ / (β ω₁)`. -/
def autarkyRate : ℝ := S.ω₂ / (S.β * S.ω₁)

/-- **Equilibrium is autarky at the autarky interest rate:** the equilibrium
interest rate path is exactly `R_t = ω₂ / (β ω₁)`. -/
theorem isEquilibrium_iff (R : ℕ → ℝ) : S.IsEquilibrium R ↔ ∀ t, R t = S.autarkyRate := by
  have hb := S.hβ; have h1 := S.hω₁; have h2 := S.hω₂
  have hr : 0 < S.autarkyRate := by unfold autarkyRate; positivity
  constructor
  · intro h t
    obtain ⟨hR, hopt⟩ := h t
    rw [saving_isOptimal_iff S.hβ hR S.hω₁ S.hω₂.le] at hopt
    have hb1 : (1 + S.β) ≠ 0 := by linarith
    field_simp at hopt
    unfold autarkyRate
    rw [eq_div_iff (by positivity)]
    linarith
  · intro h t
    refine ⟨h t ▸ hr, ?_⟩
    rw [saving_isOptimal_iff S.hβ (h t ▸ hr) S.hω₁ S.hω₂.le, h t, autarkyRate]
    field_simp
    ring

/-- A **nonmonetary competitive equilibrium** `(R, x)`: a sequence of gross
interest rates on one-period loans among the young, savings `a t` of
generation `t`, and the allocation `x` they generate, such that
* each young agent's saving `a t` is optimal at `R t` (`IsOptimalSaving`),
* the loan market clears: all young are identical, so lenders and borrowers
  are the same agents and net saving is zero, `a t = 0`,
* consumption follows from the budget constraints: `x.young t = ω₁ − a t`,
  `x.old (t + 1) = ω₂ + R t · a t`, and the initial old eat their endowment,
  `x.old 0 = ω₂` (they have nothing to trade with). -/
def IsCompetitiveEquilibrium (R : ℕ → ℝ) (x : Allocation) : Prop :=
  ∃ a : ℕ → ℝ, (∀ t, 0 < R t ∧ IsOptimalSaving S.β S.ω₁ S.ω₂ (R t) (a t) ∧ a t = 0) ∧
    x.old 0 = S.ω₂ ∧ ∀ t, x.young t = S.ω₁ - a t ∧ x.old (t + 1) = S.ω₂ + R t * a t

/-- **The competitive equilibrium is autarky.** `(R, x)` is a nonmonetary
competitive equilibrium iff `x` is the autarky allocation and every `R t`
equals the autarky rate `ω₂ / (β ω₁)`. -/
theorem isCompetitiveEquilibrium_iff (R : ℕ → ℝ) (x : Allocation) :
    S.IsCompetitiveEquilibrium R x ↔ (∀ t, R t = S.autarkyRate) ∧ x = S.autarky := by
  constructor
  · rintro ⟨a, ha, h0, hx⟩
    have hR : S.IsEquilibrium R := fun t => by
      obtain ⟨h1, h2, h3⟩ := ha t
      exact ⟨h1, h3 ▸ h2⟩
    refine ⟨(S.isEquilibrium_iff R).1 hR, ?_⟩
    obtain ⟨y, o⟩ := x
    simp only at h0 hx
    simp only [autarky, Allocation.mk.injEq]
    refine ⟨funext fun t => ?_, funext fun t => ?_⟩
    · rw [(hx t).1, (ha t).2.2, sub_zero]
    · cases t with
      | zero => exact h0
      | succ t => rw [(hx t).2, (ha t).2.2, mul_zero, add_zero]
  · rintro ⟨hR, rfl⟩
    have hE := (S.isEquilibrium_iff R).2 hR
    exact ⟨fun _ => 0, fun t => ⟨(hE t).1, (hE t).2, rfl⟩, rfl, fun t => by simp [autarky]⟩

/-- The golden-rule (stationary optimal) allocation: each date's endowment
`ω₁ + ω₂` is split `1 : β` between young and old. -/
def golden : Allocation :=
  ⟨fun _ => (S.ω₁ + S.ω₂) / (1 + S.β), fun _ => S.β * (S.ω₁ + S.ω₂) / (1 + S.β)⟩

theorem golden_feasible : S.IsFeasible S.golden := by
  have hb := S.hβ; have h1 := S.hω₁; have h2 := S.hω₂
  intro t
  refine ⟨by simp only [golden]; positivity, by simp only [golden]; positivity, ?_⟩
  simp only [golden]
  rw [← add_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- When the young want to save (`ω₂ < β ω₁`), the golden-rule allocation
strictly Pareto-dominates autarky. -/
theorem golden_dominates_autarky (h : S.ω₂ < S.β * S.ω₁) :
    S.StrictlyDominates S.golden S.autarky := by
  have hb := S.hβ; have h1 := S.hω₁; have h2 := S.hω₂
  have hb1 : 0 < 1 + S.β := by linarith
  refine ⟨?_, fun t => ?_⟩
  · simp only [autarky, golden]
    rw [lt_div_iff₀ hb1]
    nlinarith
  · simp only [utility, autarky, golden]
    have := logU_lt_opt (R := 1) (W := S.ω₁ + S.ω₂) S.hβ one_pos (by linarith) S.hω₁ S.hω₂
      (by simp) (Or.inl (by
        intro e
        rw [eq_div_iff hb1.ne'] at e
        nlinarith))
    rwa [mul_one] at this

/-- **The First Welfare Theorem fails in the OLG economy.** If `ω₂ < β ω₁`
(equivalently `R_aut < 1`), the competitive allocation (autarky) is strictly
Pareto-dominated by a feasible allocation. -/
theorem firstWelfareTheorem_fails (h : S.ω₂ < S.β * S.ω₁) :
    ∃ R x, S.IsCompetitiveEquilibrium R x ∧
      ∃ y, S.IsFeasible y ∧ S.StrictlyDominates y x :=
  ⟨fun _ => S.autarkyRate, S.autarky,
    (S.isCompetitiveEquilibrium_iff _ _).2 ⟨fun _ => rfl, rfl⟩,
    S.golden, S.golden_feasible, S.golden_dominates_autarky h⟩

/-- In fact *every* competitive equilibrium is strictly Pareto-dominated when
`ω₂ < β ω₁`. -/
theorem competitiveEquilibrium_dominated (h : S.ω₂ < S.β * S.ω₁) {R : ℕ → ℝ} {x : Allocation}
    (hx : S.IsCompetitiveEquilibrium R x) :
    ∃ y, S.IsFeasible y ∧ S.StrictlyDominates y x := by
  obtain ⟨-, rfl⟩ := (S.isCompetitiveEquilibrium_iff R x).1 hx
  exact ⟨S.golden, S.golden_feasible, S.golden_dominates_autarky h⟩

theorem autarkyRate_lt_one_iff : S.autarkyRate < 1 ↔ S.ω₂ < S.β * S.ω₁ := by
  have := mul_pos S.hβ S.hω₁
  rw [autarkyRate, div_lt_one this]

/-! ## Fiat money -/

/-- A **stationary monetary equilibrium** with money stock `M` and constant
price level `p`: both positive, and buying the real balances `M / p` (which
return `p_t / p_{t+1} = 1` in goods) is the young's optimal saving. -/
def IsMonetaryEquilibrium (M p : ℝ) : Prop :=
  0 < M ∧ 0 < p ∧ IsOptimalSaving S.β S.ω₁ S.ω₂ 1 (M / p)

/-- The allocation in a monetary equilibrium: the young give up `M / p` goods
for money; the old (including the initial old, who start with `M`) spend it. -/
def monetaryAllocation (M p : ℝ) : Allocation :=
  ⟨fun _ => S.ω₁ - M / p, fun _ => S.ω₂ + M / p⟩

/-- **Existence and uniqueness of the stationary monetary equilibrium.** For
`M > 0`, a constant price level `p` is a monetary equilibrium iff
`ω₂ < β ω₁` and `p = M (1 + β)/(β ω₁ − ω₂)`. So money has value exactly when
autarky is inefficient. -/
theorem isMonetaryEquilibrium_iff {M p : ℝ} (hM : 0 < M) :
    S.IsMonetaryEquilibrium M p ↔
      S.ω₂ < S.β * S.ω₁ ∧ p = M * (1 + S.β) / (S.β * S.ω₁ - S.ω₂) := by
  have hb := S.hβ
  have hb1 : 0 < 1 + S.β := by linarith
  unfold IsMonetaryEquilibrium
  rw [saving_isOptimal_iff S.hβ one_pos S.hω₁ S.hω₂.le, div_one]
  constructor
  · rintro ⟨-, hp, e⟩
    have hpos : 0 < S.β * S.ω₁ - S.ω₂ := by
      have : 0 < M / p := div_pos hM hp
      rw [e] at this
      exact (div_pos_iff_of_pos_right hb1).1 this
    refine ⟨by linarith, ?_⟩
    rw [div_eq_div_iff hp.ne' hb1.ne'] at e
    rw [eq_div_iff hpos.ne']
    linarith
  · rintro ⟨h, rfl⟩
    have hpos : 0 < S.β * S.ω₁ - S.ω₂ := by linarith
    refine ⟨hM, by positivity, ?_⟩
    field_simp

/-- **Money is a Pareto improvement.** In the stationary monetary
equilibrium the allocation is the golden rule, which strictly Pareto-dominates
autarky. -/
theorem monetaryEquilibrium_eq_golden_and_dominates {M p : ℝ} (hM : 0 < M)
    (h : S.IsMonetaryEquilibrium M p) :
    S.monetaryAllocation M p = S.golden ∧ S.IsFeasible (S.monetaryAllocation M p) ∧
      S.StrictlyDominates (S.monetaryAllocation M p) S.autarky := by
  obtain ⟨hlt, -⟩ := (S.isMonetaryEquilibrium_iff hM).1 h
  have e := ((saving_isOptimal_iff S.hβ one_pos S.hω₁ S.hω₂.le).1 h.2.2)
  have hb := S.hβ
  have hb1 : 0 < 1 + S.β := by linarith
  have heq : S.monetaryAllocation M p = S.golden := by
    simp only [monetaryAllocation, golden, e, Allocation.mk.injEq]
    constructor <;> funext _ <;> field_simp <;> ring
  rw [heq]
  exact ⟨rfl, S.golden_feasible, S.golden_dominates_autarky hlt⟩

/-- **Non-vacuity.** With `ω₁ = 1`, `ω₂ = 1/10`, `β = 1/2` the young want to
save, a monetary equilibrium exists (`M = 1`, `p = 15/4`), and it
Pareto-dominates autarky. -/
example : (⟨1, 1 / 10, 1 / 2, by norm_num, by norm_num, by norm_num⟩ : Samuelson).IsMonetaryEquilibrium
    1 (15 / 4) := by
  rw [isMonetaryEquilibrium_iff _ one_pos]
  norm_num

end Samuelson

end OLG
end Econ

end
