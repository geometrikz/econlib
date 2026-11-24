/-
# Relational contracts: stationary contracts are optimal (Levin 2003, observable effort)

Levin (2003), "Relational incentive contracts", AER 93(3); MacLeod and Malcomson (1989).
A principal and an agent meet in periods `t = 0, 1, …` with common discount factor `δ ∈ (0,1)`.
Each period the principal pays a court-enforceable wage `w t`, the agent chooses an effort
`e t ∈ E` at cost `c (e t) ≥ 0` producing value `y (e t)`, effort is
observed by both, and then a discretionary bonus `b t` (of either sign) is paid. Any deviation
ends the relationship (outside options normalized to `0`); some effort costs nothing. Only the
optimality theorem needs finitely many efforts.

A relational contract records the effort, wage and bonus paths together with the
continuation values `U t` (agent) and `P t` (principal), which satisfy the Bellman recursions
and are bounded (so they are the discounted sums). It is **self-enforcing** when both parties
participate in every period, the agent prefers the prescribed effort to any deviation
(after which there is no bonus and no future), and each party prefers paying the bonus to
walking away.

* `stationary_selfEnforcing`: if `(1 − δ) c e ≤ δ s e` (with surplus `s = y − c`), the stationary
  contract with effort `e` is self-enforcing for every split of the surplus.
* `selfEnforcing_dynamic`: in every self-enforcing contract, `c (e t) ≤ δ S (t+1)`, where
  `S = U + P` is joint continuation surplus: only the total matters.
* `levin_stationary_optimal`: **stationary contracts are optimal** — the joint surplus of any
  self-enforcing contract at any date is at most `s* / (1 − δ)`, where `s*` is the best
  stationary surplus, and a stationary self-enforcing contract attains it.
* `constant_effort_iff`: a constant effort path is sustainable iff `(1 − δ) c e ≤ δ s e`.

This is the observable-effort benchmark of Levin (2003) (the MacLeod–Malcomson setting), not
his main model. Not formalized: Levin's general stationarity theorem under imperfect public
monitoring, hidden effort with noisy output and the optimality of one-step (bang-bang)
bonuses, adverse selection, and subjective performance measures. Informal remark (not proved
here): randomized contracts and public randomization cannot improve on `s*` in this setting,
since any realized effort must satisfy `c e ≤ δ S'`.
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace Econ

open Set Filter Topology

/-- A relational contract: effort, wage and bonus paths with continuation values. -/
structure RelContract (E : Type*) where
  /-- effort in period `t` -/
  e : ℕ → E
  /-- contractible wage in period `t` -/
  w : ℕ → ℝ
  /-- discretionary bonus in period `t` (negative: paid by the agent) -/
  b : ℕ → ℝ
  /-- agent's continuation value at the start of period `t` -/
  U : ℕ → ℝ
  /-- principal's continuation value at the start of period `t` -/
  P : ℕ → ℝ

variable {E : Type*}

/-- **Self-enforcing relational contract** (perfect monitoring): Bellman recursions with bounded
values, participation, the agent's effort constraint against every deviation `e'`, and the
two bonus-payment constraints. Boundedness loses no generality (with finitely many efforts
the true discounted sums are bounded) and rules out spurious solutions of the recursions that
are not discounted sums. -/
structure IsSelfEnforcing (y c : E → ℝ) (δ : ℝ) (K : RelContract E) : Prop where
  recU : ∀ t, K.U t = K.w t + K.b t - c (K.e t) + δ * K.U (t + 1)
  recP : ∀ t, K.P t = y (K.e t) - K.w t - K.b t + δ * K.P (t + 1)
  bdd : ∃ B, ∀ t, |K.U t| ≤ B ∧ |K.P t| ≤ B
  irU : ∀ t, 0 ≤ K.U t
  irP : ∀ t, 0 ≤ K.P t
  effort : ∀ t e', -c e' ≤ K.b t - c (K.e t) + δ * K.U (t + 1)
  payP : ∀ t, K.b t ≤ δ * K.P (t + 1)
  payU : ∀ t, -K.b t ≤ δ * K.U (t + 1)

/-- The stationary contract with effort `e` giving the agent `u` and the principal `π` per
period (the bonus is `δ` times the principal's continuation value). These are the parties'
per-period payoffs when `u + π = y e − c e`, as in `stationary_selfEnforcing`. -/
noncomputable def stationaryRel (c : E → ℝ) (δ : ℝ) (e : E) (u π : ℝ) : RelContract E where
  e _ := e
  w _ := u + c e - δ * (π / (1 - δ))
  b _ := δ * (π / (1 - δ))
  U _ := u / (1 - δ)
  P _ := π / (1 - δ)

/-- **Stationary contracts**: if `(1 − δ) c e ≤ δ (y e − c e)`, every split `u + π = y e − c e`
with `u, π ≥ 0` is supported by a stationary self-enforcing contract. -/
theorem stationary_selfEnforcing {y c : E → ℝ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc : ∀ e, 0 ≤ c e) {e : E} (hfeas : (1 - δ) * c e ≤ δ * (y e - c e)) {u π : ℝ}
    (hu : 0 ≤ u) (hπ : 0 ≤ π) (hsum : u + π = y e - c e) :
    IsSelfEnforcing y c δ (stationaryRel c δ e u π) := by
  have h1 : 0 < 1 - δ := by linarith
  have hU : u / (1 - δ) = u + δ * (u / (1 - δ)) := by field_simp; ring
  have hP : π / (1 - δ) = π + δ * (π / (1 - δ)) := by field_simp; ring
  have hUn : 0 ≤ u / (1 - δ) := div_nonneg hu h1.le
  have hPn : 0 ≤ π / (1 - δ) := div_nonneg hπ h1.le
  -- `c e ≤ δ (u + π)/(1 − δ)`
  have hk : c e ≤ δ * (u / (1 - δ)) + δ * (π / (1 - δ)) := by
    rw [← mul_add, ← add_div, hsum, mul_div_assoc', le_div_iff₀ h1]; linarith
  refine ⟨fun _ => ?_, fun _ => ?_, ⟨|u / (1 - δ)| + |π / (1 - δ)|, fun _ => ?_⟩,
    fun _ => hUn, fun _ => hPn, fun _ e' => ?_, fun _ => le_rfl, fun _ => ?_⟩
  · simp only [stationaryRel]; linarith
  · simp only [stationaryRel]; linarith
  · simp only [stationaryRel]
    exact ⟨by linarith [abs_nonneg (π / (1 - δ))], by linarith [abs_nonneg (u / (1 - δ))]⟩
  · simp only [stationaryRel]; linarith [hc e']
  · simp only [stationaryRel]; nlinarith

/-- If `x t ≤ δ x (t+1)` with `0 ≤ δ < 1` and `x` bounded above, then `x ≤ 0`. -/
lemma nonpos_of_le_mul_succ {x : ℕ → ℝ} {δ B : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hB : ∀ t, x t ≤ B) (hx : ∀ t, x t ≤ δ * x (t + 1)) (t : ℕ) : x t ≤ 0 := by
  have hB0 : ∀ t, x t ≤ max B 0 := fun t => (hB t).trans (le_max_left _ _)
  have key : ∀ n t, x t ≤ δ ^ n * max B 0 := by
    intro n
    induction n with
    | zero => intro t; simpa using hB0 t
    | succ n ih =>
      intro t
      calc x t ≤ δ * x (t + 1) := hx t
        _ ≤ δ * (δ ^ n * max B 0) := mul_le_mul_of_nonneg_left (ih _) hδ0
        _ = δ ^ (n + 1) * max B 0 := by ring
  have hlim : Tendsto (fun n => δ ^ n * max B 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const (max B 0)
  exact ge_of_tendsto' hlim (fun n => key n t)

variable {y c : E → ℝ} {δ : ℝ} {K : RelContract E}

/-- Joint surplus satisfies `S t = s (e t) + δ S (t+1)`. -/
lemma IsSelfEnforcing.joint (hK : IsSelfEnforcing y c δ K) (t : ℕ) :
    K.U t + K.P t = (y (K.e t) - c (K.e t)) + δ * (K.U (t + 1) + K.P (t + 1)) := by
  rw [hK.recU t, hK.recP t]; ring

/-- **Only joint surplus matters**: in a self-enforcing contract the cost of effort is covered
by discounted joint continuation surplus, provided some effort is costless. -/
theorem selfEnforcing_dynamic (hK : IsSelfEnforcing y c δ K) (hc0 : ∃ e₀, c e₀ = 0) (t : ℕ) :
    c (K.e t) ≤ δ * (K.U (t + 1) + K.P (t + 1)) := by
  obtain ⟨e₀, he₀⟩ := hc0
  have h1 := hK.effort t e₀
  have h2 := hK.payP t
  rw [he₀] at h1
  linarith

/-- If per-period surplus never exceeds `a`, then `(1 − δ) S t ≤ a` at every date. -/
lemma IsSelfEnforcing.joint_le (hK : IsSelfEnforcing y c δ K) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {a : ℝ} (ha : ∀ t, y (K.e t) - c (K.e t) ≤ a) (t : ℕ) :
    (1 - δ) * (K.U t + K.P t) ≤ a := by
  have h1 : 0 < 1 - δ := by linarith
  obtain ⟨B, hB⟩ := hK.bdd
  have := nonpos_of_le_mul_succ (x := fun t => K.U t + K.P t - a / (1 - δ)) hδ0 hδ1
    (B := 2 * B - a / (1 - δ))
    (fun t => by
      have := hB t
      linarith [le_abs_self (K.U t), le_abs_self (K.P t)])
    (fun t => by
      rw [hK.joint t]
      have : a / (1 - δ) = a + δ * (a / (1 - δ)) := by field_simp; ring
      nlinarith [ha t]) t
  have h2 : K.U t + K.P t ≤ a / (1 - δ) := by linarith
  rw [le_div_iff₀ h1] at h2
  linarith

variable [Fintype E]

/-- The efforts sustainable by a stationary contract. -/
noncomputable def stationaryFeasible (y c : E → ℝ) (δ : ℝ) : Finset E :=
  Finset.univ.filter fun e => (1 - δ) * c e ≤ δ * (y e - c e)

/-- **Stationary contracts are optimal** (Levin 2003, perfect monitoring): if a self-enforcing
contract exists, some effort `e*` is stationary-feasible, the stationary contract with effort
`e*` (giving all surplus to the agent; any other split follows from
`stationary_selfEnforcing`) is self-enforcing, and no self-enforcing contract does better than
`s* = y e* − c e*` per period at any date. -/
theorem levin_stationary_optimal (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : ∀ e, 0 ≤ c e)
    (hc0 : ∃ e₀, c e₀ = 0) (hK : IsSelfEnforcing y c δ K) :
    ∃ e' ∈ stationaryFeasible y c δ,
      (∀ e ∈ stationaryFeasible y c δ, y e - c e ≤ y e' - c e') ∧
      IsSelfEnforcing y c δ (stationaryRel c δ e' (y e' - c e') 0) ∧
      ∀ (K' : RelContract E), IsSelfEnforcing y c δ K' →
        ∀ t, (1 - δ) * (K'.U t + K'.P t) ≤ y e' - c e' := by
  have h1 : 0 < 1 - δ := by linarith
  -- a general bound: any self-enforcing contract is dominated by some feasible stationary effort
  have dom : ∀ (K' : RelContract E), IsSelfEnforcing y c δ K' →
      ∃ e'' ∈ stationaryFeasible y c δ, ∀ t, (1 - δ) * (K'.U t + K'.P t) ≤ y e'' - c e'' := by
    intro K' hK'
    obtain ⟨B, hB⟩ := hK'.bdd
    set S : ℕ → ℝ := fun t => K'.U t + K'.P t
    have hSb : BddAbove (range S) := ⟨2 * B, by
      rintro _ ⟨t, rfl⟩; have := hB t; simp only [S]
      linarith [le_abs_self (K'.U t), le_abs_self (K'.P t)]⟩
    obtain ⟨M, hMdef⟩ : ∃ M, M = sSup (range S) := ⟨_, rfl⟩
    have hSM : ∀ t, S t ≤ M := fun t => hMdef ▸ le_csSup hSb ⟨t, rfl⟩
    -- every effort used costs at most `δ M`
    set F := Finset.univ.filter fun e => c e ≤ δ * M
    have hF : ∀ t, K'.e t ∈ F := fun t => by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      exact (selfEnforcing_dynamic hK' hc0 t).trans
        (mul_le_mul_of_nonneg_left (hSM (t + 1)) hδ0.le)
    have hFne : F.Nonempty := ⟨_, hF 0⟩
    obtain ⟨e'', he''F, hmax⟩ := F.exists_max_image (fun e => y e - c e) hFne
    have hle : ∀ t, (1 - δ) * S t ≤ y e'' - c e'' :=
      hK'.joint_le hδ0.le hδ1 (fun t => hmax _ (hF t))
    -- hence `M ≤ s(e'')/(1 − δ)`, so `e''` is stationary-feasible
    have hM : (1 - δ) * M ≤ y e'' - c e'' := by
      have : M ≤ (y e'' - c e'') / (1 - δ) := hMdef ▸ csSup_le ⟨S 0, ⟨0, rfl⟩⟩
        (by rintro _ ⟨t, rfl⟩; rw [le_div_iff₀ h1]; linarith [hle t])
      rw [le_div_iff₀ h1] at this; linarith
    refine ⟨e'', ?_, hle⟩
    have he''c : c e'' ≤ δ * M := (Finset.mem_filter.1 he''F).2
    rw [stationaryFeasible, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by nlinarith⟩
  obtain ⟨e₁, he₁, -⟩ := dom K hK
  obtain ⟨e', he', hmax⟩ := (stationaryFeasible y c δ).exists_max_image
    (fun e => y e - c e) ⟨e₁, he₁⟩
  have hfe : (1 - δ) * c e' ≤ δ * (y e' - c e') := by
    simpa [stationaryFeasible] using he'
  have hs : 0 ≤ y e' - c e' := by
    have := hc e'; nlinarith
  refine ⟨e', he', hmax, stationary_selfEnforcing hδ0 hδ1 hc hfe hs le_rfl (by ring), ?_⟩
  intro K' hK' t
  obtain ⟨e'', he'', hle⟩ := dom K' hK'
  exact (hle t).trans (hmax e'' he'')

omit [Fintype E] in
/-- **Constant effort**: an effort `e` can be played in every period of a self-enforcing
contract iff `(1 − δ) c e ≤ δ (y e − c e)`. -/
theorem constant_effort_iff (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : ∀ e, 0 ≤ c e)
    (hc0 : ∃ e₀, c e₀ = 0) (e : E) :
    (∃ K : RelContract E, IsSelfEnforcing y c δ K ∧ ∀ t, K.e t = e) ↔
      (1 - δ) * c e ≤ δ * (y e - c e) := by
  constructor
  · rintro ⟨K, hK, he⟩
    have hle := hK.joint_le hδ0.le hδ1 (a := y e - c e) (fun t => by rw [he t]) 1
    have hd := selfEnforcing_dynamic hK hc0 0
    rw [he 0] at hd
    have h1 : 0 < 1 - δ := by linarith
    nlinarith
  · intro hfe
    have hs : 0 ≤ y e - c e := by have := hc e; nlinarith
    exact ⟨_, stationary_selfEnforcing hδ0 hδ1 hc hfe hs le_rfl (by ring), fun _ => rfl⟩

/-! ### Witness: patience sustains high effort, impatience does not -/

/-- Value of output in the witness: high effort (`true`) produces `3`. -/
noncomputable def witnessY : Bool → ℝ := fun e => if e then 3 else 0
/-- Cost of effort in the witness: high effort costs `1`. -/
noncomputable def witnessC : Bool → ℝ := fun e => if e then 1 else 0

example : ∃ K : RelContract Bool, IsSelfEnforcing witnessY witnessC (1 / 2) K ∧
    ∀ t, K.e t = true :=
  (constant_effort_iff (by norm_num) (by norm_num)
    (fun e => by cases e <;> norm_num [witnessC]) ⟨false, rfl⟩ true).2
    (by norm_num [witnessY, witnessC])

example : ¬ ∃ K : RelContract Bool, IsSelfEnforcing witnessY witnessC (1 / 10) K ∧
    ∀ t, K.e t = true := by
  rw [constant_effort_iff (by norm_num) (by norm_num)
    (fun e => by cases e <;> norm_num [witnessC]) ⟨false, rfl⟩ true]
  norm_num [witnessY, witnessC]

/-- In the witness with `δ = 1/2`, no self-enforcing contract yields more than `2` per period
(the surplus of high effort), and this is attained by a stationary contract. -/
example : (∀ K : RelContract Bool, IsSelfEnforcing witnessY witnessC (1 / 2) K →
      ∀ t, (1 - 1 / 2) * (K.U t + K.P t) ≤ 2) ∧
    IsSelfEnforcing witnessY witnessC (1 / 2) (stationaryRel witnessC (1 / 2) true 2 0) := by
  have hc : ∀ e, 0 ≤ witnessC e := fun e => by cases e <;> norm_num [witnessC]
  refine ⟨fun K hK t => ?_, stationary_selfEnforcing (by norm_num) (by norm_num) hc
    (by norm_num [witnessY, witnessC]) (by norm_num) le_rfl (by norm_num [witnessY, witnessC])⟩
  obtain ⟨e', -, -, -, hb⟩ :=
    levin_stationary_optimal (by norm_num) (by norm_num) hc ⟨false, rfl⟩ hK
  refine (hb K hK t).trans ?_
  cases e' <;> norm_num [witnessY, witnessC]

/-- In the witness with `δ = 1/2`, the optimal stationary effort is high effort. -/
example : ∀ K : RelContract Bool, IsSelfEnforcing witnessY witnessC (1 / 2) K →
    ∃ e' ∈ stationaryFeasible witnessY witnessC (1 / 2),
      (∀ e ∈ stationaryFeasible witnessY witnessC (1 / 2),
        witnessY e - witnessC e ≤ witnessY e' - witnessC e') ∧ e' = true := by
  intro K hK
  have hc : ∀ e, 0 ≤ witnessC e := fun e => by cases e <;> norm_num [witnessC]
  obtain ⟨e', he', hmax, -⟩ :=
    levin_stationary_optimal (by norm_num) (by norm_num) hc ⟨false, rfl⟩ hK
  refine ⟨e', he', hmax, ?_⟩
  have ht : true ∈ stationaryFeasible witnessY witnessC (1 / 2) := by
    rw [stationaryFeasible, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by norm_num [witnessY, witnessC]⟩
  have := hmax true ht
  cases e'
  · norm_num [witnessY, witnessC] at this
  · rfl

end Econ
