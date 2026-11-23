/-
# The Diamond overlapping-generations model

Diamond (1965); Acemoglu §9.2–9.3 (the canonical model: log utility,
Cobb–Douglas technology); Romer ch. 2 (Part B); Blanchard–Fischer ch. 3.

**The economics.** Each period a generation of `L_t` young agents is born,
with `L_{t+1} = (1 + n) L_t`. Agents live two periods with utility
`log c₁ + β log c₂`. When young they supply one unit of labour, earn the wage
`w_t`, consume and save; when old they consume their savings plus interest.
Firms produce `y = k^α` per young worker (Cobb–Douglas, `0 < α < 1`) and
capital fully depreciates after one period, so with competitive factor
markets

    w(k) = (1 − α) k^α,      R(k) = α k^{α − 1}  (gross return = f'(k)).

Capital next period is what the young save: `(1 + n) k_{t+1} = a_t`. With log
utility the young save the fraction `β/(1+β)` of their wage, whatever the
interest rate, so the equilibrium law of motion is

    k_{t+1} = A k_t^α,   A = β (1 − α) / ((1 + β)(1 + n)).

Main results:
* `Diamond.isEquilibrium_iff`: a capital path is a competitive equilibrium
  (each young agent saves optimally, markets clear) iff it follows
  `k_{t+1} = A k_t^α`.
* `Diamond.existsUnique_equilibrium`: from any `k₀ > 0` there is exactly one
  equilibrium path.
* `Diamond.tendsto_equilibrium`: every equilibrium path converges to
  `k* = A^{1/(1−α)}` (Acemoglu Prop. 9.3).
* `Diamond.rate_steadyState`: the steady-state gross interest rate is
  `R* = α / A = α (1 + β)(1 + n) / (β (1 − α))`.
* `Diamond.no_dominating_path`, `dynamicallyInefficient_iff_exists_improvement`:
  conversely, if `R* ≥ 1 + n` no feasible path improves on the steady state,
  so `R* < 1 + n` exactly characterizes inefficiency.
* **Dynamic inefficiency** (Acemoglu Prop. 9.4):
  `Diamond.dynamicallyInefficient_iff`: `R* < 1 + n` (the interest rate is
  below the growth rate, "r < g") iff `α (1 + β) < β (1 − α)` iff `k*` exceeds
  the golden-rule capital stock; and `Diamond.exists_dominating_path`: in that
  case a feasible path gives strictly more aggregate consumption in *every*
  period than the competitive steady state.

**Deviations from the textbook.** This is Acemoglu's canonical special case
(log utility, Cobb–Douglas, full depreciation), not his general model with
arbitrary utility and technology, where equilibria can be multiple or fail to
exist. "More consumption in every period" is stated for aggregate consumption
per young worker, as in Acemoglu's proof; turning it into a Pareto improvement
for every generation additionally requires a transfer scheme (see
`Samuelson.lean` for that argument in the exchange model).
-/
module

public import EconLean.Macro.Growth.GoldenRule
public import EconLean.Macro.OLG.LogHousehold

@[expose] public section

noncomputable section

namespace Econ
namespace OLG

open Set Filter Topology Econ.Solow

/-- Parameters of the canonical Diamond model. -/
structure Diamond where
  /-- Capital share in the Cobb–Douglas technology. -/
  α : ℝ
  /-- Discount factor. -/
  β : ℝ
  /-- Population growth rate. -/
  n : ℝ
  hα₀ : 0 < α
  hα₁ : α < 1
  hβ : 0 < β
  hn : -1 < n

namespace Diamond

variable (D : Diamond)

/-- The competitive wage `w(k) = (1 − α) k^α` (marginal product of labour). -/
def wage (k : ℝ) : ℝ := (1 - D.α) * k ^ D.α

/-- The competitive gross return on capital `R(k) = α k^{α − 1}` (marginal
product of capital; capital fully depreciates). -/
def rate (k : ℝ) : ℝ := D.α * k ^ (D.α - 1)

/-- The coefficient `A = β (1 − α) / ((1 + β)(1 + n))` of the law of motion. -/
def coef : ℝ := D.β * (1 - D.α) / ((1 + D.β) * (1 + D.n))

/-- The equilibrium law of motion `k_{t+1} = A k_t^α`. -/
def next (k : ℝ) : ℝ := D.coef * k ^ D.α

theorem coef_pos : 0 < D.coef := by
  have := D.hα₁; have := D.hβ; have : 0 < 1 + D.n := by linarith [D.hn]
  unfold coef
  apply div_pos (mul_pos D.hβ (by linarith)) (by positivity)

/-- A capital path `k` (per young worker) is a **competitive equilibrium** if
capital stays positive and in every period the young, earning `w(k_t)` and
facing next period's return `R(k_{t+1})`, find it optimal to save exactly
`(1 + n) k_{t+1}` (capital-market clearing: next period's capital is this
period's saving). -/
def IsEquilibrium (k : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ IsOptimalSaving D.β (D.wage (k t)) 0 (D.rate (k (t + 1))) ((1 + D.n) * k (t + 1))

theorem wage_pos {k : ℝ} (hk : 0 < k) : 0 < D.wage k :=
  mul_pos (by linarith [D.hα₁]) (Real.rpow_pos_of_pos hk _)

theorem rate_pos {k : ℝ} (hk : 0 < k) : 0 < D.rate k :=
  mul_pos D.hα₀ (Real.rpow_pos_of_pos hk _)

theorem next_pos {k : ℝ} (hk : 0 < k) : 0 < D.next k :=
  mul_pos D.coef_pos (Real.rpow_pos_of_pos hk _)

/-- **Equilibrium ⟺ law of motion.** Given `k₀ > 0`, a path is an equilibrium
iff `k_{t+1} = A k_t^α` for all `t`. With log utility saving does not depend on
the interest rate, which is why the equilibrium is pinned down period by
period. -/
theorem isEquilibrium_iff (k : ℕ → ℝ) (hk0 : 0 < k 0) :
    D.IsEquilibrium k ↔ ∀ t, k (t + 1) = D.next (k t) := by
  have h1n : 0 < 1 + D.n := by linarith [D.hn]
  have hb : 0 < 1 + D.β := by linarith [D.hβ]
  -- the optimal-saving condition, at positive capital, is the law of motion
  have step : ∀ t, 0 < k t → 0 < k (t + 1) →
      (IsOptimalSaving D.β (D.wage (k t)) 0 (D.rate (k (t + 1))) ((1 + D.n) * k (t + 1)) ↔
        k (t + 1) = D.next (k t)) := by
    intro t ht ht1
    rw [saving_isOptimal_iff D.hβ (D.rate_pos ht1) (D.wage_pos ht) le_rfl]
    simp only [zero_div, sub_zero, next, coef, wage]
    constructor
    · intro h
      field_simp at h ⊢
      linarith
    · intro h
      rw [h]
      field_simp
  constructor
  · intro h t
    exact (step t (h t).1 (h (t + 1)).1).1 (h t).2
  · intro h
    have hpos : ∀ t, 0 < k t := by
      intro t
      induction t with
      | zero => exact hk0
      | succ t ih => rw [h t]; exact D.next_pos ih
    exact fun t => ⟨hpos t, (step t (hpos t) (hpos (t + 1))).2 (h t)⟩

/-- The Diamond economy as a basic Solow economy: saving rate
`s = β (1 − α)/(1 + β)` (the young save `β/(1+β)` of the wage, which is the
share `1 − α` of output), full depreciation `δ = 1`, `f k = k^α`. -/
def toSolow : Economy where
  f := fun k => k ^ D.α
  s := D.β * (1 - D.α) / (1 + D.β)
  δ := 1
  n := D.n
  hf := cobbDouglas_neoclassical D.hα₀ D.hα₁
  hs_pos := div_pos (mul_pos D.hβ (by linarith [D.hα₁])) (by linarith [D.hβ])
  hs_le_one := by
    rw [div_le_one (by linarith [D.hβ])]
    nlinarith [D.hα₀, D.hβ]
  hδ_nonneg := zero_le_one
  hδ_le_one := le_rfl
  hn := D.hn
  hnδ := by linarith [D.hn]

theorem toSolow_next (k : ℝ) : D.toSolow.next k = D.next k := by
  have h1n : 0 < 1 + D.n := by linarith [D.hn]
  have hb : 0 < 1 + D.β := by linarith [D.hβ]
  simp only [Economy.next, toSolow, next, coef]
  field_simp
  ring

/-- **Existence and uniqueness of equilibrium:** from any `k₀ > 0` there is
exactly one equilibrium path. -/
theorem existsUnique_equilibrium {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∃! k : ℕ → ℝ, k 0 = k₀ ∧ D.IsEquilibrium k := by
  refine ⟨fun t => D.next^[t] k₀, ⟨rfl, ?_⟩, ?_⟩
  · rw [D.isEquilibrium_iff _ hk₀]
    intro t
    exact Function.iterate_succ_apply' _ _ _
  · rintro k ⟨h0, hk⟩
    rw [D.isEquilibrium_iff _ (h0 ▸ hk₀)] at hk
    funext t
    induction t with
    | zero => exact h0
    | succ t ih => rw [hk t, ih, Function.iterate_succ_apply']

/-- The steady state `k* = A^{1/(1−α)}`. -/
def kstar : ℝ := D.coef ^ (1 / (1 - D.α))

theorem kstar_pos : 0 < D.kstar := Real.rpow_pos_of_pos D.coef_pos _

theorem isSteadyState_kstar : D.toSolow.IsSteadyState D.kstar := by
  have h := cobbDouglas_steadyState D.toSolow D.hα₁ rfl
  have h1n : 0 < 1 + D.n := by linarith [D.hn]
  have hb : 0 < 1 + D.β := by linarith [D.hβ]
  have e : D.toSolow.s / (D.toSolow.n + D.toSolow.δ) = D.coef := by
    simp only [toSolow, coef]
    have : D.n + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e] at h
  exact h

/-- `k*` is a fixed point of the equilibrium law of motion. -/
theorem next_kstar : D.next D.kstar = D.kstar := by
  rw [← D.toSolow_next]; exact D.isSteadyState_kstar.2

/-- **Global stability (Acemoglu Prop. 9.3):** every equilibrium path from
`k₀ > 0` converges to `k*`. -/
theorem tendsto_equilibrium {k : ℕ → ℝ} (hk0 : 0 < k 0) (hk : D.IsEquilibrium k) :
    Tendsto k atTop (𝓝 D.kstar) := by
  rw [D.isEquilibrium_iff _ hk0] at hk
  have hpath : ∀ t, k t = D.toSolow.path (k 0) t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hk t, Economy.path_succ, ih, D.toSolow_next]
  exact (D.toSolow.tendsto_path D.isSteadyState_kstar hk0).congr fun t => (hpath t).symm

/-- `k*^{α − 1} = 1 / A`. -/
theorem kstar_rpow : D.kstar ^ (D.α - 1) = D.coef⁻¹ := by
  have h1α : 1 - D.α ≠ 0 := by linarith [D.hα₁]
  rw [kstar, ← Real.rpow_mul D.coef_pos.le,
    show 1 / (1 - D.α) * (D.α - 1) = -1 by field_simp; ring, Real.rpow_neg_one]

/-- **Steady-state interest rate:** `R* = α / A = α (1 + β)(1 + n) / (β (1 − α))`. -/
theorem rate_steadyState :
    D.rate D.kstar = D.α * (1 + D.β) * (1 + D.n) / (D.β * (1 - D.α)) := by
  have h1n : 0 < 1 + D.n := by linarith [D.hn]
  have hb : 0 < 1 + D.β := by linarith [D.hβ]
  have h1α : 0 < 1 - D.α := by linarith [D.hα₁]
  have := D.hβ
  rw [rate, kstar_rpow, coef]
  field_simp

/-- The golden-rule capital stock `k_gold = (α / (1 + n))^{1/(1−α)}`, where
`f'(k_gold) = 1 + n` (the growth rate of the economy, with `δ = 1`). -/
def kgold : ℝ := (D.α / (1 + D.n)) ^ (1 / (1 - D.α))

theorem kgold_pos : 0 < D.kgold :=
  Real.rpow_pos_of_pos (div_pos D.hα₀ (by linarith [D.hn])) _

theorem hasDerivAt_kgold : HasDerivAt (fun k => k ^ D.α) (1 + D.n) D.kgold := by
  have h := cobbDouglas_hasDerivAt_goldenRule D.toSolow D.hα₁ rfl D.hα₀
  simp only [toSolow] at h
  rw [show D.n + 1 = 1 + D.n by ring] at h
  exact h

theorem rate_kgold : D.rate D.kgold = 1 + D.n := by
  have h1 := D.hasDerivAt_kgold
  have h2 := Real.hasDerivAt_rpow_const (p := D.α) (Or.inl D.kgold_pos.ne')
  exact (h2.unique h1)

/-- The return on capital is strictly decreasing in `k`. -/
theorem rate_strictAntiOn : StrictAntiOn D.rate (Ioi 0) := by
  intro a ha b _ hab
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow_of_neg ha hab (by linarith [D.hα₁])) D.hα₀

/-- **Dynamic inefficiency (Acemoglu Prop. 9.4).** The following are
equivalent: (i) the steady-state interest rate is below the growth rate,
`R* < 1 + n`; (ii) `α (1 + β) < β (1 − α)`; (iii) the economy overaccumulates
capital, `k* > k_gold`. -/
theorem dynamicallyInefficient_iff :
    (D.rate D.kstar < 1 + D.n ↔ D.α * (1 + D.β) < D.β * (1 - D.α)) ∧
    (D.rate D.kstar < 1 + D.n ↔ D.kgold < D.kstar) := by
  have h1n : 0 < 1 + D.n := by linarith [D.hn]
  have h1α : 0 < 1 - D.α := by linarith [D.hα₁]
  have := D.hβ
  constructor
  · rw [rate_steadyState, div_lt_iff₀ (by positivity)]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [← D.rate_kgold]
    constructor
    · intro h
      by_contra hle
      have := D.rate_strictAntiOn.antitoneOn D.kstar_pos D.kgold_pos (not_lt.1 hle)
      linarith
    · intro h
      exact D.rate_strictAntiOn D.kgold_pos D.kstar_pos h

/-- Feasibility of a path in per-young-worker terms: capital is nonnegative and
aggregate consumption `C_t` plus next period's capital stock `(1 + n) k_{t+1}`
(full depreciation) does not exceed output `k_t^α`. -/
def IsFeasible (k C : ℕ → ℝ) : Prop :=
  ∀ t, 0 ≤ k t ∧ C t + (1 + D.n) * k (t + 1) ≤ k t ^ D.α

/-- The competitive steady state is feasible, with consumption
`C* = k*^α − (1 + n) k*` each period. -/
theorem isFeasible_steadyState :
    D.IsFeasible (fun _ => D.kstar) (fun _ => D.kstar ^ D.α - (1 + D.n) * D.kstar) :=
  fun _ => ⟨D.kstar_pos.le, by simp⟩

/-- **Overaccumulation is inefficient.** If `R* < 1 + n`, the path that
consumes the excess capital `k* − k_gold` now and then stays at `k_gold`
forever is feasible and gives strictly more aggregate consumption than the
competitive steady state in *every* period. "Dominates" here is about
aggregate consumption per young worker (as in Acemoglu's proof); since utility
is strictly increasing, the surplus can be divided so that every generation,
including the initial old, gains, but that division is not formalized. -/
theorem exists_dominating_path (h : D.rate D.kstar < 1 + D.n) :
    ∃ k C : ℕ → ℝ, k 0 = D.kstar ∧ D.IsFeasible k C ∧
      ∀ t, D.kstar ^ D.α - (1 + D.n) * D.kstar < C t := by
  have hlt := (D.dynamicallyInefficient_iff.2).1 h
  have h1n : 0 < 1 + D.n := by linarith [D.hn]
  let k : ℕ → ℝ := fun t => if t = 0 then D.kstar else D.kgold
  let C : ℕ → ℝ := fun t =>
    if t = 0 then D.kstar ^ D.α - (1 + D.n) * D.kgold else D.kgold ^ D.α - (1 + D.n) * D.kgold
  -- golden-rule consumption strictly beats any other steady state
  have hgold : D.kstar ^ D.α - (1 + D.n) * D.kstar < D.kgold ^ D.α - (1 + D.n) * D.kgold :=
    goldenRule_lt (f := fun k => k ^ D.α) (Real.strictConcaveOn_rpow D.hα₀ D.hα₁)
      D.kgold_pos.le D.hasDerivAt_kgold D.kstar_pos.le hlt.ne'
  refine ⟨k, C, by simp [k], fun t => ?_, fun t => ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [k, C, ite_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      exact ⟨D.kstar_pos.le, by linarith⟩
    · simp only [k, C, ht.ne', ite_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      exact ⟨D.kgold_pos.le, by linarith⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [C, ite_true]
      nlinarith
    · simp only [C, ht.ne', ite_false]
      exact hgold

/-! ## The converse: with `R* ≥ 1 + n` the steady state is efficient -/

/-- Steady-state consumption `g(k) = k^α − (1 + n) k` is strictly increasing
below the golden rule. -/
theorem consumption_strictMonoOn {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ D.kgold) :
    a ^ D.α - (1 + D.n) * a < b ^ D.α - (1 + D.n) * b := by
  have hconc := Real.strictConcaveOn_rpow D.hα₀ D.hα₁
  have hmax : ∀ x, 0 ≤ x → x ^ D.α - (1 + D.n) * x ≤ D.kgold ^ D.α - (1 + D.n) * D.kgold :=
    fun x hx => goldenRule_le (f := fun k => k ^ D.α) hconc D.kgold_pos.le D.hasDerivAt_kgold hx
  rcases hb.lt_or_eq with hb | rfl
  · -- write `b = λ a + (1 − λ) k_gold` and use strict concavity
    have hka : 0 < D.kgold - a := by linarith
    have hl0 : 0 < (D.kgold - b) / (D.kgold - a) := div_pos (by linarith) hka
    have hl1 : 0 < 1 - (D.kgold - b) / (D.kgold - a) := by
      rw [sub_pos, div_lt_one hka]; linarith
    have hbl : (D.kgold - b) / (D.kgold - a) * a + (1 - (D.kgold - b) / (D.kgold - a)) * D.kgold
        = b := by
      field_simp; ring
    have hc := hconc.2 (Set.mem_Ici.2 ha) (Set.mem_Ici.2 D.kgold_pos.le) (by linarith : a ≠ D.kgold)
      hl0 hl1 (by ring)
    simp only [smul_eq_mul] at hc
    rw [hbl] at hc
    have e2 : (1 + D.n) * b = (D.kgold - b) / (D.kgold - a) * ((1 + D.n) * a) +
        (1 - (D.kgold - b) / (D.kgold - a)) * ((1 + D.n) * D.kgold) := by
      conv_lhs => rw [← hbl]
      ring
    have hg := mul_le_mul_of_nonneg_left (hmax a ha) hl1.le
    nlinarith
  · exact goldenRule_lt (f := fun k => k ^ D.α) hconc D.kgold_pos.le D.hasDerivAt_kgold ha
      hab.ne

/-- **Dynamic efficiency (the converse half of Acemoglu Prop. 9.4).** If the
steady-state interest rate is at least the growth rate, `R* ≥ 1 + n`, then no
feasible path starting from `k*` gives at least steady-state consumption in
every period and strictly more in some period.

Proof sketch: by concavity, a path that never consumes less than `C*` must
keep `k_t ≤ k*` and nonincreasing (because `R* ≥ 1 + n`); consuming strictly
more once pushes capital strictly below `k*`, after which steady-state
consumption `g(k_t)` falls short of `g(k*)` by a fixed gap every period (since
`k* ≤ k_gold`). Summing, `k_t` would have to become negative. -/
theorem no_dominating_path (h : 1 + D.n ≤ D.rate D.kstar) {k C : ℕ → ℝ}
    (h0 : k 0 = D.kstar) (hF : D.IsFeasible k C)
    (hge : ∀ t, D.kstar ^ D.α - (1 + D.n) * D.kstar ≤ C t) :
    ∀ t, C t = D.kstar ^ D.α - (1 + D.n) * D.kstar := by
  set ks := D.kstar
  set c := 1 + D.n
  have hc : 0 < c := by simp only [c]; linarith [D.hn]
  have hks := D.kstar_pos
  -- tangent line at `k*`: `k^α ≤ k*^α + R* (k − k*)`
  have hd : HasDerivAt (fun k => k ^ D.α) (D.rate ks) ks :=
    Real.hasDerivAt_rpow_const (Or.inl hks.ne')
  have tang : ∀ x, 0 ≤ x → x ^ D.α ≤ ks ^ D.α + D.rate ks * (x - ks) := by
    intro x hx
    rcases eq_or_ne x ks with rfl | hne
    · simp
    · exact (lt_tangent (f := fun k => k ^ D.α) (Real.strictConcaveOn_rpow D.hα₀ D.hα₁)
        hks.le hd hx hne).le
  -- step: `c (k_{t+1} − k*) ≤ R* (k_t − k*) − (C_t − C*)`
  have step : ∀ t, c * (k (t + 1) - ks) ≤ D.rate ks * (k t - ks) -
      (C t - (ks ^ D.α - c * ks)) := by
    intro t
    have := (hF t).2
    have := tang (k t) (hF t).1
    linarith
  -- capital is nonincreasing and stays at or below `k*`
  have mono : ∀ t, k t ≤ ks ∧ k (t + 1) ≤ k t := by
    intro t
    induction t with
    | zero =>
      refine ⟨h0.le, ?_⟩
      have h1 := step 0
      have h2 := hge 0
      rw [zero_add] at h1 ⊢
      rw [h0] at h1 ⊢
      nlinarith
    | succ t ih =>
      have hle : k (t + 1) ≤ ks := ih.2.trans ih.1
      refine ⟨hle, ?_⟩
      have := step (t + 1); have := hge (t + 1)
      have : D.rate ks * (k (t + 1) - ks) ≤ c * (k (t + 1) - ks) :=
        mul_le_mul_of_nonpos_right h (by linarith)
      nlinarith
  intro s
  by_contra hne
  have hgt : ks ^ D.α - c * ks < C s := lt_of_le_of_ne (hge s) (Ne.symm hne)
  -- after a strict gain, capital is strictly below `k*`
  have hbelow : k (s + 1) < ks := by
    have := step s
    have : D.rate ks * (k s - ks) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (D.rate_pos hks).le (by linarith [(mono s).1])
    nlinarith
  have hanti : ∀ N, k (s + 1 + N) ≤ k (s + 1) := by
    intro N
    induction N with
    | zero => exact le_rfl
    | succ N ih => exact ((mono (s + 1 + N)).2).trans ih
  -- `k* ≤ k_gold`, since `R* ≥ 1 + n`
  have hgold : ks ≤ D.kgold := not_lt.1 fun hlt => by
    have := (D.dynamicallyInefficient_iff.2).2 hlt
    simp only [c] at h
    linarith
  set gap := (ks ^ D.α - c * ks) - (k (s + 1) ^ D.α - c * k (s + 1))
  have hgap : 0 < gap := by
    have := D.consumption_strictMonoOn (hF (s + 1)).1 hbelow hgold
    simp only [gap, c]
    linarith
  -- each later period loses at least `gap` relative to `C*`, paid for by capital
  have loss : ∀ N, N * gap ≤ c * (k (s + 1) - k (s + 1 + N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      set t := s + 1 + N
      have hkt := hanti N
      have hkt0 := (hF t).1
      have hg : k t ^ D.α - c * k t ≤ k (s + 1) ^ D.α - c * k (s + 1) := by
        rcases (hkt.lt_or_eq) with hlt | heq
        · exact (D.consumption_strictMonoOn hkt0 hlt ((hbelow.le).trans hgold)).le
        · rw [heq]
      have := (hF t).2
      have := hge t
      have e : s + 1 + (N + 1) = t + 1 := by simp only [t]; ring
      rw [e]
      push_cast
      simp only [gap] at ih ⊢
      nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (c * ks / gap)
  have := loss N
  have hk0 := (hF (s + 1 + N)).1
  rw [div_lt_iff₀ hgap] at hN
  nlinarith [mul_le_mul_of_nonneg_left hbelow.le hc.le]

/-- **The complete characterization (Acemoglu Prop. 9.4).** The competitive
steady state can be improved upon (a feasible path from `k*` with strictly more
consumption in every period exists) iff `R* < 1 + n`; when `R* ≥ 1 + n` not
even a weak improvement exists. -/
theorem dynamicallyInefficient_iff_exists_improvement :
    D.rate D.kstar < 1 + D.n ↔
      ∃ k C : ℕ → ℝ, k 0 = D.kstar ∧ D.IsFeasible k C ∧
        (∀ t, D.kstar ^ D.α - (1 + D.n) * D.kstar ≤ C t) ∧
        ∃ t, D.kstar ^ D.α - (1 + D.n) * D.kstar < C t := by
  constructor
  · intro h
    obtain ⟨k, C, h0, hF, hlt⟩ := D.exists_dominating_path h
    exact ⟨k, C, h0, hF, fun t => (hlt t).le, 0, hlt 0⟩
  · rintro ⟨k, C, h0, hF, hge, t, ht⟩
    by_contra hle
    have := D.no_dominating_path (not_lt.1 hle) h0 hF hge t
    linarith

/-- **Non-vacuity.** Dynamic inefficiency really happens: with `α = 1/4`,
`β = 1`, `n = 0` the steady-state interest rate is below the growth rate. -/
example : (⟨1 / 4, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩ : Diamond).rate
    (⟨1 / 4, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩ : Diamond).kstar < 1 + 0 :=
  ((Diamond.dynamicallyInefficient_iff _).1).2 (by norm_num)

/-- …and need not happen: with `α = 1/2`, `β = 1`, `n = 0` the economy is
dynamically efficient. -/
example : ¬ (⟨1 / 2, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩ : Diamond).rate
    (⟨1 / 2, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩ : Diamond).kstar < 1 + 0 := by
  rw [((Diamond.dynamicallyInefficient_iff _).1)]
  norm_num

end Diamond

end OLG
end Econ

end
