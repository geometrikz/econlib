/-
# Correlated equilibrium

Aumann (1974); Fudenberg–Tirole §2.2 (Def. 2.5); not covered in MWG's main text. A mediator draws a pure
profile `s` from a joint distribution `μ` and privately recommends `sᵢ` to each player
`i`. `μ` is a **correlated equilibrium** if obeying is optimal: for every player `i`,
recommendation `t` and alternative `t'`,
`∑_{s : sᵢ = t} μ(s) [uᵢ(t', s₋ᵢ) − uᵢ(s)] ≤ 0`.

Main results:
* `isCorrelatedEq_of_isMixedNash`: the product distribution of a mixed Nash equilibrium
  is a correlated equilibrium (so correlated equilibria exist,
  `exists_isCorrelatedEq`).
* `convex_correlatedEq`: the set of correlated equilibria is convex; it is cut out by
  finitely many linear inequalities.
* Witness: in the game of chicken the "traffic light" (each of the two asymmetric
  outcomes with probability `1/2`) is a correlated equilibrium.
-/
module

public import EconLean.Games.Mixed

@[expose] public section

namespace Econ

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Expected gain to player `i` from switching to `t'` whenever told to play `t`. -/
def obedienceGain (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I) (t t' : S i) : ℝ :=
  ∑ s, if s i = t then μ s * (u i (update s i t') - u i s) else 0

/-- **Correlated equilibrium**: `μ` is a probability distribution on pure profiles under
which no player gains by disobeying any recommendation. -/
def IsCorrelatedEq (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) : Prop :=
  μ ∈ lotteries (∀ j, S j) ∧ ∀ i (t t' : S i), obedienceGain u μ i t t' ≤ 0

omit [∀ i, DecidableEq (S i)] in
/-- The product distribution of a mixed profile is a probability distribution. -/
theorem profileProb_mem {σ : ∀ i, S i → ℝ} (hσ : IsMixedProfile σ) :
    profileProb σ ∈ lotteries (∀ j, S j) :=
  ⟨profileProb_nonneg hσ, sum_profileProb hσ⟩

/-- Under a product distribution the obedience gain is `σᵢ(t)` times the payoff difference
between the pure strategies `t'` and `t`. -/
theorem obedienceGain_profileProb (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I)
    (t t' : S i) :
    obedienceGain u (profileProb σ) i t t' = σ i t * (pureDev u σ i t' - pureDev u σ i t) := by
  have h : ∀ s, (if s i = t then profileProb σ s * (u i (update s i t') - u i s) else 0) =
      σ i t * (profileProb (update σ i (degenerate t)) s * (u i (update s i t') - u i s)) := by
    intro s
    rw [← mul_assoc, ← profileProb_slice]
    split_ifs <;> simp
  unfold obedienceGain
  rw [Finset.sum_congr rfl fun s _ => h s, ← Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_update_degenerate σ i t t' (u i)]
  rfl

/-- **Mixed Nash equilibria are correlated equilibria** (Aumann 1974). -/
theorem isCorrelatedEq_of_isMixedNash {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) : IsCorrelatedEq u (profileProb σ) := by
  refine ⟨profileProb_mem h.1, fun i t t' => ?_⟩
  rw [obedienceGain_profileProb]
  rcases ((h.1 i).1 t).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
  · rw [h.eq_of_pos h0]
    exact mul_nonpos_of_nonneg_of_nonpos h0.le
      (sub_nonpos.2 ((isMixedNash_iff_pure h.1).1 h i t'))

/-- **Correlated equilibria exist** in every finite game (from Nash's theorem). -/
theorem exists_isCorrelatedEq [∀ i, Nonempty (S i)] (u : I → (∀ j, S j) → ℝ) :
    ∃ μ, IsCorrelatedEq u μ := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNash u
  exact ⟨_, isCorrelatedEq_of_isMixedNash hσ⟩

/-- **The set of correlated equilibria is convex.** -/
theorem convex_correlatedEq (u : I → (∀ j, S j) → ℝ) :
    Convex ℝ {μ | IsCorrelatedEq u μ} := by
  intro μ hμ ν hν a b ha hb hab
  refine ⟨convex_lotteries hμ.1 hν.1 ha hb hab, fun i t t' => ?_⟩
  have e : obedienceGain u (a • μ + b • ν) i t t' =
      a * obedienceGain u μ i t t' + b * obedienceGain u ν i t t' := by
    simp only [obedienceGain, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · simp
  rw [e]
  nlinarith [hμ.2 i t t', hν.2 i t t']

/-! ### Witness: the traffic light in chicken

Each driver chooses `true` = go or `false` = stop. Both going crash (`0`), going against a
stopper pays `7`, stopping against a goer pays `2`, both stopping pays `6`. The mediator
picks (go, stop) or (stop, go) with probability `1/2` each. -/

/-- Chicken payoffs. -/
def chickenPayoff (i : Bool) (s : Bool → Bool) : ℝ :=
  match s i, s (!i) with
  | true, true => 0
  | true, false => 7
  | false, true => 2
  | false, false => 6

/-- The traffic light: probability `1/2` on each asymmetric profile. -/
noncomputable def trafficLight (s : Bool → Bool) : ℝ := if s true = s false then 0 else 1 / 2

example : IsCorrelatedEq chickenPayoff trafficLight := by
  refine ⟨⟨fun s => by unfold trafficLight; split_ifs <;> norm_num, ?_⟩, fun i t t' => ?_⟩
  · rw [sum_bool_arrow_bool]; simp [trafficLight]; norm_num
  · simp only [obedienceGain, sum_bool_arrow_bool, trafficLight, chickenPayoff, update]
    cases i <;> cases t <;> cases t' <;> norm_num

end Econ
