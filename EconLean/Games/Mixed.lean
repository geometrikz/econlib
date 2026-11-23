/-
# Mixed strategies and existence of Nash equilibrium

MWG §8.D–8.E (Defs. 8.D.1–8.D.2, Props. 8.D.1–8.D.3). In a finite game a mixed strategy
for player `i` is a lottery over `S i`, the same `lotteries` used for vN–M expected utility
in `Uncertainty/VNM.lean`: a mixed strategy is just a lottery whose outcomes are pure
strategies, and payoffs are expected utilities.

* `profileProb σ s = ∏ⱼ σⱼ(sⱼ)`: players randomize independently.
* `mixedPayoff u σ i = ∑ₛ profileProb σ s · uᵢ(s)`.
* `IsMixedNash u σ`: `σ` is a profile of lotteries and no player gains by switching to any
  other lottery.

Main results:
* `mixedPayoff_update`: payoffs are linear in a player's own mixture.
* `isMixedNash_iff_pure` (MWG Prop. 8.D.1): it suffices to check pure deviations, and
  `IsMixedNash.eq_of_pos`: every pure strategy played with positive probability earns
  exactly the equilibrium payoff (the indifference principle).
* `isMixedNash_degenerate_iff`: pure Nash equilibria are exactly mixed equilibria in
  degenerate lotteries.
* `exists_isMixedNash` (Nash 1950; MWG Prop. 8.D.2): every finite game has a mixed Nash
  equilibrium. The proof is Nash's: a fixed point of the "Nash map" that shifts
  probability towards profitable pure deviations is an equilibrium.

Brouwer's theorem comes from the shared `Foundations/FixedPoint.lean`
(`brouwer_fixedPoint_continuousMap`).
-/
module

public import EconLean.Games.Strategic
public import EconLean.Uncertainty.VNM
public import EconLean.Foundations.FixedPoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace Econ

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Probability of the pure profile `s` when players mix independently according to `σ`. -/
def profileProb (σ : ∀ i, S i → ℝ) (s : ∀ i, S i) : ℝ := ∏ j, σ j (s j)

/-- Expected payoff of player `i` under the mixed profile `σ`. -/
def mixedPayoff (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) : ℝ :=
  ∑ s, profileProb σ s * u i s

/-- `σ` is a profile of mixed strategies: each `σ i` is a lottery over `S i`. -/
def IsMixedProfile (σ : ∀ i, S i → ℝ) : Prop := ∀ i, σ i ∈ lotteries (S i)

/-- **Mixed-strategy Nash equilibrium** (MWG Def. 8.D.2). -/
def IsMixedNash (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) : Prop :=
  IsMixedProfile σ ∧
    ∀ i, ∀ τ ∈ lotteries (S i), mixedPayoff u (update σ i τ) i ≤ mixedPayoff u σ i

/-- Payoff of player `i` from the pure deviation to `t` against `σ₋ᵢ`. -/
def pureDev (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) (t : S i) : ℝ :=
  mixedPayoff u (update σ i (degenerate t)) i

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem profileProb_update (σ : ∀ i, S i → ℝ) (i : I) (τ : S i → ℝ) (s : ∀ i, S i) :
    profileProb (update σ i τ) s = τ (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  rw [profileProb, ← Finset.mul_prod_erase univ _ (mem_univ i), update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Linearity in own mixture.** Player `i`'s choice of `τ` affects every payoff `uₖ`
linearly: it averages the payoffs of the pure strategies `t` with weights `τ t`. -/
theorem mixedPayoff_update (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I)
    (τ : S i → ℝ) (k : I) :
    mixedPayoff u (update σ i τ) k =
      ∑ t, τ t * mixedPayoff u (update σ i (degenerate t)) k := by
  simp only [mixedPayoff, profileProb_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [degenerate, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [mul_assoc]

/-- A player's equilibrium payoff is the `σ i`-average of its pure-deviation payoffs. -/
theorem mixedPayoff_eq_sum_pureDev (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) :
    mixedPayoff u σ i = ∑ t, σ i t * pureDev u σ i t := by
  conv_lhs => rw [← update_eq_self i σ]
  exact mixedPayoff_update u σ i (σ i) i

theorem pureDev_update (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) (τ : S i → ℝ)
    (t : S i) : pureDev u (update σ i τ) i t = pureDev u σ i t := by
  simp [pureDev]

/-- **MWG Prop. 8.D.1 (pure deviations suffice).** A mixed profile is a Nash equilibrium
iff no pure deviation is profitable. -/
theorem isMixedNash_iff_pure {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (hσ : IsMixedProfile σ) :
    IsMixedNash u σ ↔ ∀ i t, pureDev u σ i t ≤ mixedPayoff u σ i := by
  refine ⟨fun h i t => h.2 i _ (degenerate_mem t), fun h => ⟨hσ, fun i τ hτ => ?_⟩⟩
  rw [mixedPayoff_update]
  calc ∑ t, τ t * mixedPayoff u (update σ i (degenerate t)) i
      ≤ ∑ t, τ t * mixedPayoff u σ i :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h i t) (hτ.1 t)
    _ = mixedPayoff u σ i := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- **Indifference principle** (MWG Prop. 8.D.1): in a mixed equilibrium every pure
strategy played with positive probability earns exactly the equilibrium payoff. -/
theorem IsMixedNash.eq_of_pos {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) {i : I} {t : S i} (ht : 0 < σ i t) :
    pureDev u σ i t = mixedPayoff u σ i := by
  have hle := (isMixedNash_iff_pure h.1).1 h i
  -- `∑ σ_t (payoff - dev_t) = 0` with every term nonnegative.
  have hsum : ∑ t, σ i t * (mixedPayoff u σ i - pureDev u σ i t) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (h.1 i).2, one_mul]
    rw [← mixedPayoff_eq_sum_pureDev, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun t _ =>
    mul_nonneg ((h.1 i).1 t) (sub_nonneg.2 (hle t))).1 hsum t (mem_univ t)
  rcases mul_eq_zero.1 hterm with h0 | h0
  · exact absurd h0 ht.ne'
  · linarith

omit [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem profileProb_nonneg {σ : ∀ i, S i → ℝ} (hσ : IsMixedProfile σ) (s : ∀ i, S i) :
    0 ≤ profileProb σ s :=
  Finset.prod_nonneg fun j _ => (hσ j).1 (s j)

omit [∀ i, DecidableEq (S i)] in
/-- Independent mixing gives a probability distribution on profiles. -/
theorem sum_profileProb {σ : ∀ i, S i → ℝ} (hσ : IsMixedProfile σ) :
    ∑ s, profileProb σ s = 1 := by
  have h := Finset.prod_univ_sum (fun j => (Finset.univ : Finset (S j))) (fun j t => σ j t)
  rw [Fintype.piFinset_univ] at h
  simp only [profileProb]
  rw [← h]
  exact Finset.prod_eq_one fun j _ => (hσ j).2

/-- **Reindexing slices.** Summing `g (update s i t)` over the profiles where `i` plays `x`
(weighted by the others' mixtures) is the same as summing `g` over the profiles where `i`
plays `t`. -/
theorem sum_update_degenerate (σ : ∀ i, S i → ℝ) (i : I) (x t : S i) (g : (∀ j, S j) → ℝ) :
    ∑ s, profileProb (update σ i (degenerate x)) s * g (update s i t) =
      ∑ s, profileProb (update σ i (degenerate t)) s * g s := by
  set Q : (∀ j, S j) → ℝ := fun s => ∏ j ∈ univ.erase i, σ j (s j)
  have hQ : ∀ s (y : S i), Q (update s i y) = Q s := fun s y =>
    Finset.prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [profileProb_update, degenerate, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun s => update s i t) (fun s => update s i x) ?_ ?_ ?_ ?_ ?_
  · intro s _; simp
  · intro s _; simp
  · intro s hs
    rw [Finset.mem_filter] at hs
    rw [update_idem, hs.2, update_eq_self]
  · intro s hs
    rw [Finset.mem_filter] at hs
    rw [update_idem, hs.2, update_eq_self]
  · intro s _
    show Q s * g (update s i t) = Q (update s i t) * g (update s i t)
    rw [hQ]

/-- The payoff of a pure deviation to `t` is the expected payoff of the profile with `sᵢ`
replaced by `t`, under the original mixture (whatever `σ i` is, as long as it is a
lottery). -/
theorem pureDev_eq_sum_update (u : I → (∀ j, S j) → ℝ) {σ : ∀ i, S i → ℝ} {i : I}
    (hσi : σ i ∈ lotteries (S i)) (t : S i) :
    pureDev u σ i t = ∑ s, profileProb σ s * u i (update s i t) := by
  have h := mixedPayoff_eq_sum_pureDev (fun _ s => u i (update s i t)) σ i
  simp only [mixedPayoff, pureDev] at h
  rw [h]
  simp only [sum_update_degenerate σ i _ t (u i)]
  rw [← Finset.sum_mul, hσi.2, one_mul]
  rfl

omit [∀ i, Fintype (S i)] in
/-- Restricting the product distribution to `sᵢ = t` is `σᵢ(t)` times the profile in which
`i` plays `t` for sure. -/
theorem profileProb_slice (σ : ∀ i, S i → ℝ) (i : I) (t : S i) (s : ∀ i, S i) :
    (if s i = t then profileProb σ s else 0) =
      σ i t * profileProb (update σ i (degenerate t)) s := by
  have h := profileProb_update σ i (σ i) s
  rw [update_eq_self] at h
  rw [profileProb_update, h, degenerate]
  by_cases h1 : s i = t
  · simp only [h1, ↓reduceIte, one_mul]
  · simp only [h1, Ne.symm h1, ↓reduceIte, zero_mul, mul_zero]

/-- The degenerate mixed profile putting probability one on the pure profile `s`. -/
def pureProfile (s : ∀ i, S i) : ∀ i, S i → ℝ := fun i => degenerate (s i)

omit [DecidableEq I] [∀ i, Fintype (S i)] in
theorem profileProb_pureProfile (s s' : ∀ i, S i) :
    profileProb (pureProfile s) s' = if s = s' then 1 else 0 := by
  simp only [profileProb, pureProfile, degenerate, Finset.prod_boole, mem_univ, true_imp_iff]
  congr 1
  exact propext ⟨fun h => funext h, fun h j => congrFun h j⟩

theorem mixedPayoff_pureProfile (u : I → (∀ j, S j) → ℝ) (s : ∀ i, S i) (i : I) :
    mixedPayoff u (pureProfile s) i = u i s := by
  simp [mixedPayoff, profileProb_pureProfile]

omit [Fintype I] [∀ i, Fintype (S i)] in
theorem update_pureProfile (s : ∀ i, S i) (i : I) (t : S i) :
    update (pureProfile s) i (degenerate t) = pureProfile (update s i t) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [pureProfile]
  · simp [pureProfile, update_of_ne hj]

/-- Pure Nash equilibria are exactly the mixed equilibria in degenerate lotteries. -/
theorem isMixedNash_pureProfile_iff (u : I → (∀ j, S j) → ℝ) (s : ∀ i, S i) :
    IsMixedNash u (pureProfile s) ↔ IsNash u s := by
  rw [isMixedNash_iff_pure (σ := pureProfile s) fun i => degenerate_mem (s i)]
  simp only [pureDev, update_pureProfile, mixedPayoff_pureProfile, IsNash]

/-! ### Existence (Nash 1950) -/

/-- The set of lotteries is compact. -/
theorem isCompact_lotteries (C : Type*) [Fintype C] : IsCompact (lotteries C) := by
  have hsub : lotteries C ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 := by
    intro L hL c _
    refine ⟨hL.1 c, ?_⟩
    rw [← hL.2]
    exact Finset.single_le_sum (fun c _ => hL.1 c) (mem_univ c)
  have hclosed : IsClosed (lotteries C) := by
    have : lotteries C = (⋂ c, {L : C → ℝ | 0 ≤ L c}) ∩ {L | ∑ c, L c = 1} := by
      ext L; simp [lotteries]
    rw [this]
    refine (isClosed_iInter fun c => ?_).inter ?_
    · exact isClosed_le continuous_const (continuous_apply c)
    · exact isClosed_eq (continuous_finsetSum _ fun c _ => continuous_apply c)
        continuous_const
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub

/-- The gain from switching to pure strategy `t`, if positive. -/
def nashGain (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) (t : S i) : ℝ :=
  max 0 (pureDev u σ i t - mixedPayoff u σ i)

/-- **Nash's map**: move probability towards profitable pure deviations. -/
noncomputable def nashMap (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i t => (σ i t + nashGain u σ i t) / (1 + ∑ b, nashGain u σ i b)

omit [∀ i, DecidableEq (S i)] in
theorem continuous_mixedPayoff (u : I → (∀ j, S j) → ℝ) (i : I) :
    Continuous fun σ : ∀ i, S i → ℝ => mixedPayoff u σ i := by
  unfold mixedPayoff profileProb
  fun_prop

theorem continuous_pureDev (u : I → (∀ j, S j) → ℝ) (i : I) (t : S i) :
    Continuous fun σ : ∀ i, S i → ℝ => pureDev u σ i t := by
  unfold pureDev
  exact (continuous_mixedPayoff u i).comp (continuous_id.update i continuous_const)

theorem continuous_nashGain (u : I → (∀ j, S j) → ℝ) (i : I) (t : S i) :
    Continuous fun σ : ∀ i, S i → ℝ => nashGain u σ i t :=
  continuous_const.max ((continuous_pureDev u i t).sub (continuous_mixedPayoff u i))

theorem nashGain_nonneg (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) (t : S i) :
    0 ≤ nashGain u σ i t := le_max_left _ _

theorem continuous_nashMap (u : I → (∀ j, S j) → ℝ) : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun t => ?_
  have h1 : Continuous fun σ : ∀ i, S i → ℝ => σ i t := (continuous_apply t).comp (continuous_apply i)
  refine (h1.add (continuous_nashGain u i t)).div
    (continuous_const.add (continuous_finsetSum _ fun b _ => continuous_nashGain u i b))
    fun σ => ?_
  exact (add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun b _ => nashGain_nonneg u σ i b)).ne'

theorem nashMap_mem {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ} (hσ : IsMixedProfile σ) :
    IsMixedProfile (nashMap u σ) := by
  intro i
  have hD : 0 < 1 + ∑ b, nashGain u σ i b :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun b _ => nashGain_nonneg u σ i b)
  refine ⟨fun t => div_nonneg (add_nonneg ((hσ i).1 t) (nashGain_nonneg u σ i t)) hD.le, ?_⟩
  simp only [nashMap]
  rw [← Finset.sum_div, Finset.sum_add_distrib, (hσ i).2]
  exact div_self hD.ne'

/-- Some pure strategy in the support does no better than the mixture itself. -/
theorem exists_pos_pureDev_le {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (hσ : IsMixedProfile σ) (i : I) :
    ∃ t, 0 < σ i t ∧ pureDev u σ i t ≤ mixedPayoff u σ i := by
  by_contra hno
  push Not at hno
  have hsum : ∑ t, σ i t * (pureDev u σ i t - mixedPayoff u σ i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hσ i).2, one_mul]
    rw [← mixedPayoff_eq_sum_pureDev, sub_self]
  have hpos : 0 < ∑ t, σ i t * (pureDev u σ i t - mixedPayoff u σ i) := by
    obtain ⟨t0, ht0⟩ : ∃ t, 0 < σ i t := by
      by_contra h
      push Not at h
      have : ∑ t, σ i t ≤ 0 := Finset.sum_nonpos fun t _ => h t
      linarith [(hσ i).2]
    refine Finset.sum_pos' (fun t _ => ?_) ⟨t0, mem_univ _, ?_⟩
    · rcases ((hσ i).1 t).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]
      · exact (mul_pos h0 (sub_pos.2 (hno t h0))).le
    · exact mul_pos ht0 (sub_pos.2 (hno t0 ht0))
  linarith

/-- Fixed points of Nash's map are Nash equilibria. -/
theorem isMixedNash_of_nashMap_eq {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (hσ : IsMixedProfile σ) (hfix : nashMap u σ = σ) : IsMixedNash u σ := by
  rw [isMixedNash_iff_pure hσ]
  intro i
  obtain ⟨t, ht, hle⟩ := exists_pos_pureDev_le (u := u) hσ i
  have hg0 : nashGain u σ i t = 0 := max_eq_left (by linarith)
  set G := ∑ b, nashGain u σ i b
  have hG : 0 ≤ G := Finset.sum_nonneg fun b _ => nashGain_nonneg u σ i b
  -- The fixed-point equation at `t`: `σₜ = σₜ / (1 + G)`, so `G = 0`.
  have hfix_t : (σ i t + 0) / (1 + G) = σ i t := by
    have := congrFun (congrFun hfix i) t
    simpa only [nashMap, hg0] using this
  have hG0 : G = 0 := by
    rw [add_zero, div_eq_iff (by linarith)] at hfix_t
    nlinarith
  intro b
  have hb := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => nashGain_nonneg u σ i b).1 hG0 b
    (mem_univ b)
  have : pureDev u σ i b - mixedPayoff u σ i ≤ 0 := hb ▸ le_max_right _ _
  linarith

/-- **Existence of mixed Nash equilibrium** (Nash 1950; MWG Prop. 8.D.2): every finite
game (finitely many players, each with finitely many, and at least one, pure strategies)
has a mixed-strategy Nash equilibrium. -/
theorem exists_isMixedNash [∀ i, Nonempty (S i)] (u : I → (∀ j, S j) → ℝ) :
    ∃ σ, IsMixedNash u σ := by
  set K : Set (∀ i, S i → ℝ) := Set.pi Set.univ fun i => lotteries (S i)
  have hK : ∀ σ, σ ∈ K ↔ IsMixedProfile σ := fun σ => by
    simp [K, IsMixedProfile, Set.mem_pi]
  have hconv : Convex ℝ K := convex_pi fun i _ => convex_lotteries
  have hcpt : IsCompact K := isCompact_univ_pi fun i => isCompact_lotteries (S i)
  have hne : K.Nonempty :=
    ⟨fun i => degenerate (Classical.arbitrary (S i)), (hK _).2 fun i => degenerate_mem _⟩
  let f : C(K, K) :=
    ⟨fun σ => ⟨nashMap u σ, (hK _).2 (nashMap_mem ((hK _).1 σ.2))⟩,
      ((continuous_nashMap u).comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨σ, hσ⟩ := brouwer_fixedPoint_continuousMap hconv hcpt hne f
  exact ⟨σ, isMixedNash_of_nashMap_eq ((hK _).1 σ.2) (congrArg Subtype.val hσ)⟩

/-! ### Witness: matching pennies

Player `true` wants to match, player `false` wants to mismatch. There is no pure
equilibrium, and both mixing `1/2`–`1/2` is an equilibrium. -/

/-- Matching pennies: the matcher (`true`) wins `1` on a match, loses `1` otherwise. -/
def penniesPayoff (i : Bool) (s : Bool → Bool) : ℝ :=
  if (s true = s false) = i then 1 else -1

/-- Sums over the four pure profiles of a two-player, two-strategy game. -/
theorem sum_bool_arrow_bool (f : (Bool → Bool) → ℝ) :
    ∑ x, f x = f (fun b => b) + (f (fun b => !b) + (f (fun _ => true) + f (fun _ => false))) := by
  rw [show (Finset.univ : Finset (Bool → Bool)) =
      {fun b => b, fun b => !b, fun _ => true, fun _ => false} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]

example : (∀ s, ¬ IsNash penniesPayoff s) ∧
    IsMixedNash penniesPayoff (fun _ _ => 1 / 2) := by
  constructor
  · intro s hs
    cases ht : s true <;> cases hf : s false
    · have := hs false true; simp_all [penniesPayoff, update]; norm_num at this
    · have := hs true true; simp_all [penniesPayoff, update]; norm_num at this
    · have := hs true false; simp_all [penniesPayoff, update]; norm_num at this
    · have := hs false false; simp_all [penniesPayoff, update]; norm_num at this
  · have hσ : IsMixedProfile (I := Bool) (S := fun _ => Bool) (fun _ _ => (1 / 2 : ℝ)) :=
      fun i => ⟨fun _ => by norm_num, by simp⟩
    rw [isMixedNash_iff_pure hσ]
    intro i t
    -- Against a 50–50 opponent every pure strategy earns 0, the same as the mixture.
    simp only [pureDev, mixedPayoff, profileProb, Fintype.prod_bool, sum_bool_arrow_bool,
      penniesPayoff, update]
    cases i <;> cases t <;> norm_num

end Econ
