/-
# Infinitely repeated games: grim trigger and the Nash-reversion folk theorem

MWG §12.D (Prop. 12.D.1 and the Nash-reversion folk theorem, Friedman 1971); Fudenberg–Tirole
Ch. 5. A stage game `u : I → (∀ j, S j) → ℝ` is played in periods `0, 1, 2, …` with common
discount factor `δ ∈ [0, 1)`. A history is the list of past action profiles (most recent
first); a (pure) strategy maps histories to actions. A profile `σ` played from history `h`
generates the path `pathFrom σ h`, and player `i` gets the normalised discounted payoff
`(1 − δ) ∑ₜ δᵗ uᵢ(path t)`.

Main results:
* `discPayoff_le_of_bellman`: a **verification theorem**: if a bounded value process `W` along
  a path satisfies `(1 − δ) gₜ + δ Wₜ₊₁ ≤ Wₜ`, the discounted payoff is at most `W₀`.
* `grimTrigger_isSPE`: grim trigger (play `a*` while every past profile was `a*`, otherwise
  play the stage Nash equilibrium `e` forever) is a **subgame perfect equilibrium** whenever
  no player gains by a one-shot deviation from `a*` followed by Nash reversion:
  `(1 − δ) uᵢ(t, a*₋ᵢ) + δ uᵢ(e) ≤ uᵢ(a*)`. Subgame perfection is checked against **all**
  deviating strategies (not just one-shot deviations) after **every** history.
* `nashReversion_folk`: **Nash-reversion folk theorem.** With finitely many players and
  bounded stage payoffs, if `uᵢ(a*) > uᵢ(e)` for every `i`, grim trigger supporting `a*` is
  subgame perfect for all discount factors close enough to `1`.
-/
module

public import EconLean.Games.Strategic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

namespace Econ

open Function Filter Topology

variable {I : Type*} [DecidableEq I] {S : I → Type*}

/-- A pure strategy profile of the repeated game: each player maps histories (lists of past
action profiles, most recent first) to actions. -/
abbrev RepeatedProfile (S : I → Type*) := ∀ i, List (∀ j, S j) → S i

/-- The history after `t` further periods of play of `σ`, starting from history `h`. -/
def histFrom (σ : RepeatedProfile S) (h : List (∀ j, S j)) : ℕ → List (∀ j, S j)
  | 0 => h
  | t + 1 => (fun i => σ i (histFrom σ h t)) :: histFrom σ h t

/-- The action profile played in period `t` of the continuation game after history `h`. -/
def pathFrom (σ : RepeatedProfile S) (h : List (∀ j, S j)) (t : ℕ) : ∀ j, S j :=
  fun i => σ i (histFrom σ h t)

omit [DecidableEq I] in
lemma histFrom_succ (σ : RepeatedProfile S) (h : List (∀ j, S j)) (t : ℕ) :
    histFrom σ h (t + 1) = pathFrom σ h t :: histFrom σ h t := rfl

/-- Normalised discounted payoff of player `i` in the continuation game after history `h`. -/
noncomputable def discPayoff (u : I → (∀ j, S j) → ℝ) (δ : ℝ) (σ : RepeatedProfile S)
    (h : List (∀ j, S j)) (i : I) : ℝ :=
  (1 - δ) * ∑' t, δ ^ t * u i (pathFrom σ h t)

/-- **Subgame perfect equilibrium** of the repeated game with discount factor `δ ∈ [0, 1)`:
after every history, no player gains by switching to any other strategy of the repeated game.
The range of `δ` is part of the definition: at `δ = 1` the normalized payoff `(1 − δ) ∑ …` is
identically `0` and every profile would qualify. (`discPayoff` uses `tsum`, so this is
meaningful for bounded stage payoffs, which every theorem below assumes.) -/
def IsRepeatedSPE (u : I → (∀ j, S j) → ℝ) (δ : ℝ) (σ : RepeatedProfile S) : Prop :=
  0 ≤ δ ∧ δ < 1 ∧ ∀ (h : List (∀ j, S j)) (i : I) (τ : List (∀ j, S j) → S i),
    discPayoff u δ (update σ i τ) h i ≤ discPayoff u δ σ h i

/-- Bounded stage payoffs give summable discounted streams. -/
lemma summable_disc {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {g : ℕ → ℝ}
    (hg : ∀ t, |g t| ≤ M) : Summable fun t => δ ^ t * g t := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
  exact mul_le_mul_of_nonneg_left (hg t) (pow_nonneg hδ0 t)

/-- **Verification theorem.** If the bounded process `W` satisfies the one-period inequality
`(1 − δ) gₜ + δ Wₜ₊₁ ≤ Wₜ` along the path, the normalised discounted value of `g` is at
most `W₀`. -/
theorem discPayoff_le_of_bellman {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {g W : ℕ → ℝ} {B : ℝ}
    (hg : Summable fun t => δ ^ t * g t) (hW : ∀ t, |W t| ≤ B)
    (hstep : ∀ t, (1 - δ) * g t + δ * W (t + 1) ≤ W t) :
    (1 - δ) * ∑' t, δ ^ t * g t ≤ W 0 := by
  have hpart : ∀ T, (1 - δ) * (∑ s ∈ Finset.range T, δ ^ s * g s) + δ ^ T * W T ≤ W 0 := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have := mul_le_mul_of_nonneg_left (hstep T) (pow_nonneg hδ0 T)
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  have hlim : Tendsto (fun T => (1 - δ) * (∑ s ∈ Finset.range T, δ ^ s * g s) + δ ^ T * W T)
      atTop (𝓝 ((1 - δ) * ∑' t, δ ^ t * g t + 0)) := by
    refine (hg.hasSum.tendsto_sum_nat.const_mul _).add ?_
    have h0 : Tendsto (fun T => δ ^ T * B) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const B
    refine squeeze_zero_norm (fun T => ?_) h0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 T)]
    exact mul_le_mul_of_nonneg_left (hW T) (pow_nonneg hδ0 T)
  rw [add_zero] at hlim
  exact le_of_tendsto' hlim hpart

/-- A constant stream has normalised discounted value equal to the constant. -/
lemma disc_const {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (c : ℝ) :
    (1 - δ) * ∑' t : ℕ, δ ^ t * c = c := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
  field_simp [(sub_pos.2 hδ1).ne']

section Grim

open Classical

/-- A history is *clean* if every profile in it is the cooperative profile `a`. -/
def IsClean (a : ∀ j, S j) (h : List (∀ j, S j)) : Prop := ∀ b ∈ h, b = a

/-- **Grim trigger** supporting the profile `a` with Nash reversion to `e`: play `a` while
every past profile was `a`, otherwise play `e`. -/
noncomputable def grimTrigger (a e : ∀ j, S j) : RepeatedProfile S :=
  fun i h => if IsClean a h then a i else e i

variable {a e : ∀ j, S j}

omit [DecidableEq I] in
lemma isClean_cons {b : ∀ j, S j} {h : List (∀ j, S j)} :
    IsClean a (b :: h) ↔ b = a ∧ IsClean a h := by
  simp [IsClean]

omit [DecidableEq I] in
lemma grimTrigger_apply_clean {h : List (∀ j, S j)} (hc : IsClean a h) (i : I) :
    grimTrigger a e i h = a i := by
  simp only [grimTrigger, hc, ↓reduceIte]

omit [DecidableEq I] in
lemma grimTrigger_apply_dirty {h : List (∀ j, S j)} (hc : ¬ IsClean a h) (i : I) :
    grimTrigger a e i h = e i := by
  simp only [grimTrigger, hc, ↓reduceIte]

omit [DecidableEq I] in
/-- On its own, grim trigger yields the constant path `a` after a clean history and `e` after
a dirty one. -/
lemma grimTrigger_path (h : List (∀ j, S j)) (t : ℕ) :
    pathFrom (grimTrigger a e) h t = if IsClean a h then a else e := by
  induction t with
  | zero =>
    funext i
    by_cases hc : IsClean a h
    · simp only [pathFrom, histFrom, grimTrigger_apply_clean hc, hc, ↓reduceIte]
    · simp only [pathFrom, histFrom, grimTrigger_apply_dirty hc, hc, ↓reduceIte]
  | succ t ih =>
    funext i
    have hcl : IsClean a (histFrom (grimTrigger a e) h t) ↔ IsClean a h := by
      clear ih
      induction t with
      | zero => rfl
      | succ t ih' =>
        rw [histFrom_succ, isClean_cons, ih']
        constructor
        · exact And.right
        · intro hc
          refine ⟨?_, hc⟩
          funext j
          simp only [pathFrom, grimTrigger_apply_clean (ih'.2 hc)]
    have hcl' : IsClean a (histFrom (grimTrigger a e) h (t + 1)) ↔ IsClean a h := by
      rw [histFrom_succ, isClean_cons, hcl, ih]
      by_cases hc : IsClean a h <;> simp [hc]
    by_cases hc : IsClean a h
    · simp only [pathFrom, grimTrigger_apply_clean (hcl'.2 hc), hc, ↓reduceIte]
    · simp only [pathFrom, grimTrigger_apply_dirty (mt hcl'.1 hc), hc, ↓reduceIte]

omit [DecidableEq I] in
/-- On-path (and off-path) value of grim trigger. -/
lemma discPayoff_grimTrigger {u : I → (∀ j, S j) → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h : List (∀ j, S j)) (i : I) :
    discPayoff u δ (grimTrigger a e) h i = u i (if IsClean a h then a else e) := by
  simp only [discPayoff, grimTrigger_path]
  exact disc_const hδ0 hδ1 _

/-- **Grim trigger is subgame perfect** (MWG Prop. 12.D.1, Friedman 1971). If `e` is a Nash
equilibrium of the stage game and no player gains from a one-shot deviation from `a` followed
by permanent reversion to `e`, then grim trigger is a subgame perfect equilibrium of the
repeated game: after every history, no deviation to any repeated-game strategy is profitable.
Stage payoffs are assumed bounded. -/
theorem grimTrigger_isSPE {u : I → (∀ j, S j) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ i b, |u i b| ≤ M) (he : IsNash u e)
    (hdev : ∀ i (s : S i), (1 - δ) * u i (update a i s) + δ * u i e ≤ u i a) :
    IsRepeatedSPE u δ (grimTrigger a e) := by
  refine ⟨hδ0, hδ1, ?_⟩
  intro h i τ
  rw [discPayoff_grimTrigger hδ0 hδ1]
  set σ' := update (grimTrigger a e) i τ
  set H := histFrom σ' h
  -- The deviator's continuation value process.
  let W : ℕ → ℝ := fun t => u i (if IsClean a (H t) then a else e)
  have hpath : ∀ t, pathFrom σ' h t =
      update (if IsClean a (H t) then a else e) i (τ (H t)) := by
    intro t
    funext j
    by_cases hj : j = i
    · subst hj; simp [pathFrom, σ', H]
    · show update (grimTrigger a e) i τ j (H t) = _
      rw [update_of_ne hj, update_of_ne hj]
      by_cases hc : IsClean a (H t)
      · rw [grimTrigger_apply_clean hc]; simp only [hc, ↓reduceIte]
      · rw [grimTrigger_apply_dirty hc]; simp only [hc, ↓reduceIte]
  have hW : ∀ t, |W t| ≤ M := fun t => hM i _
  have hstep : ∀ t, (1 - δ) * u i (pathFrom σ' h t) + δ * W (t + 1) ≤ W t := by
    intro t
    have hnext : IsClean a (H (t + 1)) ↔ IsClean a (H t) ∧ pathFrom σ' h t = a := by
      simp only [H, histFrom_succ, isClean_cons]; exact and_comm
    simp only [W, hpath t]
    by_cases hc : IsClean a (H t)
    · simp only [hc, ↓reduceIte]
      by_cases hp : update a i (τ (H t)) = a
      · have : IsClean a (H (t + 1)) := hnext.2 ⟨hc, by rw [hpath t]; simp [hc, hp]⟩
        simp only [this, ↓reduceIte, hp]; ring_nf; rfl
      · have : ¬ IsClean a (H (t + 1)) := fun h' => hp (by
          have := (hnext.1 h').2; rw [hpath t] at this; simpa only [hc, ↓reduceIte] using this)
        simp only [this, ↓reduceIte]
        exact hdev i _
    · have : ¬ IsClean a (H (t + 1)) := fun h' => hc (hnext.1 h').1
      simp only [hc, this, ↓reduceIte]
      have := he i (τ (H t))
      nlinarith
  have := discPayoff_le_of_bellman hδ0 hδ1 (summable_disc hδ0 hδ1 fun t => hM i _) hW hstep
  exact this

/-- **Nash-reversion folk theorem** (Friedman 1971; MWG §12.D). With finitely many players and
bounded stage payoffs, if every player strictly prefers the pure profile `a` to the stage Nash
equilibrium `e`, then grim trigger supporting `a` is a subgame perfect equilibrium for every
discount factor sufficiently close to `1`. -/
theorem nashReversion_folk [Finite I] {u : I → (∀ j, S j) → ℝ} {M : ℝ}
    (hM : ∀ i b, |u i b| ≤ M) (he : IsNash u e) (hgain : ∀ i, u i e < u i a) :
    ∀ᶠ δ in 𝓝[<] (1 : ℝ), 0 ≤ δ ∧ IsRepeatedSPE u δ (grimTrigger a e) := by
  have hev : ∀ i, ∀ᶠ δ in 𝓝[<] (1 : ℝ), 0 ≤ δ ∧
      ∀ s : S i, (1 - δ) * u i (update a i s) + δ * u i e ≤ u i a := by
    intro i
    have hMa : u i a ≤ M := (abs_le.1 (hM i a)).2
    -- Threshold `c = max 0 ((M − uᵢ(a)) / (M − uᵢ(e))) < 1`.
    have hden : 0 < M - u i e := by linarith [hgain i]
    set c := max 0 ((M - u i a) / (M - u i e))
    have hc1 : c < 1 := max_lt one_pos ((div_lt_one hden).2 (by linarith [hgain i]))
    filter_upwards [Ioo_mem_nhdsLT hc1] with δ hδ
    have hδ0 : 0 ≤ δ := (le_max_left _ _).trans hδ.1.le
    refine ⟨hδ0, fun s => ?_⟩
    have hdev : u i (update a i s) ≤ M := (abs_le.1 (hM i _)).2
    have hratio : (M - u i a) / (M - u i e) < δ := (le_max_right _ _).trans_lt hδ.1
    rw [div_lt_iff₀ hden] at hratio
    nlinarith [hδ.2]
  have hall := (eventually_all.2 hev).and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))
  filter_upwards [hall] with δ hδ
  refine ⟨hδ.2.1.le, grimTrigger_isSPE hδ.2.1.le hδ.2.2 hM he fun i => (hδ.1 i).2⟩

end Grim

/-! ### Witness: cooperation in the repeated prisoners' dilemma -/

/-- In the repeated prisoners' dilemma, grim trigger supporting mutual silence is subgame
perfect for every `δ ∈ [1/5, 1)`: the one-shot gain from confessing is `1`, the punishment
loss is `4`. -/
example {δ : ℝ} (hδ : 1 / 5 ≤ δ) (hδ1 : δ < 1) :
    IsRepeatedSPE pdPayoff δ (grimTrigger (fun _ => false) (fun _ => true)) := by
  have hNash : IsNash pdPayoff (fun _ : Bool => true) := by
    intro i t; cases i <;> cases t <;> simp [pdPayoff, update] <;> norm_num
  refine grimTrigger_isSPE (M := 10) (by linarith) hδ1 (fun i b => ?_) hNash fun i s => ?_
  · simp only [pdPayoff]
    split <;> norm_num
  · cases i <;> cases s <;> simp [pdPayoff, update] <;> nlinarith

end Econ
