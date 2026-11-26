/-
# The Nash folk theorem with minmax punishments

The pure-action, pure-minmax special case of the Nash folk theorem of Fudenberg–Tirole (1991),
Thm. 5.1 and Fudenberg–Maskin (1986), Thm. 1. Setting of `Games/Repeated.lean`: perfect
monitoring of pure action profiles, common discount factor `δ ∈ [0, 1)`.

The **minmax trigger** strategy profile supporting `a` plays `a` as long as everybody has done so.
After the first period in which the profile differs from `a` in exactly one player `i`'s action,
the other players play their part of a punishment profile `p i` forever (holding `i` down to at
most `v i`). If several players deviated at once, play continues with `a` (this never happens
when only one player deviates, which is all a Nash equilibrium checks).

* `minmaxTrigger_isNash`: the minmax trigger profile is a **Nash equilibrium** of the repeated
  game whenever no player gains from deviating once and then being held to `v i` forever:
  `(1 − δ) uᵢ(sᵢ, a₋ᵢ) + δ vᵢ ≤ uᵢ(a)`. Deviations to all repeated-game strategies are checked.
* `minmax_folk`: if `uᵢ(a) > vᵢ` for every player, this holds for all `δ` close to `1`.
* `nash_folk_pureMinmax`: **Nash folk theorem for pure stationary target profiles** in finite
  stage games: every pure profile that gives each player strictly more than her **pure-strategy
  minmax value**
  `min_{b₋ᵢ} max_{sᵢ} uᵢ(sᵢ, b₋ᵢ)` is the outcome path of a Nash equilibrium of the repeated game
  for all `δ` close to `1`.

Not formalized: subgame perfection with minmax punishments (the perfect folk theorem of
Fudenberg–Maskin, which needs rewards for punishers and full dimensionality); the mixed-strategy
minmax (weakly lower than the pure one, so Fudenberg–Tirole Thm. 5.1 covers more payoffs);
and payoff vectors that are not stage payoffs of a pure profile (these need non-stationary
paths or a randomization device).
-/
module

public import EconLean.Games.Repeated
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Filter.Finite

@[expose] public section

namespace Econ

open Function Filter Topology Finset

variable {I : Type*} [DecidableEq I] {S : I → Type*}

/-- **Nash equilibrium of the repeated game** with discount factor `δ ∈ [0, 1)`: from the
initial (empty) history, no player gains by switching to any other repeated-game strategy.
As with `IsRepeatedSPE`, `discPayoff` uses `tsum`, so this is meaningful for bounded stage
payoffs, which every theorem below assumes. -/
def IsRepeatedNash (u : I → (∀ j, S j) → ℝ) (δ : ℝ) (σ : RepeatedProfile S) : Prop :=
  0 ≤ δ ∧ δ < 1 ∧ ∀ (i : I) (τ : List (∀ j, S j) → S i),
    discPayoff u δ (update σ i τ) [] i ≤ discPayoff u δ σ [] i

section Minmax

open Classical

/-- The earliest profile in the history (most recent first) that differs from `a`, if any. -/
noncomputable def firstDev (a : ∀ j, S j) : List (∀ j, S j) → Option (∀ j, S j)
  | [] => none
  | b :: h => (firstDev a h).or (if b = a then none else some b)

/-- **Minmax trigger**: play `a` until the first deviation; if it was a unilateral deviation by
player `i`, everybody plays the punishment profile `p i` forever after. -/
noncomputable def minmaxTrigger (a : ∀ j, S j) (p : I → ∀ j, S j) : RepeatedProfile S :=
  fun j h => match firstDev a h with
    | none => a j
    | some b => if hb : ∃ i, ∀ k, k ≠ i → b k = a k then p hb.choose j else a j

variable {a : ∀ j, S j} {p : I → ∀ j, S j}

omit [DecidableEq I] in
lemma firstDev_cons (b : ∀ j, S j) (h : List (∀ j, S j)) :
    firstDev a (b :: h) = (firstDev a h).or (if b = a then none else some b) := rfl

omit [DecidableEq I] in
lemma minmaxTrigger_none {h : List (∀ j, S j)} (hh : firstDev a h = none) (j : I) :
    minmaxTrigger a p j h = a j := by
  simp only [minmaxTrigger, hh]

omit [DecidableEq I] in
/-- After a unilateral deviation by `i`, everybody plays `p i`. -/
lemma minmaxTrigger_some {h : List (∀ j, S j)} {b : ∀ j, S j} (hh : firstDev a h = some b)
    (hba : b ≠ a) {i : I} (hi : ∀ k, k ≠ i → b k = a k) (j : I) :
    minmaxTrigger a p j h = p i j := by
  have hb : ∃ i, ∀ k, k ≠ i → b k = a k := ⟨i, hi⟩
  simp only [minmaxTrigger, hh, hb, ↓reduceDIte]
  congr
  by_contra hne
  apply hba
  funext k
  by_cases hk : k = i
  · subst hk; exact hb.choose_spec k (Ne.symm hne)
  · exact hi k hk

omit [DecidableEq I] in
lemma firstDev_ne {h : List (∀ j, S j)} {b : ∀ j, S j} (hh : firstDev a h = some b) : b ≠ a := by
  induction h with
  | nil => simp [firstDev] at hh
  | cons c h ih =>
    rw [firstDev_cons] at hh
    cases hf : firstDev a h with
    | some d => rw [hf] at hh; simp only [Option.some_or, Option.some.injEq] at hh; subst hh
                exact ih hf
    | none =>
      rw [hf] at hh
      by_cases hc : c = a
      · simp [hc] at hh
      · simp only [hc, ↓reduceIte, Option.none_or, Option.some.injEq] at hh; subst hh; exact hc

omit [DecidableEq I] in
/-- Along the equilibrium path nobody deviates: the path is `a` forever. -/
lemma minmaxTrigger_path (t : ℕ) : pathFrom (minmaxTrigger a p) [] t = a ∧
    firstDev a (histFrom (minmaxTrigger a p) [] t) = none := by
  induction t with
  | zero =>
    refine ⟨funext fun j => ?_, rfl⟩
    exact minmaxTrigger_none rfl j
  | succ t ih =>
    have hnone : firstDev a (histFrom (minmaxTrigger a p) [] (t + 1)) = none := by
      rw [histFrom_succ, firstDev_cons, ih.2, ih.1]; simp
    exact ⟨funext fun j => minmaxTrigger_none hnone j, hnone⟩

/-- **The minmax trigger profile is a Nash equilibrium of the repeated game** (the argument of
Fudenberg–Tirole Thm. 5.1). Suppose `p i` holds player `i` down to `v i`
(`uᵢ(sᵢ, (p i)₋ᵢ) ≤ vᵢ` for every `sᵢ`) and no player gains from deviating once and then
receiving `v i` forever. Then no player gains from switching to any repeated-game strategy. Stage
payoffs are bounded. -/
theorem minmaxTrigger_isNash {u : I → (∀ j, S j) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ i b, |u i b| ≤ M) {v : I → ℝ} (hpun : ∀ i (s : S i), u i (update (p i) i s) ≤ v i)
    (hdev : ∀ i (s : S i), (1 - δ) * u i (update a i s) + δ * v i ≤ u i a) :
    IsRepeatedNash u δ (minmaxTrigger a p) := by
  refine ⟨hδ0, hδ1, fun i τ => ?_⟩
  have hon : discPayoff u δ (minmaxTrigger a p) [] i = u i a := by
    simp only [discPayoff, fun t => (minmaxTrigger_path (p := p) (a := a) t).1]
    exact disc_const hδ0 hδ1 _
  rw [hon]
  set σ' := update (minmaxTrigger a p) i τ
  set H := histFrom σ' []
  -- the deviator's continuation value
  let W : ℕ → ℝ := fun t => if firstDev a (H t) = none then u i a else v i
  -- the only deviations on record are by `i`
  have hpath : ∀ t, pathFrom σ' [] t =
      update (fun j => minmaxTrigger a p j (H t)) i (τ (H t)) := by
    intro t; funext j
    by_cases hj : j = i
    · subst hj; simp [pathFrom, σ', H]
    · simp only [pathFrom, σ', H, update_of_ne hj]
  have hinv : ∀ t b, firstDev a (H t) = some b → ∀ k, k ≠ i → b k = a k := by
    intro t
    induction t with
    | zero => intro b hb; simp [H, histFrom, firstDev] at hb
    | succ t ih =>
      intro b hb k hk
      simp only [H] at hb ih
      rw [histFrom_succ, firstDev_cons] at hb
      cases hf : firstDev a (histFrom σ' [] t) with
      | some d =>
        rw [hf] at hb; simp only [Option.some_or, Option.some.injEq] at hb; subst hb
        exact ih d hf k hk
      | none =>
        rw [hf] at hb
        by_cases hc : pathFrom σ' [] t = a
        · simp [hc] at hb
        · simp only [hc, ↓reduceIte, Option.none_or, Option.some.injEq] at hb
          subst hb
          rw [hpath t, update_of_ne hk]
          exact minmaxTrigger_none hf k
  have hW : ∀ t, |W t| ≤ max |u i a| |v i| := by
    intro t; simp only [W]; split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hstep : ∀ t, (1 - δ) * u i (pathFrom σ' [] t) + δ * W (t + 1) ≤ W t := by
    intro t
    have hnext : H (t + 1) = pathFrom σ' [] t :: H t := histFrom_succ _ _ _
    cases hf : firstDev a (H t) with
    | none =>
      have hx : pathFrom σ' [] t = update a i (τ (H t)) := by
        rw [hpath t, show (fun j => minmaxTrigger a p j (H t)) = a from
          funext (minmaxTrigger_none hf)]
      by_cases hxa : pathFrom σ' [] t = a
      · have h1 : firstDev a (H (t + 1)) = none := by rw [hnext, firstDev_cons, hf]; simp [hxa]
        simp only [W, h1, hf, ↓reduceIte, hxa]; ring_nf; rfl
      · have h1 : firstDev a (H (t + 1)) = some (pathFrom σ' [] t) := by
          rw [hnext, firstDev_cons, hf]; simp [hxa]
        simp only [W, h1, hf, reduceCtorEq, ↓reduceIte]
        rw [hx]; exact hdev i _
    | some b =>
      have h1 : firstDev a (H (t + 1)) = some b := by rw [hnext, firstDev_cons, hf]; rfl
      have hx : pathFrom σ' [] t = update (p i) i (τ (H t)) := by
        rw [hpath t, show (fun j => minmaxTrigger a p j (H t)) = p i from
          funext (minmaxTrigger_some hf (firstDev_ne hf) (hinv t b hf))]
      simp only [W, h1, hf, reduceCtorEq, ↓reduceIte]
      rw [hx]
      have := hpun i (τ (H t))
      nlinarith
  have hfin := discPayoff_le_of_bellman hδ0 hδ1 (summable_disc hδ0 hδ1 fun t => hM i _) hW hstep
  have h0 : W 0 = u i a := by simp [W, H, histFrom, firstDev]
  rw [h0] at hfin
  exact hfin

/-- **Minmax folk theorem** (Nash version): with finitely many players and bounded stage
payoffs, if every player gets strictly more from `a` than the level `v i` to which `p i` holds
her, the minmax trigger profile is a Nash equilibrium for all `δ` close enough to `1`. -/
theorem minmax_folk [Finite I] {u : I → (∀ j, S j) → ℝ} {M : ℝ} (hM : ∀ i b, |u i b| ≤ M)
    {v : I → ℝ} (hpun : ∀ i (s : S i), u i (update (p i) i s) ≤ v i)
    (hgain : ∀ i, v i < u i a) :
    ∀ᶠ δ in 𝓝[<] (1 : ℝ), IsRepeatedNash u δ (minmaxTrigger a p) := by
  have hev : ∀ i, ∀ᶠ δ in 𝓝[<] (1 : ℝ), 0 ≤ δ ∧
      ∀ s : S i, (1 - δ) * u i (update a i s) + δ * v i ≤ u i a := by
    intro i
    have hMa : u i a ≤ M := (abs_le.1 (hM i a)).2
    have hden : 0 < M - v i := by linarith [hgain i]
    set c := max 0 ((M - u i a) / (M - v i))
    have hc1 : c < 1 := max_lt one_pos ((div_lt_one hden).2 (by linarith [hgain i]))
    filter_upwards [Ioo_mem_nhdsLT hc1] with δ hδ
    have hδ0 : 0 ≤ δ := (le_max_left _ _).trans hδ.1.le
    refine ⟨hδ0, fun s => ?_⟩
    have hdev : u i (update a i s) ≤ M := (abs_le.1 (hM i _)).2
    have hratio : (M - u i a) / (M - v i) < δ := (le_max_right _ _).trans_lt hδ.1
    rw [div_lt_iff₀ hden] at hratio
    nlinarith [hδ.2]
  have hall := (eventually_all.2 hev).and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))
  filter_upwards [hall] with δ hδ
  exact minmaxTrigger_isNash hδ.2.1.le hδ.2.2 hM hpun fun i => (hδ.1 i).2

end Minmax

/-! ### Pure-strategy minmax values in finite games -/

section Finite

variable [Fintype I] [∀ j, Fintype (S j)] [∀ j, Nonempty (S j)]

/-- Player `i`'s best stage payoff against the others' actions in `b`. -/
noncomputable def bestDevPayoff (u : I → (∀ j, S j) → ℝ) (i : I) (b : ∀ j, S j) : ℝ :=
  univ.sup' univ_nonempty fun s : S i => u i (update b i s)

/-- Player `i`'s **pure-strategy minmax value** `min_{b₋ᵢ} max_{sᵢ} uᵢ(sᵢ, b₋ᵢ)`. -/
noncomputable def pureMinmax (u : I → (∀ j, S j) → ℝ) (i : I) : ℝ :=
  univ.inf' univ_nonempty (bestDevPayoff u i)

/-- In any (pure) stage Nash equilibrium, each player gets at least her pure minmax value. -/
theorem pureMinmax_le_of_isNash {u : I → (∀ j, S j) → ℝ} {e : ∀ j, S j} (he : IsNash u e)
    (i : I) : pureMinmax u i ≤ u i e := by
  refine (inf'_le _ (mem_univ e)).trans (sup'_le _ _ fun s _ => he i s)

/-- **Nash folk theorem for pure stationary target profiles** (a pure-action special case of
Fudenberg–Tirole Thm. 5.1, with the pure minmax, which is weakly above the mixed one): in a
finite stage game,
if a pure profile `a` gives every player strictly more than her pure-strategy minmax value,
then for all `δ` close enough to `1` some Nash equilibrium of the repeated game plays `a` in
every period. -/
theorem nash_folk_pureMinmax {u : I → (∀ j, S j) → ℝ} {a : ∀ j, S j}
    (hgain : ∀ i, pureMinmax u i < u i a) :
    ∀ᶠ δ in 𝓝[<] (1 : ℝ), ∃ σ : RepeatedProfile S, IsRepeatedNash u δ σ ∧
      ∀ t, pathFrom σ [] t = a := by
  classical
  have hp : ∀ i, ∃ b ∈ (univ : Finset (∀ j, S j)), bestDevPayoff u i b = pureMinmax u i :=
    fun i => by
      obtain ⟨b, hb, h⟩ := exists_mem_eq_inf' (univ_nonempty (α := ∀ j, S j)) (bestDevPayoff u i)
      exact ⟨b, hb, h.symm⟩
  choose p _ hp using hp
  obtain ⟨M, hM⟩ : ∃ M, ∀ i b, |u i b| ≤ M :=
    ⟨∑ ib : I × (∀ j, S j), |u ib.1 ib.2|, fun i b =>
      single_le_sum (f := fun ib : I × (∀ j, S j) => |u ib.1 ib.2|) (fun _ _ => abs_nonneg _)
        (mem_univ (i, b))⟩
  have hpun : ∀ i (s : S i), u i (update (p i) i s) ≤ pureMinmax u i := fun i s => by
    rw [← hp i]; exact le_sup' (fun s : S i => u i (update (p i) i s)) (mem_univ s)
  filter_upwards [minmax_folk (a := a) hM hpun hgain] with δ hδ
  exact ⟨minmaxTrigger a p, hδ, fun t => (minmaxTrigger_path t).1⟩

end Finite

/-! ### Witness -/

/-- In the repeated prisoners' dilemma, the minmax trigger supporting mutual silence (punish by
confessing) is a Nash equilibrium at `δ = 1/2`. -/
example : IsRepeatedNash pdPayoff (1 / 2) (minmaxTrigger (fun _ => false) fun _ _ => true) := by
  refine minmaxTrigger_isNash (M := 10) (v := fun _ => -5) (by norm_num) (by norm_num)
    (fun i b => ?_) (fun i s => ?_) (fun i s => ?_)
  · simp only [pdPayoff]; split <;> norm_num
  · cases i <;> cases s <;> simp [pdPayoff, update] <;> norm_num
  · cases i <;> cases s <;> simp [pdPayoff, update] <;> norm_num

end Econ
