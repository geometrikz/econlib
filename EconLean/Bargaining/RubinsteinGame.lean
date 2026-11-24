/-
# The Rubinstein alternating-offers game: the unique subgame perfect equilibrium

Rubinstein (1982); Shaked and Sutton (1984); Osborne–Rubinstein, *Bargaining and Markets*,
Ch. 3; Osborne–Rubinstein, *A Course in Game Theory*, §7.2–7.3 (Prop. 122.1, here specialized
to exponential discounting). Two players divide a pie of size
`1`. Before an agreement, the history is the list of rejected offers. An offer is player 1's
share `x ∈ [0, 1]`. At a history of even length player 1 proposes and player 2 responds; at a
history of odd length player 2 proposes and player 1 responds. If the offer `x` is accepted at
period `t`, player 1 gets `δ₁ᵗ x` and player 2 gets `δ₂ᵗ (1 − x)`; perpetual disagreement gives
both `0`.

A (pure) strategy profile `BargProfile` assigns to every history the offer of the player who
proposes there, and to every history and offer the response of the player who responds there.
Payoffs from a node are measured in units of that node's period. A profile is a **subgame
perfect equilibrium** (`IsBargSPE`) if after every history, at proposal nodes and at response
nodes (after any offer), no player gains by switching to any other strategy of her own.

Main results:
* `stationary_isBargSPE`: the stationary profile in which each proposer offers the responder
  exactly the discounted value of proposing next period, and each responder accepts iff she gets
  at least that, is a subgame perfect equilibrium; player 1 gets `x* = (1 − δ₂)/(1 − δ₁δ₂)`.
  Its payoffs are `stationary_pay₁` and `stationary_pay₂`.
* `spePay_eq`: in every SPE the proposer's payoff after any history is `x*` (player 1) or `y*`
  (player 2). The proof derives the Shaked–Sutton inequalities from subgame perfection and
  applies `shaked_sutton_bounds`.
* `bargSPE_eq_stationary`: **Rubinstein's theorem.** Every SPE coincides with the stationary
  profile at every history (offers, and responses to every feasible offer).
* `bargSPE_unique`: hence player 1 offers `x*` at the start and player 2 accepts at once.

Strategies are pure; the extension of the theorem to behavioral strategies is not formalized. Discount factors are in `[0, 1)`; Rubinstein assumes `(0, 1)`, and the results
extend to `δᵢ = 0`.
-/
module

public import EconLean.Bargaining.Rubinstein
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace Econ

open Set

/-- A pure strategy profile of the alternating-offers game. `prop h` is the offer (player 1's
share) made at history `h`; `acc h x` says the responder at `h` accepts the offer `x`. -/
structure BargProfile where
  /-- The offer at each history. -/
  prop : List ℝ → ℝ
  /-- The response at each history to each offer. -/
  acc : List ℝ → ℝ → Prop
  prop_mem : ∀ h, prop h ∈ Icc (0 : ℝ) 1

namespace BargProfile

/-- The history after `k` further rejections, starting from `h`. -/
def path (σ : BargProfile) (h : List ℝ) : ℕ → List ℝ
  | 0 => h
  | k + 1 => σ.path h k ++ [σ.prop (σ.path h k)]

/-- Agreement is reached `k` periods after `h`. -/
def Agrees (σ : BargProfile) (h : List ℝ) (k : ℕ) : Prop :=
  σ.acc (σ.path h k) (σ.prop (σ.path h k))

open Classical in
/-- Payoff from history `h`, in units of the period of `h`, for discount factor `δ` and the
share function `share` (`id` for player 1, `1 − ·` for player 2). -/
noncomputable def payoff (σ : BargProfile) (δ : ℝ) (share : ℝ → ℝ) (h : List ℝ) : ℝ :=
  if hk : ∃ k, σ.Agrees h k then δ ^ Nat.find hk * share (σ.prop (σ.path h (Nat.find hk)))
  else 0

open Classical in
/-- Payoff at the response node after the offer `x` at history `h`. -/
noncomputable def respPayoff (σ : BargProfile) (δ : ℝ) (share : ℝ → ℝ) (h : List ℝ) (x : ℝ) :
    ℝ :=
  if σ.acc h x then share x else δ * σ.payoff δ share (h ++ [x])

lemma path_length (σ : BargProfile) (h : List ℝ) (k : ℕ) : (σ.path h k).length = h.length + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [path, ih, Nat.add_assoc]

lemma path_succ' (σ : BargProfile) (h : List ℝ) (k : ℕ) :
    σ.path h (k + 1) = σ.path (h ++ [σ.prop h]) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [path, ih, path]

/-- **One-step decomposition** of the payoff at a proposal node. -/
lemma payoff_eq_resp (σ : BargProfile) (δ : ℝ) (share : ℝ → ℝ) (h : List ℝ) :
    σ.payoff δ share h = σ.respPayoff δ share h (σ.prop h) := by
  classical
  unfold respPayoff
  by_cases h0 : σ.acc h (σ.prop h)
  · have hex : ∃ k, σ.Agrees h k := ⟨0, h0⟩
    have hfind : Nat.find hex = 0 := (Nat.find_eq_zero hex).2 h0
    simp only [payoff, hex, ↓reduceDIte, hfind, pow_zero, one_mul, h0, ↓reduceIte]
    rfl
  · simp only [h0, ↓reduceIte]
    have hiff : ∀ k, σ.Agrees h (k + 1) ↔ σ.Agrees (h ++ [σ.prop h]) k := fun k => by
      simp only [Agrees, path_succ']
    by_cases hex : ∃ k, σ.Agrees (h ++ [σ.prop h]) k
    · have hex' : ∃ k, σ.Agrees h k := ⟨_, (hiff _).2 hex.choose_spec⟩
      have hex1 : ∃ k, σ.Agrees h (k + 1) := ⟨_, (hiff _).2 hex.choose_spec⟩
      have hf := Nat.find_comp_succ hex' hex1 h0
      have hf' : Nat.find hex1 = Nat.find hex := by
        congr 1; exact funext fun k => propext (hiff k)
      simp only [payoff, hex, hex', ↓reduceDIte, hf, hf', pow_succ, path_succ']
      ring
    · have hex' : ¬ ∃ k, σ.Agrees h k := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => exact h0 hk
        | succ k => exact hex ⟨k, (hiff k).1 hk⟩
      simp only [payoff, hex, hex', ↓reduceDIte, mul_zero]

/-- The payoff from `h` depends only on the profile at histories at least as long as `h`. -/
lemma payoff_congr {σ τ : BargProfile} {n : ℕ}
    (hp : ∀ h : List ℝ, n ≤ h.length → τ.prop h = σ.prop h)
    (ha : ∀ h : List ℝ, n ≤ h.length → ∀ x, (τ.acc h x ↔ σ.acc h x)) (δ : ℝ) (share : ℝ → ℝ)
    {h : List ℝ} (hh : n ≤ h.length) : τ.payoff δ share h = σ.payoff δ share h := by
  classical
  have hpath : ∀ k, τ.path h k = σ.path h k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [path, path, ih, hp _ (by rw [path_length]; omega)]
  have hag : ∀ k, τ.Agrees h k ↔ σ.Agrees h k := fun k => by
    unfold Agrees
    rw [hpath, hp _ (by rw [path_length]; omega)]
    exact ha _ (by rw [path_length]; omega) _
  have hex : (∃ k, τ.Agrees h k) ↔ ∃ k, σ.Agrees h k := exists_congr hag
  unfold payoff
  by_cases he : ∃ k, σ.Agrees h k
  · have he' := hex.2 he
    have hf : Nat.find he' = Nat.find he := by congr 1; exact funext fun k => propext (hag k)
    simp only [he, he', ↓reduceDIte, hf, hpath]
    rw [hp _ (by rw [path_length]; omega)]
  · have he' : ¬ ∃ k, τ.Agrees h k := fun h' => he (hex.1 h')
    simp only [he, he', ↓reduceDIte]

/-- Upper bound on a payoff from bounds on what agreement at each delay can give. -/
lemma payoff_le_of {σ : BargProfile} {δ : ℝ} {share : ℝ → ℝ} {h : List ℝ} {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ k, σ.Agrees h k → δ ^ k * share (σ.prop (σ.path h k)) ≤ B) :
    σ.payoff δ share h ≤ B := by
  classical
  unfold payoff
  split_ifs with hk
  · exact hB _ (Nat.find_spec hk)
  · exact hB0

lemma payoff_nonneg (σ : BargProfile) {δ : ℝ} (hδ : 0 ≤ δ) {share : ℝ → ℝ}
    (hs : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ share x) (h : List ℝ) : 0 ≤ σ.payoff δ share h := by
  classical
  unfold payoff
  split_ifs with hk
  · exact mul_nonneg (pow_nonneg hδ _) (hs _ (σ.prop_mem _))
  · exact le_rfl

/-- Payoffs are nonnegative and add up to at most the pie. -/
lemma payoff_add_le (σ : BargProfile) {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ ≤ 1) (h₂ : 0 ≤ δ₂)
    (h₂' : δ₂ ≤ 1) (h : List ℝ) :
    σ.payoff δ₁ id h + σ.payoff δ₂ (fun x => 1 - x) h ≤ 1 := by
  classical
  unfold payoff
  split_ifs with hk
  · set k := Nat.find hk
    have hx := σ.prop_mem (σ.path h k)
    have a1 : δ₁ ^ k ≤ 1 := pow_le_one₀ h₁ h₁'
    have a2 : δ₂ ^ k ≤ 1 := pow_le_one₀ h₂ h₂'
    simp only [id]
    nlinarith [hx.1, hx.2, pow_nonneg h₁ k, pow_nonneg h₂ k]
  · norm_num

end BargProfile

open BargProfile

/-- Player 1's payoff from history `h`. -/
noncomputable abbrev pay₁ (σ : BargProfile) (δ₁ : ℝ) (h : List ℝ) : ℝ := σ.payoff δ₁ id h

/-- Player 2's payoff from history `h`. -/
noncomputable abbrev pay₂ (σ : BargProfile) (δ₂ : ℝ) (h : List ℝ) : ℝ :=
  σ.payoff δ₂ (fun x => 1 - x) h

/-- `τ` differs from `σ` only in player 1's choices: player 2's offers (odd histories) and
player 2's responses (even histories) are unchanged. -/
def IsDev₁ (τ σ : BargProfile) : Prop :=
  (∀ h : List ℝ, ¬ Even h.length → τ.prop h = σ.prop h) ∧
    ∀ h : List ℝ, Even h.length → ∀ x, (τ.acc h x ↔ σ.acc h x)

/-- `τ` differs from `σ` only in player 2's choices. -/
def IsDev₂ (τ σ : BargProfile) : Prop :=
  (∀ h : List ℝ, Even h.length → τ.prop h = σ.prop h) ∧
    ∀ h : List ℝ, ¬ Even h.length → ∀ x, (τ.acc h x ↔ σ.acc h x)

/-- **(Pure-strategy) subgame perfect equilibrium**: after every history, at the proposal node and
at every response node, neither player gains from any unilateral change of strategy. -/
def IsBargSPE (δ₁ δ₂ : ℝ) (σ : BargProfile) : Prop :=
  (∀ τ, IsDev₁ τ σ → ∀ h, pay₁ τ δ₁ h ≤ pay₁ σ δ₁ h ∧
      ∀ x ∈ Icc (0 : ℝ) 1, τ.respPayoff δ₁ id h x ≤ σ.respPayoff δ₁ id h x) ∧
    ∀ τ, IsDev₂ τ σ → ∀ h, pay₂ τ δ₂ h ≤ pay₂ σ δ₂ h ∧
      ∀ x ∈ Icc (0 : ℝ) 1, τ.respPayoff δ₂ (fun x => 1 - x) h x ≤
        σ.respPayoff δ₂ (fun x => 1 - x) h x

section Stationary

variable {δ₁ δ₂ : ℝ}

/-- The stationary profile: player 1 always offers `x*`, player 2 always offers player 1 the
share `δ₁ x*` (keeping `y* = 1 − δ₁ x*`); player 2 accepts iff her share is at least `δ₂ y*`,
player 1 accepts iff her share is at least `δ₁ x*`. -/
noncomputable def stationaryProfile (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1) :
    BargProfile where
  prop h := if Even h.length then rubinsteinShare δ₁ δ₂ else δ₁ * rubinsteinShare δ₁ δ₂
  acc h x := (Even h.length ∧ δ₂ * rubinsteinShare δ₂ δ₁ ≤ 1 - x) ∨
    (¬ Even h.length ∧ δ₁ * rubinsteinShare δ₁ δ₂ ≤ x)
  prop_mem h := by
    have hm := rubinsteinShare_mem h₁ h₁' h₂ h₂'
    split_ifs
    · exact ⟨hm.1.le, hm.2⟩
    · exact ⟨mul_nonneg h₁ hm.1.le, by nlinarith [hm.1, hm.2]⟩

variable (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)

include h₁ h₁' h₂' in
lemma stationary_eqs : rubinsteinShare δ₁ δ₂ = 1 - δ₂ * rubinsteinShare δ₂ δ₁ ∧
    rubinsteinShare δ₂ δ₁ = 1 - δ₁ * rubinsteinShare δ₁ δ₂ :=
  (rubinstein_stationary h₁ h₁' h₂' _ _).2 ⟨rfl, rfl⟩

lemma stationary_pay₁ (h : List ℝ) :
    pay₁ (stationaryProfile h₁ h₁' h₂ h₂') δ₁ h =
      if Even h.length then rubinsteinShare δ₁ δ₂ else δ₁ * rubinsteinShare δ₁ δ₂ := by
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  unfold pay₁
  rw [payoff_eq_resp, respPayoff]
  by_cases he : Even h.length
  · have hacc : (stationaryProfile h₁ h₁' h₂ h₂').acc h
        ((stationaryProfile h₁ h₁' h₂ h₂').prop h) := by
      left; refine ⟨he, ?_⟩; simp only [stationaryProfile, he, ↓reduceIte]; linarith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hacc)]
    simp only [id, stationaryProfile, he, ↓reduceIte]
  · have hacc : (stationaryProfile h₁ h₁' h₂ h₂').acc h
        ((stationaryProfile h₁ h₁' h₂ h₂').prop h) := by
      right; refine ⟨he, ?_⟩; simp only [stationaryProfile, he, ↓reduceIte, le_refl]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hacc)]
    simp only [id, stationaryProfile, he, ↓reduceIte]

lemma stationary_pay₂ (h : List ℝ) :
    pay₂ (stationaryProfile h₁ h₁' h₂ h₂') δ₂ h =
      if Even h.length then δ₂ * rubinsteinShare δ₂ δ₁ else rubinsteinShare δ₂ δ₁ := by
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  unfold pay₂
  rw [payoff_eq_resp, respPayoff]
  by_cases he : Even h.length
  · have hacc : (stationaryProfile h₁ h₁' h₂ h₂').acc h
        ((stationaryProfile h₁ h₁' h₂ h₂').prop h) := by
      left; refine ⟨he, ?_⟩; simp only [stationaryProfile, he, ↓reduceIte]; linarith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hacc)]
    simp only [stationaryProfile, he, ↓reduceIte]; linarith
  · have hacc : (stationaryProfile h₁ h₁' h₂ h₂').acc h
        ((stationaryProfile h₁ h₁' h₂ h₂').prop h) := by
      right; refine ⟨he, ?_⟩; simp only [stationaryProfile, he, ↓reduceIte, le_refl]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hacc)]
    simp only [stationaryProfile, he, ↓reduceIte]; linarith

/-- Against the stationary strategy of player 2, player 1 never gets more than the stationary
payoff. -/
lemma dev₁_pay_le {τ : BargProfile} (hτ : IsDev₁ τ (stationaryProfile h₁ h₁' h₂ h₂'))
    (h : List ℝ) :
    pay₁ τ δ₁ h ≤ if Even h.length then rubinsteinShare δ₁ δ₂ else δ₁ * rubinsteinShare δ₁ δ₂ := by
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  have hm := rubinsteinShare_mem h₁ h₁' h₂ h₂'
  set xs := rubinsteinShare δ₁ δ₂
  -- every accepted offer gives player 1 at most `x*`
  have hshare : ∀ k, τ.Agrees h k → τ.prop (τ.path h k) ≤ xs ∧
      (¬ Even (τ.path h k).length → τ.prop (τ.path h k) = δ₁ * xs) := by
    intro k hk
    set H := τ.path h k
    by_cases hE : Even H.length
    · have := (hτ.2 H hE _).1 hk
      rcases this with ⟨_, hle⟩ | ⟨hne, _⟩
      · exact ⟨by linarith, fun h' => absurd hE h'⟩
      · exact absurd hE hne
    · rw [hτ.1 H hE]
      simp only [stationaryProfile, hE, ↓reduceIte]
      exact ⟨by nlinarith [hm.1], fun _ => rfl⟩
  have hpos : 0 ≤ xs := hm.1.le
  split_ifs with he
  · refine payoff_le_of hpos fun k hk => ?_
    have := (hshare k hk).1
    calc δ₁ ^ k * id (τ.prop (τ.path h k)) ≤ 1 * xs := by
          simp only [id]
          exact mul_le_mul (pow_le_one₀ h₁ h₁'.le) this (τ.prop_mem _).1 zero_le_one
      _ = xs := one_mul xs
  · refine payoff_le_of (mul_nonneg h₁ hpos) fun k hk => ?_
    simp only [id]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [(hshare 0 hk).2 (by simpa [path] using he)]; simp
    · calc δ₁ ^ k * τ.prop (τ.path h k) ≤ δ₁ ^ 1 * xs :=
            mul_le_mul (pow_le_pow_of_le_one h₁ h₁'.le hk0) (hshare k hk).1 (τ.prop_mem _).1
              (pow_nonneg h₁ _)
        _ = δ₁ * xs := by rw [pow_one]

/-- Against the stationary strategy of player 1, player 2 never gets more than the stationary
payoff. -/
lemma dev₂_pay_le {τ : BargProfile} (hτ : IsDev₂ τ (stationaryProfile h₁ h₁' h₂ h₂'))
    (h : List ℝ) :
    pay₂ τ δ₂ h ≤ if Even h.length then δ₂ * rubinsteinShare δ₂ δ₁ else rubinsteinShare δ₂ δ₁ := by
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  have hm := rubinsteinShare_mem h₂ h₂' h₁ h₁'
  set ys := rubinsteinShare δ₂ δ₁
  have hshare : ∀ k, τ.Agrees h k → 1 - τ.prop (τ.path h k) ≤ ys ∧
      (Even (τ.path h k).length → 1 - τ.prop (τ.path h k) = δ₂ * ys) := by
    intro k hk
    set H := τ.path h k
    by_cases hE : Even H.length
    · rw [hτ.1 H hE]
      simp only [stationaryProfile, hE, ↓reduceIte]
      exact ⟨by nlinarith [hm.1], fun _ => by linarith⟩
    · have := (hτ.2 H hE _).1 hk
      rcases this with ⟨he', _⟩ | ⟨_, hle⟩
      · exact absurd he' hE
      · exact ⟨by linarith, fun h' => absurd h' hE⟩
  have hpos : 0 ≤ ys := hm.1.le
  have hnn : ∀ k, 0 ≤ 1 - τ.prop (τ.path h k) := fun k => by linarith [(τ.prop_mem (τ.path h k)).2]
  split_ifs with he
  · refine payoff_le_of (mul_nonneg h₂ hpos) fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [(hshare 0 hk).2 (by simpa [path] using he)]; simp
    · calc δ₂ ^ k * (1 - τ.prop (τ.path h k)) ≤ δ₂ ^ 1 * ys :=
            mul_le_mul (pow_le_pow_of_le_one h₂ h₂'.le hk0) (hshare k hk).1 (hnn k)
              (pow_nonneg h₂ _)
        _ = δ₂ * ys := by rw [pow_one]
  · refine payoff_le_of hpos fun k hk => ?_
    calc δ₂ ^ k * (1 - τ.prop (τ.path h k)) ≤ 1 * ys :=
          mul_le_mul (pow_le_one₀ h₂ h₂'.le) (hshare k hk).1 (hnn k) zero_le_one
      _ = ys := one_mul ys

/-- **The stationary profile is a subgame perfect equilibrium** (Rubinstein 1982). Its payoffs
are given by `stationary_pay₁` and `stationary_pay₂`. -/
theorem stationary_isBargSPE : IsBargSPE δ₁ δ₂ (stationaryProfile h₁ h₁' h₂ h₂') := by
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  have hm := rubinsteinShare_mem h₁ h₁' h₂ h₂'
  have hm' := rubinsteinShare_mem h₂ h₂' h₁ h₁'
  refine ⟨fun τ hτ h => ⟨?_, fun x hx => ?_⟩, fun τ hτ h => ⟨?_, fun x hx => ?_⟩⟩
  · rw [stationary_pay₁]; exact dev₁_pay_le h₁ h₁' h₂ h₂' hτ h
  · have hnext := dev₁_pay_le h₁ h₁' h₂ h₂' hτ (h ++ [x])
    have hnext' := stationary_pay₁ h₁ h₁' h₂ h₂' (h ++ [x])
    have hlen : (h ++ [x]).length = h.length + 1 := by simp
    simp only [hlen, Nat.even_add_one] at hnext hnext'
    unfold pay₁ at hnext hnext'
    unfold respPayoff
    by_cases he : Even h.length
    · have hiff := hτ.2 h he x
      simp only [he, not_true_eq_false, ↓reduceIte] at hnext hnext'
      by_cases ha : (stationaryProfile h₁ h₁' h₂ h₂').acc h x
      · simp only [hiff.2 ha, ha, ↓reduceIte, le_refl]
      · have ha' : ¬ τ.acc h x := fun h' => ha (hiff.1 h')
        simp only [ha, ha', ↓reduceIte]
        rw [hnext']; exact mul_le_mul_of_nonneg_left hnext h₁
    · simp only [he, not_false_eq_true, ↓reduceIte] at hnext hnext'
      have hσacc : (stationaryProfile h₁ h₁' h₂ h₂').acc h x ↔
          δ₁ * rubinsteinShare δ₁ δ₂ ≤ x := by
        simp only [stationaryProfile, he, false_and, false_or, not_false_eq_true, true_and]
      by_cases hσ : δ₁ * rubinsteinShare δ₁ δ₂ ≤ x
      · simp only [hσacc.2 hσ, ↓reduceIte, id]
        split_ifs
        · exact le_rfl
        · nlinarith
      · have hσn : ¬ (stationaryProfile h₁ h₁' h₂ h₂').acc h x := fun h' => hσ (hσacc.1 h')
        simp only [hσn, ↓reduceIte, id]
        rw [hnext']
        split_ifs
        · push Not at hσ; linarith
        · exact mul_le_mul_of_nonneg_left hnext h₁
  · rw [stationary_pay₂]; exact dev₂_pay_le h₁ h₁' h₂ h₂' hτ h
  · have hnext := dev₂_pay_le h₁ h₁' h₂ h₂' hτ (h ++ [x])
    have hnext' := stationary_pay₂ h₁ h₁' h₂ h₂' (h ++ [x])
    have hlen : (h ++ [x]).length = h.length + 1 := by simp
    simp only [hlen, Nat.even_add_one] at hnext hnext'
    unfold pay₂ at hnext hnext'
    unfold respPayoff
    by_cases he : Even h.length
    · simp only [he, not_true_eq_false, ↓reduceIte] at hnext hnext'
      have hσacc : (stationaryProfile h₁ h₁' h₂ h₂').acc h x ↔
          δ₂ * rubinsteinShare δ₂ δ₁ ≤ 1 - x := by
        simp only [stationaryProfile, he, true_and, not_true_eq_false, false_and, or_false]
      by_cases hσ : δ₂ * rubinsteinShare δ₂ δ₁ ≤ 1 - x
      · simp only [hσacc.2 hσ, ↓reduceIte]
        split_ifs
        · exact le_rfl
        · nlinarith
      · have hσn : ¬ (stationaryProfile h₁ h₁' h₂ h₂').acc h x := fun h' => hσ (hσacc.1 h')
        simp only [hσn, ↓reduceIte]
        rw [hnext']
        split_ifs
        · push Not at hσ; linarith
        · exact mul_le_mul_of_nonneg_left hnext h₂
    · have hiff := hτ.2 h he x
      simp only [he, not_false_eq_true, ↓reduceIte] at hnext hnext'
      by_cases ha : (stationaryProfile h₁ h₁' h₂ h₂').acc h x
      · simp only [hiff.2 ha, ha, ↓reduceIte, le_refl]
      · have ha' : ¬ τ.acc h x := fun h' => ha (hiff.1 h')
        simp only [ha, ha', ↓reduceIte]
        rw [hnext']; exact mul_le_mul_of_nonneg_left hnext h₂

end Stationary

section Unique

namespace BargProfile

open Classical in
/-- Change the response at the single node `(h₀, x₀)` to `b`. -/
noncomputable def setAcc (σ : BargProfile) (h₀ : List ℝ) (x₀ : ℝ) (b : Prop) : BargProfile where
  prop := σ.prop
  acc h x := if h = h₀ ∧ x = x₀ then b else σ.acc h x
  prop_mem := σ.prop_mem

open Classical in
/-- Change the offer at the single history `h₀` to `x₀`. -/
noncomputable def setProp (σ : BargProfile) (h₀ : List ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) :
    BargProfile where
  prop h := if h = h₀ then x₀ else σ.prop h
  acc := σ.acc
  prop_mem h := by
    split_ifs
    · exact hx₀
    · exact σ.prop_mem h

lemma setAcc_payoff_next (σ : BargProfile) (h₀ : List ℝ) (x₀ : ℝ) (b : Prop) (δ : ℝ)
    (share : ℝ → ℝ) (x : ℝ) :
    (σ.setAcc h₀ x₀ b).payoff δ share (h₀ ++ [x]) = σ.payoff δ share (h₀ ++ [x]) := by
  classical
  refine payoff_congr (τ := σ.setAcc h₀ x₀ b) (σ := σ) (n := h₀.length + 1) (h := h₀ ++ [x]) (fun _ _ => rfl) (fun h hh y => ?_) δ share
    (by simp)
  have : h ≠ h₀ := fun e => by rw [e] at hh; omega
  simp only [setAcc, this, false_and, ↓reduceIte]

lemma setAcc_acc (σ : BargProfile) (h₀ : List ℝ) (x₀ : ℝ) (b : Prop) :
    (σ.setAcc h₀ x₀ b).acc h₀ x₀ ↔ b := by
  classical
  simp only [setAcc, and_self, ↓reduceIte]

lemma setProp_payoff (σ : BargProfile) (h₀ : List ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (share : ℝ → ℝ) (hacc : σ.acc h₀ x₀) :
    (σ.setProp h₀ x₀ hx₀).payoff δ share h₀ = share x₀ := by
  classical
  rw [payoff_eq_resp, respPayoff]
  have hp : (σ.setProp h₀ x₀ hx₀).prop h₀ = x₀ := by simp only [setProp, ↓reduceIte]
  have ha : (σ.setProp h₀ x₀ hx₀).acc h₀ x₀ := hacc
  rw [hp, ite_eq_left_of_eq_true _ _ (eq_true ha)]

end BargProfile

open BargProfile

variable {δ₁ δ₂ : ℝ}

lemma setAcc_isDev₂ (σ : BargProfile) {h₀ : List ℝ} (he : Even h₀.length) (x₀ : ℝ) (b : Prop) :
    IsDev₂ (σ.setAcc h₀ x₀ b) σ := by
  classical
  refine ⟨fun _ _ => rfl, fun h hh x => ?_⟩
  have : h ≠ h₀ := fun e => hh (e ▸ he)
  simp only [setAcc, this, false_and, ↓reduceIte]

lemma setAcc_isDev₁ (σ : BargProfile) {h₀ : List ℝ} (he : ¬ Even h₀.length) (x₀ : ℝ) (b : Prop) :
    IsDev₁ (σ.setAcc h₀ x₀ b) σ := by
  classical
  refine ⟨fun _ _ => rfl, fun h hh x => ?_⟩
  have : h ≠ h₀ := fun e => he (e ▸ hh)
  simp only [setAcc, this, false_and, ↓reduceIte]

lemma setProp_isDev₁ (σ : BargProfile) {h₀ : List ℝ} (he : Even h₀.length) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) : IsDev₁ (σ.setProp h₀ x₀ hx₀) σ := by
  classical
  refine ⟨fun h hh => ?_, fun _ _ _ => Iff.rfl⟩
  have : h ≠ h₀ := fun e => hh (e ▸ he)
  simp only [setProp, this, ↓reduceIte]

lemma setProp_isDev₂ (σ : BargProfile) {h₀ : List ℝ} (he : ¬ Even h₀.length) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) : IsDev₂ (σ.setProp h₀ x₀ hx₀) σ := by
  classical
  refine ⟨fun h hh => ?_, fun _ _ _ => Iff.rfl⟩
  have : h ≠ h₀ := fun e => he (e ▸ hh)
  simp only [setProp, this, ↓reduceIte]

/-- In an SPE, player 2 (responding at an even history) accepts any offer that leaves her more
than the discounted value of rejecting. -/
lemma spe_acc₂ {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) {h : List ℝ} (he : Even h.length)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hgt : δ₂ * pay₂ σ δ₂ (h ++ [x]) < 1 - x) : σ.acc h x := by
  classical
  by_contra hn
  have := (hσ.2 _ (setAcc_isDev₂ σ he x True) h).2 x hx
  unfold respPayoff at this
  rw [ite_eq_left_of_eq_true _ _ (eq_true ((setAcc_acc σ h x True).2 trivial)),
    ite_eq_right_of_eq_false _ _ (eq_false hn)] at this
  linarith

/-- In an SPE, player 2 accepts only offers worth at least the discounted value of rejecting. -/
lemma spe_acc₂_le {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) {h : List ℝ} (he : Even h.length)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : σ.acc h x) : δ₂ * pay₂ σ δ₂ (h ++ [x]) ≤ 1 - x := by
  classical
  have := (hσ.2 _ (setAcc_isDev₂ σ he x False) h).2 x hx
  unfold respPayoff at this
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => (setAcc_acc σ h x False).1 h'),
    ite_eq_left_of_eq_true _ _ (eq_true ha), setAcc_payoff_next] at this
  exact this

/-- In an SPE, player 1 (responding at an odd history) accepts any offer worth more than the
discounted value of rejecting. -/
lemma spe_acc₁ {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) {h : List ℝ} (he : ¬ Even h.length)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hgt : δ₁ * pay₁ σ δ₁ (h ++ [x]) < x) : σ.acc h x := by
  classical
  by_contra hn
  have := (hσ.1 _ (setAcc_isDev₁ σ he x True) h).2 x hx
  unfold respPayoff at this
  rw [ite_eq_left_of_eq_true _ _ (eq_true ((setAcc_acc σ h x True).2 trivial)),
    ite_eq_right_of_eq_false _ _ (eq_false hn)] at this
  simp only [id] at this
  linarith

lemma spe_acc₁_le {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) {h : List ℝ} (he : ¬ Even h.length)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : σ.acc h x) : δ₁ * pay₁ σ δ₁ (h ++ [x]) ≤ x := by
  classical
  have := (hσ.1 _ (setAcc_isDev₁ σ he x False) h).2 x hx
  unfold respPayoff at this
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => (setAcc_acc σ h x False).1 h'),
    ite_eq_left_of_eq_true _ _ (eq_true ha), setAcc_payoff_next] at this
  exact this

/-- In an SPE, the proposer gets at least what any accepted offer would give her. -/
lemma spe_prop₁ {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) {h : List ℝ} (he : Even h.length)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : σ.acc h x) : x ≤ pay₁ σ δ₁ h := by
  have := (hσ.1 _ (setProp_isDev₁ σ he hx) h).1
  unfold pay₁ at this
  rwa [setProp_payoff σ h x hx δ₁ id ha] at this

lemma spe_prop₂ {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) {h : List ℝ} (he : ¬ Even h.length)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : σ.acc h x) : 1 - x ≤ pay₂ σ δ₂ h := by
  have := (hσ.2 _ (setProp_isDev₂ σ he hx) h).1
  unfold pay₂ at this
  rwa [setProp_payoff σ h x hx δ₂ _ ha] at this

/-- Player 1's SPE payoffs in subgames where she proposes. -/
def spePay₁ (δ₁ δ₂ : ℝ) : Set ℝ :=
  {v | ∃ σ h, IsBargSPE δ₁ δ₂ σ ∧ Even (List.length h) ∧ v = pay₁ σ δ₁ h}

/-- Player 2's SPE payoffs in subgames where she proposes. -/
def spePay₂ (δ₁ δ₂ : ℝ) : Set ℝ :=
  {v | ∃ σ h, IsBargSPE δ₁ δ₂ σ ∧ ¬ Even (List.length h) ∧ v = pay₂ σ δ₂ h}

variable (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
include h₁ h₁' h₂ h₂'

lemma pay_bounds (σ : BargProfile) (h : List ℝ) :
    0 ≤ pay₁ σ δ₁ h ∧ 0 ≤ pay₂ σ δ₂ h ∧ pay₁ σ δ₁ h + pay₂ σ δ₂ h ≤ 1 :=
  ⟨σ.payoff_nonneg h₁ (fun x hx => hx.1) h, σ.payoff_nonneg h₂ (fun x hx => by linarith [hx.2]) h,
    σ.payoff_add_le h₁ h₁'.le h₂ h₂'.le h⟩

lemma spePay_props :
    (spePay₁ δ₁ δ₂).Nonempty ∧ (spePay₂ δ₁ δ₂).Nonempty ∧
      (∀ v ∈ spePay₁ δ₁ δ₂, 0 ≤ v ∧ v ≤ 1) ∧ ∀ v ∈ spePay₂ δ₁ δ₂, 0 ≤ v ∧ v ≤ 1 := by
  refine ⟨⟨_, stationaryProfile h₁ h₁' h₂ h₂', [], stationary_isBargSPE h₁ h₁' h₂ h₂',
      by simp, rfl⟩,
    ⟨_, stationaryProfile h₁ h₁' h₂ h₂', [0], stationary_isBargSPE h₁ h₁' h₂ h₂', by simp, rfl⟩,
    ?_, ?_⟩
  · rintro v ⟨σ, h, -, -, rfl⟩
    have := pay_bounds h₁ h₁' h₂ h₂' σ h
    exact ⟨this.1, by linarith [this.2.1, this.2.2]⟩
  · rintro v ⟨σ, h, -, -, rfl⟩
    have := pay_bounds h₁ h₁' h₂ h₂' σ h
    exact ⟨this.2.1, by linarith [this.1, this.2.2]⟩

/-- **SPE payoffs are unique** (Shaked–Sutton 1984). In every pure-strategy subgame perfect
equilibrium, player 1's payoff after any history where she proposes is `x*`, and player 2's
payoff after any history where she proposes is `y*`. The proof derives the Shaked–Sutton
inequalities for the sup and inf of these payoff sets from subgame perfection. -/
theorem spePay_eq :
    (∀ v ∈ spePay₁ δ₁ δ₂, v = rubinsteinShare δ₁ δ₂) ∧
      ∀ v ∈ spePay₂ δ₁ δ₂, v = rubinsteinShare δ₂ δ₁ := by
  obtain ⟨ne1, ne2, b1, b2⟩ := spePay_props h₁ h₁' h₂ h₂'
  have bdd1 : BddAbove (spePay₁ δ₁ δ₂) := ⟨1, fun v hv => (b1 v hv).2⟩
  have bdd1' : BddBelow (spePay₁ δ₁ δ₂) := ⟨0, fun v hv => (b1 v hv).1⟩
  have bdd2 : BddAbove (spePay₂ δ₁ δ₂) := ⟨1, fun v hv => (b2 v hv).2⟩
  have bdd2' : BddBelow (spePay₂ δ₁ δ₂) := ⟨0, fun v hv => (b2 v hv).1⟩
  set M₁ := sSup (spePay₁ δ₁ δ₂)
  set m₁ := sInf (spePay₁ δ₁ δ₂)
  set M₂ := sSup (spePay₂ δ₁ δ₂)
  set m₂ := sInf (spePay₂ δ₁ δ₂)
  have hm₁0 : 0 ≤ m₁ := le_csInf ne1 fun v hv => (b1 v hv).1
  have hm₂0 : 0 ≤ m₂ := le_csInf ne2 fun v hv => (b2 v hv).1
  have hM₁1 : M₁ ≤ 1 := csSup_le ne1 fun v hv => (b1 v hv).2
  have hM₂1 : M₂ ≤ 1 := csSup_le ne2 fun v hv => (b2 v hv).2
  have mM₁ : m₁ ≤ M₁ := by
    obtain ⟨v, hv⟩ := ne1; exact (csInf_le bdd1' hv).trans (le_csSup bdd1 hv)
  have mM₂ : m₂ ≤ M₂ := by
    obtain ⟨v, hv⟩ := ne2; exact (csInf_le bdd2' hv).trans (le_csSup bdd2 hv)
  have hM₂0 : 0 ≤ M₂ := hm₂0.trans mM₂
  have hM₁0 : 0 ≤ M₁ := hm₁0.trans mM₁
  have in1 : ∀ τ h, IsBargSPE δ₁ δ₂ τ → Even (List.length h) → pay₁ τ δ₁ h ∈ spePay₁ δ₁ δ₂ :=
    fun τ h hτ he => ⟨τ, h, hτ, he, rfl⟩
  have in2 : ∀ τ h, IsBargSPE δ₁ δ₂ τ → ¬ Even (List.length h) →
      pay₂ τ δ₂ h ∈ spePay₂ δ₁ δ₂ := fun τ h hτ he => ⟨τ, h, hτ, he, rfl⟩
  have odd_next : ∀ h : List ℝ, ∀ x : ℝ, Even h.length → ¬ Even (h ++ [x]).length := fun h x he => by
    simp [Nat.even_add_one, he]
  have even_next : ∀ h : List ℝ, ∀ x : ℝ, ¬ Even h.length → Even (h ++ [x]).length := fun h x he => by
    simp [Nat.even_add_one, he]
  -- (i) `m₁ ≥ 1 − δ₂ M₂`
  have i1 : 1 - δ₂ * M₂ ≤ m₁ := by
    refine le_csInf ne1 ?_
    rintro v ⟨τ, h, hτ, he, rfl⟩
    by_contra hlt
    push Not at hlt
    have hv0 := (pay_bounds h₁ h₁' h₂ h₂' τ h).1
    have hv1 : pay₁ τ δ₁ h ≤ 1 := by
      have := pay_bounds h₁ h₁' h₂ h₂' τ h; linarith [this.2.1, this.2.2]
    have hc : δ₂ * M₂ ≤ 1 := by nlinarith
    have hc0 : 0 ≤ δ₂ * M₂ := mul_nonneg h₂ hM₂0
    set x := (pay₁ τ δ₁ h + (1 - δ₂ * M₂)) / 2 with hxdef
    have hx : x ∈ Icc (0 : ℝ) 1 := ⟨by rw [hxdef]; linarith, by rw [hxdef]; linarith⟩
    have hacc : τ.acc h x := spe_acc₂ hτ he hx (by
      have := mul_le_mul_of_nonneg_left (le_csSup bdd2 (in2 τ _ hτ (odd_next h x he))) h₂
      have hxlt : x < 1 - δ₂ * M₂ := by rw [hxdef]; linarith
      linarith)
    have := spe_prop₁ hτ he hx hacc
    have hxgt : pay₁ τ δ₁ h < x := by rw [hxdef]; linarith
    linarith
  -- (ii) `M₁ ≤ 1 − δ₂ m₂`
  have i2 : M₁ ≤ 1 - δ₂ * m₂ := by
    refine csSup_le ne1 ?_
    rintro v ⟨τ, h, hτ, he, rfl⟩
    have hx := τ.prop_mem h
    have hnext := csInf_le bdd2' (in2 τ _ hτ (odd_next h (τ.prop h) he))
    unfold pay₁
    rw [payoff_eq_resp, respPayoff]
    split_ifs with ha
    · have := spe_acc₂_le hτ he hx ha
      simp only [id]
      nlinarith
    · have hb := pay_bounds h₁ h₁' h₂ h₂' τ (h ++ [τ.prop h])
      simp only [pay₁, pay₂] at hb hnext
      nlinarith
  -- (iii) `m₂ ≥ 1 − δ₁ M₁`
  have i3 : 1 - δ₁ * M₁ ≤ m₂ := by
    refine le_csInf ne2 ?_
    rintro v ⟨τ, h, hτ, he, rfl⟩
    by_contra hlt
    push Not at hlt
    have hv0 := (pay_bounds h₁ h₁' h₂ h₂' τ h).2.1
    have hv1 : pay₂ τ δ₂ h ≤ 1 := by
      have := pay_bounds h₁ h₁' h₂ h₂' τ h; linarith [this.1, this.2.2]
    have hc : δ₁ * M₁ ≤ 1 := by nlinarith
    have hc0 : 0 ≤ δ₁ * M₁ := mul_nonneg h₁ hM₁0
    set y := (pay₂ τ δ₂ h + (1 - δ₁ * M₁)) / 2 with hydef
    have hx : 1 - y ∈ Icc (0 : ℝ) 1 := ⟨by rw [hydef]; linarith, by rw [hydef]; linarith⟩
    have hacc : τ.acc h (1 - y) := spe_acc₁ hτ he hx (by
      have := mul_le_mul_of_nonneg_left (le_csSup bdd1 (in1 τ _ hτ (even_next h (1 - y) he))) h₁
      have hylt : y < 1 - δ₁ * M₁ := by rw [hydef]; linarith
      linarith)
    have := spe_prop₂ hτ he hx hacc
    have hygt : pay₂ τ δ₂ h < y := by rw [hydef]; linarith
    linarith
  -- (iv) `M₂ ≤ 1 − δ₁ m₁`
  have i4 : M₂ ≤ 1 - δ₁ * m₁ := by
    refine csSup_le ne2 ?_
    rintro v ⟨τ, h, hτ, he, rfl⟩
    have hx := τ.prop_mem h
    have hnext := csInf_le bdd1' (in1 τ _ hτ (even_next h (τ.prop h) he))
    unfold pay₂
    rw [payoff_eq_resp, respPayoff]
    split_ifs with ha
    · have := spe_acc₁_le hτ he hx ha
      nlinarith
    · have hb := pay_bounds h₁ h₁' h₂ h₂' τ (h ++ [τ.prop h])
      simp only [pay₁, pay₂] at hb hnext
      nlinarith
  obtain ⟨eM₁, em₁, eM₂, em₂⟩ := shaked_sutton_bounds h₁ h₁' h₂ h₂' i1 i2 i3 i4 mM₁ mM₂
  exact ⟨fun v hv => le_antisymm (eM₁ ▸ le_csSup bdd1 hv) (em₁ ▸ csInf_le bdd1' hv),
    fun v hv => le_antisymm (eM₂ ▸ le_csSup bdd2 hv) (em₂ ▸ csInf_le bdd2' hv)⟩

/-- **Rubinstein's theorem** (Rubinstein 1982; Osborne–Rubinstein, *A Course in Game Theory*,
Prop. 122.1, specialized to exponential discounting and pure strategies). Every pure-strategy
subgame perfect equilibrium **is** the stationary profile: after every history the proposer
makes the stationary offer, and the responder accepts an offer exactly when the stationary
strategy does. -/
theorem bargSPE_eq_stationary {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) (h : List ℝ) :
    σ.prop h = (stationaryProfile h₁ h₁' h₂ h₂').prop h ∧
      ∀ x ∈ Icc (0 : ℝ) 1, (σ.acc h x ↔ (stationaryProfile h₁ h₁' h₂ h₂').acc h x) := by
  obtain ⟨E1, E2⟩ := spePay_eq h₁ h₁' h₂ h₂'
  have hm := rubinsteinShare_mem h₁ h₁' h₂ h₂'
  have hm' := rubinsteinShare_mem h₂ h₂' h₁ h₁'
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  have v1 : ∀ h : List ℝ, Even h.length → pay₁ σ δ₁ h = rubinsteinShare δ₁ δ₂ :=
    fun h he => E1 _ ⟨σ, h, hσ, he, rfl⟩
  have v2 : ∀ h : List ℝ, ¬ Even h.length → pay₂ σ δ₂ h = rubinsteinShare δ₂ δ₁ :=
    fun h he => E2 _ ⟨σ, h, hσ, he, rfl⟩
  have len : ∀ x : ℝ, (h ++ [x]).length = h.length + 1 := fun x => by simp
  by_cases he : Even h.length
  · have hnext : ∀ x : ℝ, ¬ Even (h ++ [x]).length := fun x => by
      rw [len, Nat.even_add_one]; exact not_not.2 he
    -- the proposer's offer is accepted and equals `x*`
    have hacc : σ.acc h (σ.prop h) := by
      by_contra hn
      have h1 := v1 h he
      unfold pay₁ at h1
      rw [payoff_eq_resp, respPayoff, ite_eq_right_of_eq_false _ _ (eq_false hn)] at h1
      have hy := v2 _ (hnext (σ.prop h))
      have hb := pay_bounds h₁ h₁' h₂ h₂' σ (h ++ [σ.prop h])
      simp only [pay₁, pay₂] at hb hy
      have hle : rubinsteinShare δ₁ δ₂ ≤ δ₁ * (δ₁ * rubinsteinShare δ₁ δ₂) := by nlinarith
      nlinarith [hm.1, mul_nonneg h₁ h₁]
    have hx0 : σ.prop h = rubinsteinShare δ₁ δ₂ := by
      have h1 := v1 h he
      unfold pay₁ at h1
      rw [payoff_eq_resp, respPayoff, ite_eq_left_of_eq_true _ _ (eq_true hacc)] at h1
      exact h1
    refine ⟨by simp only [stationaryProfile, he, ↓reduceIte, hx0], fun x hx => ?_⟩
    have hst : (stationaryProfile h₁ h₁' h₂ h₂').acc h x ↔
        δ₂ * rubinsteinShare δ₂ δ₁ ≤ 1 - x := by
      simp only [stationaryProfile, he, true_and, not_true_eq_false, false_and, or_false]
    rw [hst]
    have hv := v2 _ (hnext x)
    constructor
    · intro ha
      have := spe_acc₂_le hσ he hx ha
      rwa [hv] at this
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact spe_acc₂ hσ he hx (by rw [hv]; exact hlt)
      · have : x = σ.prop h := by rw [hx0]; linarith
        rw [this]; exact hacc
  · have hnext : ∀ x : ℝ, Even (h ++ [x]).length := fun x => by
      rw [len, Nat.even_add_one]; exact he
    have hacc : σ.acc h (σ.prop h) := by
      by_contra hn
      have h2 := v2 h he
      unfold pay₂ at h2
      rw [payoff_eq_resp, respPayoff, ite_eq_right_of_eq_false _ _ (eq_false hn)] at h2
      have hx := v1 _ (hnext (σ.prop h))
      have hb := pay_bounds h₁ h₁' h₂ h₂' σ (h ++ [σ.prop h])
      simp only [pay₁, pay₂] at hb hx
      have hle : rubinsteinShare δ₂ δ₁ ≤ δ₂ * (δ₂ * rubinsteinShare δ₂ δ₁) := by nlinarith
      nlinarith [hm'.1, mul_nonneg h₂ h₂]
    have hx0 : σ.prop h = δ₁ * rubinsteinShare δ₁ δ₂ := by
      have h2 := v2 h he
      unfold pay₂ at h2
      rw [payoff_eq_resp, respPayoff, ite_eq_left_of_eq_true _ _ (eq_true hacc)] at h2
      linarith
    refine ⟨by simp only [stationaryProfile, he, ↓reduceIte, hx0], fun x hx => ?_⟩
    have hst : (stationaryProfile h₁ h₁' h₂ h₂').acc h x ↔ δ₁ * rubinsteinShare δ₁ δ₂ ≤ x := by
      simp only [stationaryProfile, he, false_and, false_or, not_false_eq_true, true_and]
    rw [hst]
    have hv := v1 _ (hnext x)
    constructor
    · intro ha
      have := spe_acc₁_le hσ he hx ha
      rwa [hv] at this
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact spe_acc₁ hσ he hx (by rw [hv]; exact hlt)
      · have : x = σ.prop h := by rw [hx0]; linarith
        rw [this]; exact hacc

/-- **Rubinstein's outcome** (Rubinstein 1982). In every pure-strategy subgame perfect
equilibrium, player 1 offers `x*` at the start, player 2 accepts immediately, and the payoffs
are `x*` and `1 − x*`. -/
theorem bargSPE_unique {σ : BargProfile} (hσ : IsBargSPE δ₁ δ₂ σ) :
    σ.prop [] = rubinsteinShare δ₁ δ₂ ∧ σ.acc [] (rubinsteinShare δ₁ δ₂) ∧
      pay₁ σ δ₁ [] = rubinsteinShare δ₁ δ₂ ∧ pay₂ σ δ₂ [] = 1 - rubinsteinShare δ₁ δ₂ := by
  have hm := rubinsteinShare_mem h₁ h₁' h₂ h₂'
  obtain ⟨e1, e2⟩ := stationary_eqs h₁ h₁' h₂'
  obtain ⟨hp, ha⟩ := bargSPE_eq_stationary h₁ h₁' h₂ h₂' hσ []
  have hx0 : σ.prop [] = rubinsteinShare δ₁ δ₂ := by
    rw [hp]; simp [stationaryProfile]
  have hacc : σ.acc [] (σ.prop []) := by
    rw [hx0, ha _ ⟨hm.1.le, hm.2⟩]
    left; refine ⟨by simp, by linarith⟩
  refine ⟨hx0, hx0 ▸ hacc, ?_, ?_⟩
  · unfold pay₁
    rw [payoff_eq_resp, respPayoff, ite_eq_left_of_eq_true _ _ (eq_true hacc)]
    exact hx0
  · unfold pay₂
    rw [payoff_eq_resp, respPayoff, ite_eq_left_of_eq_true _ _ (eq_true hacc)]
    exact congrArg (fun t => 1 - t) hx0

end Unique

end Econ
