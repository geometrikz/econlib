/-
# Regret matching

References. S. Hart and A. Mas-Colell (2000), "A Simple Adaptive Procedure
Leading to Correlated Equilibrium", *Econometrica* 68(5), and (2001), "A
General Class of Adaptive Strategies", *JET* 98 (unconditional regret
matching); D. Blackwell (1956), "An Analog of the Minimax Theorem for Vector
Payoffs", *Pacific J. Math.* 6 (approachability). The deterministic bound
below is the one in N. Cesa-Bianchi and G. Lugosi (2006), *Prediction,
Learning, and Games*, §2.3 and §7.

**Blackwell's potential argument.** Let `R t ∈ ℝ^A` be a cumulative regret
vector, `R (t+1) = R t + r t`, with `|r t a| ≤ M`. If every increment is
orthogonal to the positive part of the current regret,
`Σ_a (R t a)⁺ r t a ≤ 0`, then `Σ_a ((R T a)⁺)² ≤ T |A| M²`
(`potential_le`), so every regret is at most `M √(|A| T)` (`regret_le`).

**Regret matching** plays each action with probability proportional to its
positive regret (uniformly if no regret is positive), `rm`. This choice makes
the increment orthogonal (`rm_orth`), whatever the payoffs.

This is **unconditional** regret matching (Hart–Mas-Colell 2000 §4(c), 2001):
it yields Hannan consistency and hence coarse correlated equilibrium, not
the correlated equilibrium of Hart–Mas-Colell's main (conditional) theorem.

**Games.** Every player of a finite game runs unconditional regret matching on
its expected payoffs against the others' current mixtures (`play`,
`regrets`). Then, deterministically and against no assumption on the game
beyond `|u| ≤ B`:
* `regrets_eq`: player `i`'s cumulative regret for `a` is `T` times the
  coarse-correlated gain of switching to `a` under `avgDist T`, the time
  average of the product distributions played;
* `cceGain_avgDist_le`: every such gain is at most `2B √(|Sᵢ|) / √T`;
* `eventually_isCCE`: for every `ε > 0`, `avgDist T` is an `ε`-coarse
  correlated equilibrium for all large `T`;
* `isCCE_of_tendsto`: every limit of `avgDist` along `T → ∞` is a coarse
  correlated equilibrium.

Here regrets are measured with the expected payoffs of the mixtures actually
played (no sampling), so there is no probability: the realized-play version
needs martingale arguments (Hart–Mas-Colell's almost-sure theorem) and is not
formalized; neither is conditional regret matching, which leads to correlated
equilibria.
-/
module

public import EconLean.BoundedRationality.NoRegret

@[expose] public section

noncomputable section

namespace Econ

namespace RegretMatching

open Function Finset Filter Topology NoRegret

/-! ### Blackwell's potential bound -/

section Potential

variable {A : Type*} [Fintype A]

/-- The potential `Σ_a ((x a)⁺)²`. -/
def potential (x : A → ℝ) : ℝ := ∑ a, max (x a) 0 ^ 2

theorem potential_nonneg (x : A → ℝ) : 0 ≤ potential x :=
  sum_nonneg fun _ _ => sq_nonneg _

private theorem pos_sq_add_le (x r : ℝ) :
    max (x + r) 0 ^ 2 ≤ max x 0 ^ 2 + 2 * (max x 0 * r) + r ^ 2 := by
  rcases le_total (x + r) 0 with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (max x 0 + r)]
  · rw [max_eq_left h]
    have h1 : x + r ≤ max x 0 + r := by linarith [le_max_left x 0]
    nlinarith

/-- One step of the potential. -/
theorem potential_add_le (x r : A → ℝ) :
    potential (x + r) ≤ potential x + 2 * ∑ a, max (x a) 0 * r a + ∑ a, r a ^ 2 := by
  unfold potential
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_le_sum fun a _ => pos_sq_add_le (x a) (r a)

/-- **Blackwell's potential bound.** -/
theorem potential_le {R r : ℕ → A → ℝ} {M : ℝ} (h0 : R 0 = 0)
    (hR : ∀ t, R (t + 1) = R t + r t) (horth : ∀ t, ∑ a, max (R t a) 0 * r t a ≤ 0)
    (hb : ∀ t a, |r t a| ≤ M) (T : ℕ) :
    potential (R T) ≤ T * Fintype.card A * M ^ 2 := by
  induction T with
  | zero => simp [h0, potential]
  | succ T ih =>
    have hs : ∑ a, r T a ^ 2 ≤ Fintype.card A * M ^ 2 := by
      calc ∑ a, r T a ^ 2 ≤ ∑ _a : A, M ^ 2 :=
            sum_le_sum fun a _ => by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb T a) 2
        _ = _ := by simp
    have := potential_add_le (R T) (r T)
    rw [hR]
    push_cast
    nlinarith [horth T]

/-- **Regret bound**: every cumulative regret is at most `M √(|A| T)`. -/
theorem regret_le {R r : ℕ → A → ℝ} {M : ℝ} (hM : 0 ≤ M) (h0 : R 0 = 0)
    (hR : ∀ t, R (t + 1) = R t + r t) (horth : ∀ t, ∑ a, max (R t a) 0 * r t a ≤ 0)
    (hb : ∀ t a, |r t a| ≤ M) (T : ℕ) (a : A) :
    R T a ≤ M * Real.sqrt (Fintype.card A * T) := by
  have hP := potential_le h0 hR horth hb T
  have h1 : max (R T a) 0 ^ 2 ≤ potential (R T) :=
    single_le_sum (f := fun a => max (R T a) 0 ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a)
  have h2 : max (R T a) 0 ≤ Real.sqrt (T * Fintype.card A * M ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have e : Real.sqrt (T * Fintype.card A * M ^ 2) = M * Real.sqrt (Fintype.card A * T) := by
    rw [show (T : ℝ) * Fintype.card A * M ^ 2 = M ^ 2 * (Fintype.card A * T) by ring,
      Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
  linarith [le_max_left (R T a) 0]

/-! ### The regret-matching rule -/

variable [Nonempty A]

/-- **Regret matching**: probabilities proportional to positive regrets,
uniform if none is positive. -/
def rm (x : A → ℝ) : A → ℝ :=
  if 0 < ∑ b, max (x b) 0 then fun a => max (x a) 0 / ∑ b, max (x b) 0
  else fun _ => 1 / Fintype.card A

theorem rm_mem (x : A → ℝ) : rm x ∈ lotteries A := by
  unfold rm
  split_ifs with h
  · refine ⟨fun a => div_nonneg (le_max_right _ _) h.le, ?_⟩
    rw [← sum_div, div_self h.ne']
  · refine ⟨fun a => by positivity, ?_⟩
    simp

omit [Nonempty A] in
/-- **Orthogonality**: under regret matching, the next regret increment is
orthogonal to the current positive regrets, for every payoff vector `g`. -/
theorem rm_orth (x g : A → ℝ) :
    ∑ a, max (x a) 0 * (g a - ∑ b, rm x b * g b) = 0 := by
  unfold rm
  split_ifs with h
  · simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [sum_congr rfl fun b _ => div_mul_eq_mul_div (max (x b) 0) _ (g b), ← sum_div,
      mul_div_cancel₀ _ h.ne', sub_self]
  · have h0 : ∀ a, max (x a) 0 = 0 := fun a =>
      le_antisymm ((single_le_sum (f := fun b => max (x b) 0) (fun _ _ => le_max_right _ _)
        (mem_univ a)).trans (not_lt.1 h)) (le_max_right _ _)
    simp [h0]

end Potential

/-! ### Regret matching in games -/

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- Cumulative regrets when all players use regret matching on expected
payoffs: `regrets u t i a`. -/
def regrets (u : I → (∀ j, S j) → ℝ) : ℕ → ∀ i, S i → ℝ
  | 0 => fun _ _ => 0
  | t + 1 => fun i a => regrets u t i a +
      (pureDev u (fun j => rm (regrets u t j)) i a - mixedPayoff u (fun j => rm (regrets u t j)) i)

/-- The mixed profile played in period `t`. -/
def play (u : I → (∀ j, S j) → ℝ) (t : ℕ) : ∀ i, S i → ℝ := fun j => rm (regrets u t j)

/-- The time-average of the product distributions played in periods `0, …, T−1`. -/
def avgDist (u : I → (∀ j, S j) → ℝ) (T : ℕ) (s : ∀ j, S j) : ℝ :=
  (∑ t ∈ range T, profileProb (play u t) s) / T

theorem play_isMixedProfile (u : I → (∀ j, S j) → ℝ) (t : ℕ) : IsMixedProfile (play u t) :=
  fun _ => rm_mem _

theorem avgDist_mem (u : I → (∀ j, S j) → ℝ) {T : ℕ} (hT : 0 < T) :
    avgDist u T ∈ lotteries (∀ j, S j) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  refine ⟨fun s => div_nonneg (sum_nonneg fun t _ =>
    profileProb_nonneg (play_isMixedProfile u t) s) hT'.le, ?_⟩
  simp only [avgDist, ← sum_div]
  rw [sum_comm]
  simp only [sum_profileProb (play_isMixedProfile u _), sum_const, card_range, nsmul_eq_mul,
    mul_one]
  exact div_self hT'.ne'

omit [∀ i, Nonempty (S i)] in
/-- The coarse gain under a product distribution is the gain of the pure
deviation against the others' mixtures. -/
theorem cceGain_profileProb (u : I → (∀ j, S j) → ℝ) {σ : ∀ i, S i → ℝ}
    (hσ : IsMixedProfile σ) (i : I) (a : S i) :
    cceGain u (profileProb σ) i a = pureDev u σ i a - mixedPayoff u σ i := by
  rw [pureDev_eq_sum_update u (hσ i)]
  simp only [cceGain, mixedPayoff, mul_sub, sum_sub_distrib]

omit [∀ i, Nonempty (S i)] in
theorem regrets_succ (u : I → (∀ j, S j) → ℝ) (t : ℕ) (i : I) :
    regrets u (t + 1) i = regrets u t i +
      fun a => pureDev u (play u t) i a - mixedPayoff u (play u t) i := rfl

/-- Cumulative regret is `T` times the coarse gain of the average play. -/
theorem regrets_eq (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (a : S i) :
    regrets u T i a = T * cceGain u (avgDist u T) i a := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [regrets]
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hsum : regrets u T i a = ∑ t ∈ range T, cceGain u (profileProb (play u t)) i a := by
    clear hT hT'
    induction T with
    | zero => simp [regrets]
    | succ T ih =>
      rw [sum_range_succ, ← ih, regrets_succ, cceGain_profileProb u (play_isMixedProfile u T)]
      rfl
  rw [hsum]
  simp only [cceGain, avgDist, div_mul_eq_mul_div, ← sum_div, sum_mul]
  rw [mul_div_cancel₀ _ hT', sum_comm]

omit [∀ i, Nonempty (S i)] [∀ i, DecidableEq (S i)] in
/-- Payoffs bounded by `B` give expected payoffs bounded by `B`. -/
theorem abs_mixedPayoff_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {σ : ∀ i, S i → ℝ} (hσ : IsMixedProfile σ) (i : I) : |mixedPayoff u σ i| ≤ B := by
  unfold mixedPayoff
  calc |∑ s, profileProb σ s * u i s| ≤ ∑ s, |profileProb σ s * u i s| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, profileProb σ s * B := sum_le_sum fun s _ => by
        rw [abs_mul, abs_of_nonneg (profileProb_nonneg hσ s)]
        exact mul_le_mul_of_nonneg_left (hB i s) (profileProb_nonneg hσ s)
    _ = B := by rw [← sum_mul, sum_profileProb hσ, one_mul]

/-- **Regret matching bound**: under regret matching by all players, every
coarse-correlated gain of the average play is at most `2B √(|Sᵢ|) / √T`. -/
theorem cceGain_avgDist_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {T : ℕ} (hT : 0 < T) (i : I) (a : S i) :
    cceGain u (avgDist u T) i a ≤
      2 * B * Real.sqrt (Fintype.card (S i)) / Real.sqrt T := by
  have hB0 : 0 ≤ B := by
    obtain ⟨s⟩ : Nonempty (∀ j, S j) := inferInstance
    exact (abs_nonneg _).trans (hB i s)
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hreg := regret_le (R := fun t => regrets u t i)
    (r := fun t a => pureDev u (play u t) i a - mixedPayoff u (play u t) i)
    (by positivity : 0 ≤ 2 * B) (funext fun _ => rfl) (fun t => regrets_succ u t i)
    (fun t => le_of_eq (Eq.trans (sum_congr rfl fun b _ => by
      show _ = max (regrets u t i b) 0 *
        (pureDev u (play u t) i b - ∑ c, rm (regrets u t i) c * pureDev u (play u t) i c)
      rw [mixedPayoff_eq_sum_pureDev]; rfl)
      (rm_orth (regrets u t i) (fun a => pureDev u (play u t) i a))))
    (fun t b => by
      have h1 := abs_mixedPayoff_le u hB (play_isMixedProfile u t) i
      have h2 : |pureDev u (play u t) i b| ≤ B := abs_mixedPayoff_le u hB
        (fun j => by
          by_cases hj : j = i
          · subst hj; rw [update_self]; exact degenerate_mem b
          · rw [update_of_ne hj]; exact play_isMixedProfile u t j) i
      calc |pureDev u (play u t) i b - mixedPayoff u (play u t) i|
          ≤ |pureDev u (play u t) i b| + |mixedPayoff u (play u t) i| := abs_sub _ _
        _ ≤ 2 * B := by linarith) T a
  simp only [regrets_eq] at hreg
  rw [Real.sqrt_mul (Nat.cast_nonneg _)] at hreg
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT'
  have e : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT'.le
  rw [le_div_iff₀ hsT]
  have h3 : Real.sqrt T * (cceGain u (avgDist u T) i a * Real.sqrt T) ≤
      Real.sqrt T * (2 * B * Real.sqrt (Fintype.card (S i))) := by
    have l : Real.sqrt T * (cceGain u (avgDist u T) i a * Real.sqrt T) =
        (Real.sqrt T * Real.sqrt T) * cceGain u (avgDist u T) i a := by ring
    have r : Real.sqrt T * (2 * B * Real.sqrt (Fintype.card (S i))) =
        2 * B * (Real.sqrt (Fintype.card (S i)) * Real.sqrt T) := by ring
    rw [l, r, e]; exact hreg
  exact le_of_mul_le_mul_left h3 hsT

/-- **Regret matching leads to coarse correlated equilibrium**: for every
`ε > 0`, the average play is an `ε`-CCE from some date on. -/
theorem eventually_isCCE (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ T in atTop, IsCCE u ε (avgDist u T) := by
  -- the bound `2B√|Sᵢ|/√T` tends to `0`, uniformly over the finitely many players
  have hlim : ∀ i : I, Tendsto (fun T : ℕ => 2 * B * Real.sqrt (Fintype.card (S i)) /
      Real.sqrt T) atTop (𝓝 0) := fun i => by
    have h := tendsto_const_nhds (x := 2 * B * Real.sqrt (Fintype.card (S i))) |>.div_atTop
      ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
    exact h
  have hev : ∀ i : I, ∀ᶠ T : ℕ in atTop,
      2 * B * Real.sqrt (Fintype.card (S i)) / Real.sqrt T < ε := fun i =>
    (hlim i).eventually (gt_mem_nhds hε)
  have hall := (eventually_all.2 hev).and (eventually_gt_atTop 0)
  filter_upwards [hall] with T ⟨hT, hpos⟩
  exact ⟨avgDist_mem u hpos, fun i a => (cceGain_avgDist_le u hB hpos i a).trans (hT i).le⟩

/-- **Limits of regret-matching play are coarse correlated equilibria.** -/
theorem isCCE_of_tendsto (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => avgDist u (φ n)) atTop (𝓝 μ)) : IsCCE u 0 μ := by
  refine ⟨isClosed_lotteries.mem_of_tendsto hμ
    ((hφ.eventually (eventually_gt_atTop 0)).mono fun n hn => avgDist_mem u hn), fun i a => ?_⟩
  have hc := ((continuous_cceGain u i a).tendsto μ).comp hμ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  refine le_of_tendsto hc ?_
  filter_upwards [hφ.eventually (eventually_isCCE u hB hε)] with n hn
  exact hn.2 i a

end RegretMatching

end Econ
