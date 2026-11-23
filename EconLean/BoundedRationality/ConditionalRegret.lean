/-
# Conditional regret matching and correlated equilibrium

References. D. Foster and R. Vohra (1997), "Calibrated Learning and
Correlated Equilibrium", *GEB* 21; S. Hart and A. Mas-Colell (2000), "A
Simple Adaptive Procedure Leading to Correlated Equilibrium", *Econometrica*
68(5); A. Blum and Y. Mansour (2007), "From External to Internal Regret",
*JMLR* 8; N. Cesa-Bianchi and G. Lugosi (2006), *Prediction, Learning, and
Games*, §4.4 and §7.4.

A player keeps, for every ordered pair of actions `(j, k)`, the cumulative
**conditional (internal) regret** `D(j, k)`: the expected gain it would have
had by playing `k` every time it played `j`. Its mixed action `q` is a
stationary distribution of the Markov matrix that moves from `j` to `k` at
rate proportional to `D(j, k)⁺` (`condMatrix`, `crm`). Stationarity is the
balance condition `Σ_j q_j D(j,k)⁺ = q_k Σ_l D(k,l)⁺` (`crm_balance`), which
makes the regret increment orthogonal to the positive regrets (`crm_orth`).
Blackwell's potential bound (`RegretMatching.regret_le`, on the index set
`A × A`) then gives every conditional regret `≤ 2B |A| √T`.

**Games.** If every player uses this rule on expected payoffs against the
others' current mixtures (`condRegrets`, `condPlay`), then deterministically
* `condRegrets_eq`: player `i`'s cumulative conditional regret for `j → k` is
  `T` times the obedience gain of `j → k` under the time average of the
  product distributions played, `condAvg T`;
* `obedienceGain_condAvg_le`: every such gain is at most `2B |Sᵢ| / √T`;
* `eventually_isCE`: for every `ε > 0`, `condAvg T` is an `ε`-correlated
  equilibrium from some date on;
* `isCorrelatedEq_of_tendsto`: every limit of `condAvg` along `T → ∞` is a
  correlated equilibrium.

This is the expected-payoff (deterministic) form of the Foster–Vohra /
Hart–Mas-Colell result. Hart–Mas-Colell's own procedure plays realized pure
actions with a different (non-stationary-distribution) rule and proves almost
sure convergence of the empirical distribution of realized play; that
probabilistic statement is not formalized.
-/
module

public import EconLean.BoundedRationality.RegretMatching
public import EconLean.Macro.DP.MarkovChain

@[expose] public section

noncomputable section

namespace Econ

namespace RegretMatching

open Function Finset Filter Topology NoRegret Matrix

/-! ### The conditional regret-matching rule -/

section Rule

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The normalizing rate `λ = 1 + Σ_{j,k} D(j,k)⁺`. -/
def rate (D : A → A → ℝ) : ℝ := 1 + ∑ j, ∑ k, max (D j k) 0

omit [DecidableEq A] in
theorem rate_pos (D : A → A → ℝ) : 0 < rate D := by
  unfold rate
  have : 0 ≤ ∑ j, ∑ k, max (D j k) 0 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => le_max_right _ _
  linarith

omit [DecidableEq A] in
theorem rowSum_le_rate (D : A → A → ℝ) (j : A) : ∑ k, max (D j k) 0 ≤ rate D := by
  unfold rate
  have := single_le_sum (f := fun j => ∑ k, max (D j k) 0)
    (fun _ _ => sum_nonneg fun _ _ => le_max_right _ _) (mem_univ j)
  linarith

/-- The Markov matrix moving from `j` to `k` with probability
`D(j,k)⁺/λ` and staying put with the remaining probability. -/
def condMatrix (D : A → A → ℝ) : Matrix A A ℝ := fun j k =>
  max (D j k) 0 / rate D + if j = k then 1 - (∑ l, max (D j l) 0) / rate D else 0

theorem condMatrix_isStochastic (D : A → A → ℝ) : IsStochastic (condMatrix D) := by
  have hr := rate_pos D
  refine ⟨fun j k => ?_, fun j => ?_⟩
  · unfold condMatrix
    have h1 : 0 ≤ max (D j k) 0 / rate D := div_nonneg (le_max_right _ _) hr.le
    split_ifs
    · have : (∑ l, max (D j l) 0) / rate D ≤ 1 := (div_le_one hr).2 (rowSum_le_rate D j)
      linarith
    · linarith
  · simp only [condMatrix, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← sum_div]
    ring

variable [Nonempty A]

/-- **Conditional regret matching**: a stationary distribution of
`condMatrix D`. -/
def crm (D : A → A → ℝ) : A → ℝ :=
  Classical.choose (exists_invariant (condMatrix_isStochastic D))

theorem crm_isInvariant (D : A → A → ℝ) : IsInvariant (condMatrix D) (crm D) :=
  Classical.choose_spec (exists_invariant (condMatrix_isStochastic D))

theorem crm_mem (D : A → A → ℝ) : crm D ∈ lotteries A :=
  ⟨(crm_isInvariant D).1.1, (crm_isInvariant D).1.2⟩

/-- **Balance**: inflow equals outflow at every action. -/
theorem crm_balance (D : A → A → ℝ) (k : A) :
    ∑ j, crm D j * max (D j k) 0 = crm D k * ∑ l, max (D k l) 0 := by
  have h := congrFun (crm_isInvariant D).2 k
  rw [vecMul_apply'] at h
  have hr := (rate_pos D).ne'
  simp only [condMatrix, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ite_true] at h
  have e : ∑ j, crm D j * (max (D j k) 0 / rate D) = (∑ j, crm D j * max (D j k) 0) / rate D :=
    by rw [sum_div]; exact sum_congr rfl fun j _ => by ring
  rw [e] at h
  field_simp at h
  linarith

/-- **Orthogonality** for conditional regrets: for every payoff vector `g`,
`Σ_{j,k} D(j,k)⁺ q_j (g_k − g_j) = 0` at `q = crm D`. -/
theorem crm_orth (D : A → A → ℝ) (g : A → ℝ) :
    ∑ jk : A × A, max (D jk.1 jk.2) 0 * (crm D jk.1 * (g jk.2 - g jk.1)) = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [mul_sub, sum_sub_distrib]
  have h1 : ∑ j, ∑ k, max (D j k) 0 * (crm D j * g k) =
      ∑ k, g k * ∑ j, crm D j * max (D j k) 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, ∑ k, max (D j k) 0 * (crm D j * g j) =
      ∑ k, g k * (crm D k * ∑ l, max (D k l) 0) := by
    refine sum_congr rfl fun j _ => ?_
    simp only [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [h1, h2]
  simp only [crm_balance, sub_self]

end Rule

/-! ### Conditional regret matching in games -/

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- Cumulative conditional regrets when all players use conditional regret
matching on expected payoffs. -/
def condRegrets (u : I → (∀ j, S j) → ℝ) : ℕ → ∀ i, S i → S i → ℝ
  | 0 => fun _ _ _ => 0
  | t + 1 => fun i j k => condRegrets u t i j k +
      crm (condRegrets u t i) j * (pureDev u (fun l => crm (condRegrets u t l)) i k -
        pureDev u (fun l => crm (condRegrets u t l)) i j)

/-- The mixed profile played in period `t`. -/
def condPlay (u : I → (∀ j, S j) → ℝ) (t : ℕ) : ∀ i, S i → ℝ :=
  fun l => crm (condRegrets u t l)

/-- The time-average of the product distributions played. -/
def condAvg (u : I → (∀ j, S j) → ℝ) (T : ℕ) (s : ∀ j, S j) : ℝ :=
  (∑ t ∈ range T, profileProb (condPlay u t) s) / T

theorem condPlay_isMixedProfile (u : I → (∀ j, S j) → ℝ) (t : ℕ) :
    IsMixedProfile (condPlay u t) := fun _ => crm_mem _

theorem condAvg_mem (u : I → (∀ j, S j) → ℝ) {T : ℕ} (hT : 0 < T) :
    condAvg u T ∈ lotteries (∀ j, S j) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  refine ⟨fun s => div_nonneg (sum_nonneg fun t _ =>
    profileProb_nonneg (condPlay_isMixedProfile u t) s) hT'.le, ?_⟩
  simp only [condAvg, ← sum_div]
  rw [sum_comm]
  simp only [sum_profileProb (condPlay_isMixedProfile u _), sum_const, card_range, nsmul_eq_mul,
    mul_one]
  exact div_self hT'.ne'

omit [∀ i, Nonempty (S i)] in
theorem obedienceGain_add (u : I → (∀ j, S j) → ℝ) (μ ν : (∀ j, S j) → ℝ) (i : I)
    (j k : S i) : obedienceGain u (μ + ν) i j k = obedienceGain u μ i j k + obedienceGain u ν i j k := by
  simp only [obedienceGain, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [add_mul]

/-- Cumulative conditional regret is `T` times the obedience gain of the
average play. -/
theorem condRegrets_eq (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (j k : S i) :
    condRegrets u T i j k = T * obedienceGain u (condAvg u T) i j k := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [condRegrets]
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hsum : condRegrets u T i j k =
      ∑ t ∈ range T, obedienceGain u (profileProb (condPlay u t)) i j k := by
    clear hT hT'
    induction T with
    | zero => simp [condRegrets]
    | succ T ih =>
      rw [sum_range_succ, ← ih, obedienceGain_profileProb]
      rfl
  rw [hsum]
  simp only [obedienceGain, condAvg]
  rw [mul_sum, sum_comm]
  refine sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [← sum_mul]; field_simp
  · simp

/-- **Conditional regret bound**: every obedience gain of the average play is
at most `2B |Sᵢ| / √T`. -/
theorem obedienceGain_condAvg_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {T : ℕ} (hT : 0 < T) (i : I) (j k : S i) :
    obedienceGain u (condAvg u T) i j k ≤ 2 * B * Fintype.card (S i) / Real.sqrt T := by
  have hB0 : 0 ≤ B := by
    obtain ⟨s⟩ : Nonempty (∀ j, S j) := inferInstance
    exact (abs_nonneg _).trans (hB i s)
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hdev : ∀ t (a : S i), |pureDev u (condPlay u t) i a| ≤ B := fun t a =>
    abs_mixedPayoff_le u hB (fun l => by
      by_cases hl : l = i
      · subst hl; rw [update_self]; exact degenerate_mem a
      · rw [update_of_ne hl]; exact condPlay_isMixedProfile u t l) i
  have hreg := regret_le (A := S i × S i) (R := fun t jk => condRegrets u t i jk.1 jk.2)
    (r := fun t jk => condPlay u t i jk.1 *
      (pureDev u (condPlay u t) i jk.2 - pureDev u (condPlay u t) i jk.1))
    (by positivity : 0 ≤ 2 * B) (funext fun _ => rfl) (fun t => funext fun _ => rfl)
    (fun t => le_of_eq (crm_orth (condRegrets u t i) fun a => pureDev u (condPlay u t) i a))
    (fun t jk => by
      have hq := crm_mem (condRegrets u t i)
      have hq1 : condPlay u t i jk.1 ≤ 1 := by
        have := single_le_sum (f := condPlay u t i) (fun a _ => hq.1 a) (mem_univ jk.1)
        rw [show ∑ a, condPlay u t i a = 1 from hq.2] at this; exact this
      have hq0 : 0 ≤ condPlay u t i jk.1 := hq.1 _
      rw [abs_mul, abs_of_nonneg hq0]
      have h1 : |pureDev u (condPlay u t) i jk.2 - pureDev u (condPlay u t) i jk.1| ≤ 2 * B :=
        (abs_sub _ _).trans (by linarith [hdev t jk.2, hdev t jk.1])
      nlinarith [abs_nonneg (pureDev u (condPlay u t) i jk.2 -
        pureDev u (condPlay u t) i jk.1)]) T (j, k)
  simp only [condRegrets_eq, Fintype.card_prod] at hreg
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT'
  have e : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT'.le
  have hc : Real.sqrt ((Fintype.card (S i) * Fintype.card (S i) : ℕ) * (T : ℝ)) =
      Fintype.card (S i) * Real.sqrt T := by
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  rw [hc] at hreg
  rw [le_div_iff₀ hsT]
  have h3 : Real.sqrt T * (obedienceGain u (condAvg u T) i j k * Real.sqrt T) ≤
      Real.sqrt T * (2 * B * Fintype.card (S i)) := by
    have l : Real.sqrt T * (obedienceGain u (condAvg u T) i j k * Real.sqrt T) =
        (Real.sqrt T * Real.sqrt T) * obedienceGain u (condAvg u T) i j k := by ring
    have r : Real.sqrt T * (2 * B * Fintype.card (S i)) =
        2 * B * (Fintype.card (S i) * Real.sqrt T) := by ring
    rw [l, r, e]; exact hreg
  exact le_of_mul_le_mul_left h3 hsT

/-- **Conditional regret matching leads to correlated equilibrium**: for every
`ε > 0`, the average play is an `ε`-correlated equilibrium from some date on. -/
theorem eventually_isCE (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ T in atTop, IsCE u ε (condAvg u T) := by
  have hlim : ∀ i : I, Tendsto (fun T : ℕ => 2 * B * Fintype.card (S i) / Real.sqrt T) atTop
      (𝓝 0) := fun i =>
    tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
  have hev : ∀ i : I, ∀ᶠ T : ℕ in atTop, 2 * B * Fintype.card (S i) / Real.sqrt T < ε :=
    fun i => (hlim i).eventually (gt_mem_nhds hε)
  filter_upwards [(eventually_all.2 hev).and (eventually_gt_atTop 0)] with T ⟨hT, hpos⟩
  exact ⟨condAvg_mem u hpos, fun i j k =>
    (obedienceGain_condAvg_le u hB hpos i j k).trans (hT i).le⟩

/-- **Limits of conditional regret-matching play are correlated equilibria.** -/
theorem isCorrelatedEq_of_tendsto (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => condAvg u (φ n)) atTop (𝓝 μ)) : IsCorrelatedEq u μ := by
  refine ⟨isClosed_lotteries.mem_of_tendsto hμ
    ((hφ.eventually (eventually_gt_atTop 0)).mono fun n hn => condAvg_mem u hn),
    fun i j k => ?_⟩
  have hc := ((continuous_obedienceGain u i j k).tendsto μ).comp hμ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  refine le_of_tendsto hc ?_
  filter_upwards [hφ.eventually (eventually_isCE u hB hε)] with n hn
  exact hn.2 i j k

end RegretMatching

end Econ
