/-
# Present bias: quasi-hyperbolic (β–δ) discounting

References.
* D. Laibson (1997), "Golden Eggs and Hyperbolic Discounting", *QJE* 112(2).
  Quasi-hyperbolic discount function `1, βδ, βδ², …`.
* T. O'Donoghue and M. Rabin (1999), "Doing It Now or Later", *AER* 89(1).
  The one-shot task model, naive vs sophisticated agents, and their
  Propositions comparing completion dates.
* R. H. Strotz (1956), "Myopia and Inconsistency in Dynamic Utility
  Maximization": a time-inconsistent agent who foresees it plays "consistent
  planning", i.e. the subgame-perfect equilibrium of the game between its
  successive selves.

**The economics.** Self `t` values a payoff that arrives `k` periods later at
`D(k)` times its face value, where

    D(0) = 1,   D(k) = β δ^k  for k ≥ 1.

With `β = 1` this is ordinary exponential discounting. With `β < 1` there is an
extra penalty on *everything* that is not "now", which produces preference
reversals: from far away you prefer the larger-later reward, but when the
smaller reward becomes immediate you grab it. Part 1 proves that reversals
happen exactly when `β < 1` (for positive rewards), and that `β = 1`
preferences over dated rewards are the same at every date (time consistency).

Part 2 is the O'Donoghue–Rabin task model. A task must be done exactly once in
one of the periods `1, …, T`. Doing it in period `τ` yields reward `v τ` and
cost `c τ`. Following the paper we set the long-run discount factor `δ = 1`.
Self `t` (task not yet done) values doing it at `τ > t` at `β (v τ - c τ)`, and
doing it now at
* `β v t - c t` when **costs are immediate** (rewards come later), or
* `v t - β c t` when **rewards are immediate** (costs come later).

Three agent types:
* **time-consistent (TC)**: `β = 1`;
* **naive**: believes future selves will behave time-consistently, so self `t`
  does the task now iff now is at least as good (in its eyes) as every later
  date (O'Donoghue–Rabin's definition, with the paper's tie-break "when
  indifferent, do it now");
* **sophisticated**: correctly predicts its future selves; its plan is computed
  by backward induction from the deadline (Strotz consistent planning, the
  subgame-perfect equilibrium of the intrapersonal game).

Results (O'Donoghue–Rabin 1999):
* `soph_le_naive`: sophisticates complete no later than naifs, for **any**
  payoff schedule (Proposition 2 in the paper covers both schedules);
* `tc_le_naive_of_immediateCosts`: with immediate costs naifs procrastinate
  relative to the TC agent (Proposition 1);
* `naive_le_tc_of_immediateRewards`: with immediate rewards naifs
  preproperate (Proposition 1);
* worked examples: the "report" (immediate costs `3,5,8,13`, `β = 1/2`) and
  "movie" (immediate rewards `3,5,8,13`) examples of the paper.

**Scope note.** The Harris–Laibson nonexistence of (pure, stationary)
equilibria with continuous choice is not formalized: in the finite-horizon,
finite-choice task model the backward-induction plan always exists, which is
what `sophFrom` constructs.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Econ

namespace PresentBias

/-! ## Part 1. The β–δ discount function and preference reversals -/

/-- Laibson's quasi-hyperbolic discount weight on a payoff `k` periods ahead:
`1` for `k = 0`, `β δ^k` for `k ≥ 1`. -/
noncomputable def discount (β δ : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else β * δ ^ k

/-- The present value, to the self living at date `t`, of reward `a` received at
date `s ≥ t`. (For `s < t` the reward is in the past; Lean's truncated
subtraction then gives weight `1`, a junk value that no theorem uses: every
statement assumes `t ≤ s`.) -/
noncomputable def presentValue (β δ : ℝ) (t : ℕ) (a : ℝ) (s : ℕ) : ℝ :=
  discount β δ (s - t) * a

/-- With `β = 1` the discount function is exponential, `δ^k`. -/
theorem discount_one (δ : ℝ) (k : ℕ) : discount 1 δ k = δ ^ k := by
  unfold discount
  split_ifs with h
  · simp [h]
  · simp

/-- **Time consistency of exponential discounting.** With `β = 1` and `δ > 0`,
the self at date `t` and the self at any later date `t' ≤ s, s'` rank the dated
rewards `(a at s)` and `(b at s')` the same way. -/
theorem exponential_timeConsistent {δ : ℝ} (hδ : 0 < δ) {t t' s s' : ℕ}
    (htt' : t ≤ t') (hs : t' ≤ s) (hs' : t' ≤ s') (a b : ℝ) :
    presentValue 1 δ t b s' < presentValue 1 δ t a s ↔
      presentValue 1 δ t' b s' < presentValue 1 δ t' a s := by
  unfold presentValue
  simp only [discount_one]
  -- Factor out `δ^(t'-t)` from both sides at date `t`.
  have e1 : s - t = (s - t') + (t' - t) := by omega
  have e2 : s' - t = (s' - t') + (t' - t) := by omega
  rw [e1, e2, pow_add, pow_add]
  have hpos : 0 < δ ^ (t' - t) := pow_pos hδ _
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- A **preference reversal** between a smaller-sooner reward `a` at date `s`
and a larger-later reward `b` at date `s+1`: viewed from date `0` the later
reward is strictly preferred, but at date `s` the immediate one is strictly
preferred. -/
def PreferenceReversal (β δ : ℝ) (a b : ℝ) (s : ℕ) : Prop :=
  0 < s ∧ presentValue β δ 0 a s < presentValue β δ 0 b (s + 1) ∧
    presentValue β δ s b (s + 1) < presentValue β δ s a s

/-- **Present bias ⟺ preference reversals.** For `0 < β` and `0 < δ`, there are
positive rewards that exhibit a preference reversal exactly when `β < 1`. -/
theorem exists_preferenceReversal_iff {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) :
    (∃ a b : ℝ, ∃ s : ℕ, 0 < a ∧ 0 < b ∧ PreferenceReversal β δ a b s) ↔ β < 1 := by
  constructor
  · rintro ⟨a, b, s, ha, hb, hs, h0, h1⟩
    simp [presentValue, discount, hs.ne'] at h0 h1
    -- From date 0: `β δ^s a < β δ^(s+1) b`, i.e. `a < δ b`.
    have hpos : 0 < β * δ ^ s := mul_pos hβ (pow_pos hδ _)
    have h0' : a < δ * b := by
      rw [pow_succ] at h0
      nlinarith
    -- From date s: `β δ b < a`. Together: `β δ b < δ b`, so `β < 1`.
    by_contra hge
    push Not at hge
    nlinarith [mul_pos hδ hb]
  · intro hβ1
    -- Take `b = 1`, `a = δ (1 + β) / 2`, strictly between `β δ` and `δ`.
    refine ⟨δ * (1 + β) / 2, 1, 1, by positivity, one_pos, one_pos, ?_, ?_⟩
    · simp only [presentValue, discount]
      norm_num
      nlinarith [mul_pos hβ hδ, mul_pos (mul_pos hβ hδ) hδ]
    · simp only [presentValue, discount]
      norm_num
      nlinarith [mul_pos hβ hδ]

/-- With `β = 1` there are no preference reversals at all (any rewards). -/
theorem not_preferenceReversal_of_beta_one {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) (s : ℕ) :
    ¬ PreferenceReversal 1 δ a b s := by
  rintro ⟨_, h0, h1⟩
  -- Date-0 ranking `a@s < b@(s+1)` carries over to date `s`, contradicting `h1`.
  have h := (exponential_timeConsistent (t := 0) (t' := s) (s := s + 1) (s' := s) hδ
    (Nat.zero_le _) (Nat.le_succ _) le_rfl b a).1 h0
  exact lt_asymm h h1

/-! ## Part 2. O'Donoghue–Rabin (1999): doing it now or later -/

/-- When the task's costs and rewards are experienced. -/
inductive Schedule
  /-- costs are paid when the task is done, rewards come later (writing a report) -/
  | immediateCosts
  /-- rewards are enjoyed when the task is done, costs come later (seeing a movie) -/
  | immediateRewards

/-- A one-shot task (O'Donoghue–Rabin 1999 §I). Periods are `1, …, T`; the
task must be done in exactly one of them. `δ = 1` as in the paper. -/
structure Task where
  /-- the deadline: the last period in which the task can be done -/
  T : ℕ
  /-- there is at least one period -/
  one_le_T : 1 ≤ T
  /-- the reward from doing the task in period `τ` -/
  v : ℕ → ℝ
  /-- the cost of doing the task in period `τ` -/
  c : ℕ → ℝ
  /-- whether costs or rewards are immediate -/
  schedule : Schedule

namespace Task

variable (P : Task)

/-- Long-run (β-free) net value of doing the task in period `τ`. -/
def w (τ : ℕ) : ℝ := P.v τ - P.c τ

/-- Self `t`'s utility, with present-bias parameter `β`, of doing the task in
period `τ` (meaningful for `τ ≥ t`; `δ = 1` as in the paper): the immediate component is undiscounted, everything
else gets weight `β`. -/
def U (β : ℝ) (t τ : ℕ) : ℝ :=
  if τ = t then
    match P.schedule with
    | .immediateCosts => β * P.v t - P.c t
    | .immediateRewards => P.v t - β * P.c t
  else β * P.w τ

/-- **Naive** self `t` (in period `1 ≤ t ≤ T`, task not yet done) does the task
now iff it is the deadline or now is weakly preferred to every later period.
(A naif believes future selves are time-consistent; since self `t` weights all
future dates by the same `β`, the date it expects to complete at is one of the
later periods, so this is equivalent to comparing with that expected date.) -/
def NaiveDoes (β : ℝ) (t : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ P.T ∧ (t = P.T ∨ ∀ τ, t < τ → τ ≤ P.T → P.U β t τ ≤ P.U β t t)

theorem naiveDoes_T (β : ℝ) : P.NaiveDoes β P.T := ⟨P.one_le_T, le_rfl, Or.inl rfl⟩

open Classical in
/-- The naif's completion date `τ_n`: the first period whose self does it. -/
noncomputable def naiveDate (β : ℝ) : ℕ := Nat.find ⟨P.T, P.naiveDoes_T β⟩

/-- The time-consistent completion date `τ_tc`: the naive rule with `β = 1`
(with `β = 1` beliefs about future selves are correct, so naive = TC). -/
noncomputable def tcDate : ℕ := P.naiveDate 1

/-- The **sophisticate's** plan, by backward induction: `sophFrom β t` is the
period in which the task ends up done if it is not done before `t`. At the
deadline it is done; earlier, self `t` does it iff doing it now is weakly
preferred to the (correctly predicted) completion date of its successors.
This is Strotz consistent planning, the subgame-perfect equilibrium of the
game among the selves `t = 1, …, T` (with the paper's "do it when indifferent"
tie-break). -/
noncomputable def sophFrom (Q : Task) (β : ℝ) (t : ℕ) : ℕ :=
  if Q.T ≤ t then t
  else if Q.U β t (sophFrom Q β (t + 1)) ≤ Q.U β t t then t else sophFrom Q β (t + 1)
termination_by Q.T - t

/-- The sophisticate's completion date `τ_s`. -/
noncomputable def sophDate (β : ℝ) : ℕ := P.sophFrom β 1

/-- The backward-induction date is never before `t`. -/
theorem le_sophFrom (β : ℝ) (t : ℕ) : t ≤ P.sophFrom β t := by
  -- Induction on the number of periods left before the deadline.
  obtain ⟨k, hk⟩ : ∃ k, P.T - t = k := ⟨_, rfl⟩
  induction k generalizing t with
  | zero => rw [sophFrom, ite_eq_left (by omega)]
  | succ k ih =>
    rw [sophFrom]
    split_ifs with h1 h2
    · exact le_rfl
    · exact le_rfl
    · have := ih (t + 1) (by omega)
      omega

/-- Each sophisticated self best-responds to its successors' strategies (the
equilibrium condition, before the deadline). -/
theorem sophFrom_spec (β : ℝ) {t : ℕ} (ht : t < P.T) :
    (P.sophFrom β t = t ↔ P.U β t (P.sophFrom β (t + 1)) ≤ P.U β t t) := by
  rw [sophFrom, ite_eq_right (by omega)]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    -- `sophFrom (t+1) ≥ t+1 ≠ t`
    have : t + 1 ≤ P.sophFrom β (t + 1) := P.le_sophFrom β (t + 1)
    omega


/-- Before or at the deadline, the backward-induction date is at most `T`. -/
theorem sophFrom_le_T (β : ℝ) {t : ℕ} (ht : t ≤ P.T) : P.sophFrom β t ≤ P.T := by
  obtain ⟨k, hk⟩ : ∃ k, P.T - t = k := ⟨_, rfl⟩
  induction k generalizing t with
  | zero => rw [sophFrom, ite_eq_left (by omega)]; exact ht
  | succ k ih =>
    rw [sophFrom]
    split_ifs with h1 h2
    · exact ht
    · exact ht
    · exact ih (by omega) (by omega)

/-- If the naive self at `t` would do the task, so would the sophisticated self:
the sophisticate compares "now" with one particular later date, the naif with
all of them. -/
theorem sophFrom_eq_of_naiveDoes (β : ℝ) {t : ℕ} (h : P.NaiveDoes β t) :
    P.sophFrom β t = t := by
  obtain ⟨_, htT, hnow⟩ := h
  rcases hnow with rfl | hall
  · rw [sophFrom, ite_eq_left le_rfl]
  · rcases eq_or_lt_of_le htT with rfl | hlt
    · rw [sophFrom, ite_eq_left le_rfl]
    · rw [P.sophFrom_spec β hlt]
      apply hall
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self t) (P.le_sophFrom β (t + 1))
      · exact P.sophFrom_le_T β (by omega)

/-- If the plan from `t` stops at `t`, the plan from any earlier `t'` stops no
later than `t`. -/
theorem sophFrom_le_of_stop (β : ℝ) {t t' : ℕ} (htt : t' ≤ t) (hstop : P.sophFrom β t = t) :
    P.sophFrom β t' ≤ t := by
  obtain ⟨k, hk⟩ : ∃ k, t - t' = k := ⟨_, rfl⟩
  induction k generalizing t' with
  | zero => rw [show t' = t by omega]; exact hstop.le
  | succ k ih =>
    rw [sophFrom]
    split_ifs with h1 h2
    · omega
    · omega
    · exact ih (by omega) (by omega)

/-- **O'Donoghue–Rabin (1999), Proposition 2: sophisticates complete no later
than naifs**, `τ_s ≤ τ_n`, for every task and every `β` (both schedules). -/
theorem soph_le_naive (β : ℝ) : P.sophDate β ≤ P.naiveDate β := by
  classical
  have hspec := Nat.find_spec (⟨P.T, P.naiveDoes_T β⟩ : ∃ t, P.NaiveDoes β t)
  have hstop := P.sophFrom_eq_of_naiveDoes β hspec
  unfold sophDate naiveDate
  convert P.sophFrom_le_of_stop β hspec.1 hstop

/-- The TC date is the earliest period `τ` (in `1..T`) whose long-run value is
at least that of every later period. -/
theorem tcDate_spec : 1 ≤ P.tcDate ∧ P.tcDate ≤ P.T ∧
    ∀ τ, P.tcDate < τ → τ ≤ P.T → P.w τ ≤ P.w P.tcDate := by
  classical
  have h : P.NaiveDoes 1 P.tcDate := Nat.find_spec (⟨P.T, P.naiveDoes_T 1⟩ : ∃ t, _)
  refine ⟨h.1, h.2.1, ?_⟩
  intro τ h1 h2
  rcases h.2.2 with h' | h'
  · omega
  · have := h' τ h1 h2
    unfold U at this
    rw [ite_eq_right (by omega), ite_eq_left rfl] at this
    cases hs : P.schedule <;> simp only [hs, one_mul, w] at this ⊢ <;> linarith

/-- Minimality of the TC date: every earlier period `t ≥ 1` has some later
period with strictly higher long-run value. -/
theorem exists_better_of_lt_tcDate {t : ℕ} (h1 : 1 ≤ t) (ht : t < P.tcDate) :
    ∃ τ, t < τ ∧ τ ≤ P.T ∧ P.w t < P.w τ := by
  classical
  have hmin : ¬ P.NaiveDoes 1 t := Nat.find_min _ ht
  have hTt : t < P.T := lt_of_lt_of_le ht P.tcDate_spec.2.1
  by_contra hcon
  push Not at hcon
  apply hmin
  refine ⟨h1, hTt.le, Or.inr fun τ hτ hτT => ?_⟩
  have := hcon τ hτ hτT
  unfold U
  rw [ite_eq_right (by omega), ite_eq_left rfl]
  cases hs : P.schedule <;> simp only [w] at this ⊢ <;> linarith

/-- **O'Donoghue–Rabin (1999), Proposition 1 (immediate costs): naifs
procrastinate**, `τ_tc ≤ τ_n`, when costs are nonnegative and `0 < β ≤ 1`. -/
theorem tc_le_naive_of_immediateCosts (hs : P.schedule = .immediateCosts)
    (hc : ∀ τ, 0 ≤ P.c τ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    P.tcDate ≤ P.naiveDate β := by
  classical
  by_contra hlt
  push Not at hlt
  set t := P.naiveDate β with ht
  have hspec : P.NaiveDoes β t := Nat.find_spec (⟨P.T, P.naiveDoes_T β⟩ : ∃ t, P.NaiveDoes β t)
  obtain ⟨h1, _, hnow⟩ := hspec
  obtain ⟨τ, htτ, hτT, hbetter⟩ := P.exists_better_of_lt_tcDate h1 hlt
  rcases hnow with heq | hall
  · omega
  · have := hall τ htτ hτT
    unfold U at this
    rw [ite_eq_right (by omega), ite_eq_left rfl, hs] at this
    simp only [w] at this hbetter
    -- `β (v τ - c τ) ≤ β v t - c t ≤ β (v t - c t)` contradicts `w t < w τ`.
    have hct := hc t
    nlinarith

/-- **O'Donoghue–Rabin (1999), Proposition 1 (immediate rewards): naifs
preproperate**, `τ_n ≤ τ_tc`, when rewards are nonnegative and `0 ≤ β ≤ 1`. -/
theorem naive_le_tc_of_immediateRewards (hs : P.schedule = .immediateRewards)
    (hv : ∀ τ, 0 ≤ P.v τ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    P.naiveDate β ≤ P.tcDate := by
  classical
  obtain ⟨h1, hT, hbest⟩ := P.tcDate_spec
  apply Nat.find_min'
  refine ⟨h1, hT, Or.inr fun τ hτ hτT => ?_⟩
  have hw := hbest τ hτ hτT
  unfold U
  rw [ite_eq_right (by omega), ite_eq_left rfl, hs]
  simp only [w] at hw ⊢
  have hvt := hv P.tcDate
  nlinarith

/-! ### The paper's worked examples (β = 1/2, T = 4, values 3, 5, 8, 13) -/

/-- The "report" example: immediate costs `3, 5, 8, 13` in periods `1..4`,
equal rewards (normalized to 0). -/
def report : Task where
  T := 4
  one_le_T := by norm_num
  v := fun _ => 0
  c := fun τ => if τ = 1 then 3 else if τ = 2 then 5 else if τ = 3 then 8 else 13
  schedule := .immediateCosts

/-- The "movie" example: immediate rewards `3, 5, 8, 13`, no costs. -/
def movie : Task where
  T := 4
  one_le_T := by norm_num
  v := fun τ => if τ = 1 then 3 else if τ = 2 then 5 else if τ = 3 then 8 else 13
  c := fun _ => 0
  schedule := .immediateRewards

/-- Unfold `sophFrom` at a concrete date. -/
private theorem sophFrom_unfold (P : Task) (β : ℝ) (t : ℕ) :
    P.sophFrom β t = if P.T ≤ t then t
      else if P.U β t (P.sophFrom β (t + 1)) ≤ P.U β t t then t else P.sophFrom β (t + 1) := by
  rw [sophFrom]

/-- Report: the TC agent writes it in period 1, the sophisticate in period 2,
the naif procrastinates to the deadline. -/
theorem report_dates :
    report.tcDate = 1 ∧ report.sophDate (1 / 2) = 2 ∧ report.naiveDate (1 / 2) = 4 := by
  classical
  have s4 : report.sophFrom (1 / 2) 4 = 4 := by
    rw [sophFrom_unfold]; simp [report]
  have s3 : report.sophFrom (1 / 2) 3 = 4 := by
    rw [sophFrom_unfold, s4]; simp [report, U, w]; norm_num
  have s2 : report.sophFrom (1 / 2) 2 = 2 := by
    rw [sophFrom_unfold, s3]; simp [report, U, w]; norm_num
  have s1 : report.sophFrom (1 / 2) 1 = 2 := by
    rw [sophFrom_unfold, s2]; simp [report, U, w]; norm_num
  refine ⟨?_, s1, ?_⟩
  · unfold tcDate naiveDate
    rw [Nat.find_eq_iff]
    refine ⟨⟨le_rfl, by simp [report], Or.inr fun τ h1 h2 => ?_⟩, fun n hn => by
      intro h; exact absurd h.1 (by omega)⟩
    simp only [report] at h2
    simp only [report, U, w]
    interval_cases τ <;> norm_num
  · unfold naiveDate
    rw [Nat.find_eq_iff]
    refine ⟨report.naiveDoes_T _, fun n hn ⟨h1, _, h3⟩ => ?_⟩
    rcases h3 with h3 | h3
    · simp [report] at h3; omega
    · have := h3 (n + 1) (by omega) (by simp [report]; omega)
      simp only [report, U, w] at this
      interval_cases n <;> norm_num at this

/-- Movie: the TC agent waits for the best movie (period 4), the naif sees one
in period 3, the sophisticate already in period 1 (unravelling). -/
theorem movie_dates :
    movie.tcDate = 4 ∧ movie.sophDate (1 / 2) = 1 ∧ movie.naiveDate (1 / 2) = 3 := by
  classical
  have s4 : movie.sophFrom (1 / 2) 4 = 4 := by
    rw [sophFrom_unfold]; simp [movie]
  have s3 : movie.sophFrom (1 / 2) 3 = 3 := by
    rw [sophFrom_unfold, s4]; simp [movie, U, w]; norm_num
  have s2 : movie.sophFrom (1 / 2) 2 = 2 := by
    rw [sophFrom_unfold, s3]; simp [movie, U, w]; norm_num
  have s1 : movie.sophFrom (1 / 2) 1 = 1 := by
    rw [sophFrom_unfold, s2]; simp [movie, U, w]; norm_num
  refine ⟨?_, s1, ?_⟩
  · unfold tcDate naiveDate
    rw [Nat.find_eq_iff]
    refine ⟨movie.naiveDoes_T _, fun n hn ⟨h1, _, h3⟩ => ?_⟩
    rcases h3 with h3 | h3
    · simp [movie] at h3; omega
    · have := h3 4 (by simpa [movie] using hn) (by simp [movie])
      simp only [movie, U, w] at this
      interval_cases n <;> norm_num at this
  · unfold naiveDate
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by simp [movie], Or.inr fun τ h1 h2 => ?_⟩, fun n hn ⟨h1, _, h3⟩ => ?_⟩
    · simp only [movie] at h2
      simp only [movie, U, w]
      interval_cases τ; norm_num
    · rcases h3 with h3 | h3
      · simp [movie] at h3; omega
      · have := h3 4 (by omega) (by simp [movie])
        simp only [movie, U, w] at this
        interval_cases n <;> norm_num at this

end Task

end PresentBias

end Econ
