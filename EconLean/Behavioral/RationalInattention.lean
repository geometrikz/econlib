/-
# Rational inattention and the generalized logit (Matějka–McKay 2015)

References.
* C. Sims (2003), "Implications of Rational Inattention", *JME* 50(3):
  information costs proportional to Shannon mutual information.
* F. Matějka and A. McKay (2015), "Rational Inattention to Discrete Choices:
  A New Foundation for the Multinomial Logit Model", *AER* 105(1), Theorem 1.

**The model.** Finitely many states `ω ∈ Ω` with prior `g ω > 0`, finitely
many actions `i ∈ ι`, payoffs `v ω i`. The agent picks a **choice rule**
`p ω i = Prob(choose i | state ω)` (a probability vector for each state).
Its **marginal** (unconditional choice probabilities) is
`P i = Σ_ω g ω p ω i`. Information costs `λ` times the **mutual information**
between state and action,

    I(p) = Σ_ω g ω Σ_i p ω i (log p ω i − log P i),

and the agent maximizes `Σ_ω g ω Σ_i p ω i v ω i − λ I(p)`.

**Matějka–McKay, Theorem 1.** At an optimum, in every state the choice
probabilities are the *generalized logit* with respect to the rule's own
marginal:

    p ω i = P i e^{v ω i / λ} / Σ_j P j e^{v ω j / λ}.

Proof idea (formalized below): for *any* full-support probability vector `Q`,
`Σ_ω g ω KL(p ω ‖ Q) = I(p) + KL(P ‖ Q) ≥ I(p)` (`avgKL_eq`,
`mutualInfo_le_avgKL`), with equality at `Q = P`. So replacing the rule in
one state by the per-state optimum for the fixed default `P` (the Gibbs
problem of `Logit.lean`) can only raise the objective, strictly unless the
rule already was that optimum.

Actions never chosen (`P i = 0`) are allowed, as in MM: for them both sides
of the formula are `0`. For that case the per-state Gibbs bound is redone
for defaults that may vanish (`objective_le0`, `eq_gl_of_optimal0`).
**Not formalized:** existence of an optimal rule (it exists by compactness)
and MM's characterization of the optimal marginal itself.
-/
module

public import EconLean.Behavioral.Logit

@[expose] public section

namespace Econ

namespace RationalInattention

open Finset Real Logit

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- Kullback–Leibler divergence `KL(p ‖ q) = Σ pᵢ (log pᵢ − log qᵢ)`
(meaningful when `q > 0`; `0 log 0 = 0` by Lean's `log 0 = 0`). -/
noncomputable def kl (p q : ι → ℝ) : ℝ := ∑ i, (p i * log (p i) - p i * log (q i))

/-- **Gibbs' inequality**: `KL(p ‖ q) ≥ 0` for probability vectors, `q > 0`,
with equality only if `p = q`. -/
theorem kl_nonneg [Nonempty ι] {p q : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hqpos : ∀ i, 0 < q i) : 0 ≤ kl p q := by
  have h := generalizedLogit_optimal (lam := 1) (v := fun _ => 0) one_pos hqpos hp
  rw [objective_generalizedLogit one_pos hqpos] at h
  have hZ : Z 1 q (fun _ => 0) = 1 := by simp [Z, hq.2]
  simp only [objective, hZ, log_one, mul_zero, sum_const_zero, zero_sub, one_mul] at h
  unfold kl; linarith

theorem kl_eq_zero_iff [Nonempty ι] {p q : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hqpos : ∀ i, 0 < q i) : kl p q = 0 ↔ p = q := by
  have hgl : generalizedLogit 1 q (fun _ => 0) = q := by
    funext i; simp [generalizedLogit, Z, hq.2]
  constructor
  · intro h0
    rw [← hgl]
    apply eq_generalizedLogit_of_optimal one_pos hqpos hp
    rw [objective_generalizedLogit one_pos hqpos]
    have hZ : Z 1 q (fun _ => 0) = 1 := by simp [Z, hq.2]
    simp only [objective, hZ, log_one, mul_zero, sum_const_zero, zero_sub, one_mul]
    unfold kl at h0; linarith
  · rintro rfl; simp [kl]

/-- A choice rule: a probability vector over actions in every state. -/
def IsRule (p : Ω → ι → ℝ) : Prop := ∀ ω, IsProb (p ω)

/-- A prior over states with full support. -/
def IsPrior (g : Ω → ℝ) : Prop := (∀ ω, 0 < g ω) ∧ ∑ ω, g ω = 1

/-- The marginal (unconditional) choice probabilities `P i = Σ_ω g ω p ω i`. -/
def marginal (g : Ω → ℝ) (p : Ω → ι → ℝ) (i : ι) : ℝ := ∑ ω, g ω * p ω i

theorem marginal_isProb {g : Ω → ℝ} (hg : IsPrior g) {p : Ω → ι → ℝ} (hp : IsRule p) :
    IsProb (marginal g p) := by
  refine ⟨fun i => sum_nonneg fun ω _ => mul_nonneg (hg.1 ω).le ((hp ω).1 i), ?_⟩
  unfold marginal
  rw [sum_comm]
  simp_rw [← mul_sum, (hp _).2, mul_one, hg.2]

/-- Shannon mutual information between state and action under rule `p`. -/
noncomputable def mutualInfo (g : Ω → ℝ) (p : Ω → ι → ℝ) : ℝ :=
  ∑ ω, g ω * kl (p ω) (marginal g p)

/-- Average divergence of the state-contingent choice from a default `Q`. -/
noncomputable def avgKL (g : Ω → ℝ) (p : Ω → ι → ℝ) (Q : ι → ℝ) : ℝ :=
  ∑ ω, g ω * kl (p ω) Q

/-- **Decomposition**: `Σ_ω g ω KL(p ω ‖ Q) = I(p) + KL(P ‖ Q)`. -/
theorem avgKL_eq (g : Ω → ℝ) (p : Ω → ι → ℝ) (Q : ι → ℝ) :
    avgKL g p Q = mutualInfo g p + kl (marginal g p) Q := by
  set m := marginal g p with hm
  have key : avgKL g p Q - mutualInfo g p = kl m Q := by
    unfold avgKL mutualInfo
    rw [← sum_sub_distrib]
    -- state by state, the difference is `Σᵢ g ω p ω i (log mᵢ − log Qᵢ)`
    have h1 : ∀ ω, g ω * kl (p ω) Q - g ω * kl (p ω) m =
        ∑ i, g ω * p ω i * (log (m i) - log (Q i)) := by
      intro ω
      unfold kl
      rw [← mul_sub, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [sum_congr rfl fun ω _ => h1 ω, sum_comm]
    unfold kl
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_mul]
    change m i * _ = _
    ring
  linarith

/-- **Mutual information is the smallest average divergence**: the marginal
is the best default. -/
theorem mutualInfo_le_avgKL [Nonempty ι] {g : Ω → ℝ} (hg : IsPrior g) {p : Ω → ι → ℝ}
    (hp : IsRule p) {Q : ι → ℝ} (hQ : IsProb Q) (hQpos : ∀ i, 0 < Q i) :
    mutualInfo g p ≤ avgKL g p Q := by
  rw [avgKL_eq]
  linarith [kl_nonneg (marginal_isProb hg hp) hQ hQpos]

/-- The rational-inattention objective: expected payoff minus `λ` times
mutual information. -/
noncomputable def riObjective (lam : ℝ) (g : Ω → ℝ) (v : Ω → ι → ℝ) (p : Ω → ι → ℝ) : ℝ :=
  ∑ ω, g ω * ∑ i, p ω i * v ω i - lam * mutualInfo g p

/-- An optimal rule: it maximizes the RI objective among all choice rules. -/
def IsOptimalRule (lam : ℝ) (g : Ω → ℝ) (v : Ω → ι → ℝ) (p : Ω → ι → ℝ) : Prop :=
  IsRule p ∧ ∀ p', IsRule p' → riObjective lam g v p' ≤ riObjective lam g v p

/-- The RI objective written state by state with a default `Q`, as in the
per-state Gibbs problem: `Σ_ω g ω · objective(Q, v ω, p ω)`. -/
theorem sum_objective_eq (lam : ℝ) (g : Ω → ℝ) (v : Ω → ι → ℝ) (p : Ω → ι → ℝ)
    (Q : ι → ℝ) :
    ∑ ω, g ω * objective lam Q (v ω) (p ω) =
      ∑ ω, g ω * ∑ i, p ω i * v ω i - lam * avgKL g p Q := by
  have h : ∀ ω, objective lam Q (v ω) (p ω) = ∑ i, p ω i * v ω i - lam * kl (p ω) Q :=
    fun ω => rfl
  rw [avgKL, Finset.mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun ω _ => by rw [h]; ring

/-- Actions never chosen unconditionally are never chosen in any state (and
the generalized-logit formula also gives `0` for them). -/
theorem rule_eq_zero_of_marginal_eq_zero {g : Ω → ℝ} (hg : IsPrior g) {p : Ω → ι → ℝ}
    (hp : IsRule p) {i : ι} (h : marginal g p i = 0) (ω : Ω) : p ω i = 0 := by
  have hnn : ∀ ω ∈ univ, 0 ≤ g ω * p ω i := fun ω _ => mul_nonneg (hg.1 ω).le ((hp ω).1 i)
  have := (sum_eq_zero_iff_of_nonneg hnn).1 h ω (mem_univ _)
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (hg.1 ω).ne'
  · exact h1

/-! ### The Gibbs problem with a default that may have zeros

Matějka–McKay allow actions that are never chosen. The default `P` (the
marginal) may then vanish at some actions, and the relevant choices `p`
put no weight where `P` does (`p ≪ P`). We redo the per-state Gibbs bound
under these weaker hypotheses: `P ≥ 0` and `Z > 0`. -/

section Gibbs0

variable {lam : ℝ} {P v : ι → ℝ}

theorem gl_nonneg (hP0 : ∀ i, 0 ≤ P i) (hZ : 0 < Z lam P v) (i : ι) :
    0 ≤ generalizedLogit lam P v i :=
  div_nonneg (mul_nonneg (hP0 i) (exp_pos _).le) hZ.le

theorem gl_eq_zero {i : ι} (h : P i = 0) : generalizedLogit lam P v i = 0 := by
  simp [generalizedLogit, h]

theorem gl_isProb (hP0 : ∀ i, 0 ≤ P i) (hZ : 0 < Z lam P v) : IsProb (generalizedLogit lam P v) :=
  ⟨gl_nonneg hP0 hZ, by unfold generalizedLogit; rw [← sum_div]; exact div_self hZ.ne'⟩

theorem log_gl (hZ : 0 < Z lam P v) {i : ι} (hPi : 0 < P i) :
    log (generalizedLogit lam P v i) = log (P i) + v i / lam - log (Z lam P v) := by
  unfold generalizedLogit
  rw [log_div (mul_pos hPi (exp_pos _)).ne' hZ.ne', log_mul hPi.ne' (exp_pos _).ne', log_exp]

/-- Per-action Gibbs bound when `P` may vanish (and `p` vanishes there too). -/
theorem term_le0 (hlam : 0 < lam) (hZ : 0 < Z lam P v) {p : ι → ℝ} (i : ι) (hP0 : 0 ≤ P i)
    (hp : 0 ≤ p i) (habs : P i = 0 → p i = 0) :
    p i * v i - lam * (p i * log (p i) - p i * log (P i)) ≤
      lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v) := by
  rcases eq_or_lt_of_le hP0 with h0 | hPi
  · rw [habs h0.symm, gl_eq_zero h0.symm]; simp
  set q := generalizedLogit lam P v i
  have hq : 0 < q := div_pos (mul_pos hPi (exp_pos _)) hZ
  rcases eq_or_lt_of_le hp with hp0 | hpos
  · rw [← hp0]; simp; positivity
  · have hv : v i = lam * (log q - log (P i) + log (Z lam P v)) := by
      rw [log_gl hZ hPi]; field_simp; ring
    have hlog : log (q / p i) ≤ q / p i - 1 := log_le_sub_one_of_pos (div_pos hq hpos)
    rw [log_div hq.ne' hpos.ne'] at hlog
    have key : p i * (log q - log (p i)) ≤ q - p i := by
      have e : p i * (q / p i - 1) = q - p i := by field_simp
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      rwa [e] at this
    rw [hv]
    nlinarith

theorem term_lt0 (hlam : 0 < lam) (hZ : 0 < Z lam P v) {p : ι → ℝ} (i : ι) (hP0 : 0 ≤ P i)
    (hp : 0 ≤ p i) (habs : P i = 0 → p i = 0) (hne : p i ≠ generalizedLogit lam P v i) :
    p i * v i - lam * (p i * log (p i) - p i * log (P i)) <
      lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v) := by
  rcases eq_or_lt_of_le hP0 with h0 | hPi
  · exact absurd (by rw [habs h0.symm, gl_eq_zero h0.symm]) hne
  set q := generalizedLogit lam P v i
  have hq : 0 < q := div_pos (mul_pos hPi (exp_pos _)) hZ
  rcases eq_or_lt_of_le hp with hp0 | hpos
  · rw [← hp0]; simp; positivity
  · have hv : v i = lam * (log q - log (P i) + log (Z lam P v)) := by
      rw [log_gl hZ hPi]; field_simp; ring
    have hne' : q / p i ≠ 1 := by
      intro h; apply hne; field_simp at h; exact h.symm
    have hlog : log (q / p i) < q / p i - 1 := log_lt_sub_one_of_pos (div_pos hq hpos) hne'
    rw [log_div hq.ne' hpos.ne'] at hlog
    have key : p i * (log q - log (p i)) < q - p i := by
      have e : p i * (q / p i - 1) = q - p i := by field_simp
      have := mul_lt_mul_of_pos_left hlog hpos
      rwa [e] at this
    rw [hv]
    nlinarith

/-- Summed bound: `objective(p) ≤ λ log Z`, for `p ≪ P`. -/
theorem objective_le0 (hlam : 0 < lam) (hP0 : ∀ i, 0 ≤ P i) (hZ : 0 < Z lam P v) {p : ι → ℝ}
    (hp : IsProb p) (habs : ∀ i, P i = 0 → p i = 0) :
    objective lam P v p ≤ lam * log (Z lam P v) := by
  unfold objective
  rw [mul_sum, ← sum_sub_distrib]
  calc ∑ i, (p i * v i - lam * (p i * log (p i) - p i * log (P i)))
      ≤ ∑ i, (lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v)) :=
        sum_le_sum fun i _ => term_le0 hlam hZ i (hP0 i) (hp.1 i) (habs i)
    _ = lam * log (Z lam P v) := by
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, (gl_isProb hP0 hZ).2, hp.2,
          ← sum_mul, ← mul_sum, hp.2]
        ring

/-- The generalized logit attains `λ log Z`. -/
theorem objective_gl0 (hlam : 0 < lam) (hP0 : ∀ i, 0 ≤ P i) (hZ : 0 < Z lam P v) :
    objective lam P v (generalizedLogit lam P v) = lam * log (Z lam P v) := by
  unfold objective
  have h : ∀ i, generalizedLogit lam P v i * v i - lam * (generalizedLogit lam P v i *
      log (generalizedLogit lam P v i) - generalizedLogit lam P v i * log (P i)) =
      lam * log (Z lam P v) * generalizedLogit lam P v i := by
    intro i
    rcases eq_or_lt_of_le (hP0 i) with h0 | hPi
    · rw [gl_eq_zero h0.symm]; ring
    · rw [log_gl hZ hPi]; field_simp; ring
  rw [mul_sum, ← sum_sub_distrib, sum_congr rfl fun i _ => h i, ← mul_sum,
    (gl_isProb hP0 hZ).2, mul_one]

/-- Uniqueness: a `p ≪ P` attaining `λ log Z` is the generalized logit. -/
theorem eq_gl_of_optimal0 (hlam : 0 < lam) (hP0 : ∀ i, 0 ≤ P i) (hZ : 0 < Z lam P v)
    {p : ι → ℝ} (hp : IsProb p) (habs : ∀ i, P i = 0 → p i = 0)
    (hopt : lam * log (Z lam P v) ≤ objective lam P v p) : p = generalizedLogit lam P v := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hne
  unfold objective at hopt
  rw [mul_sum, ← sum_sub_distrib] at hopt
  have hlt : ∑ i, (p i * v i - lam * (p i * log (p i) - p i * log (P i))) <
      ∑ i, (lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v)) :=
    sum_lt_sum (fun i _ => term_le0 hlam hZ i (hP0 i) (hp.1 i) (habs i))
      ⟨i₀, mem_univ _, term_lt0 hlam hZ i₀ (hP0 i₀) (hp.1 i₀) (habs i₀) hi₀⟩
  have hval : ∑ i, (lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v)) =
      lam * log (Z lam P v) := by
    rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, (gl_isProb hP0 hZ).2, hp.2,
      ← sum_mul, ← mul_sum, hp.2]
    ring
  linarith

/-- Gibbs' inequality when `q` may vanish but `p ≪ q`. -/
theorem kl_nonneg0 {p q : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
    (habs : ∀ i, q i = 0 → p i = 0) : 0 ≤ kl p q := by
  have hZ : Z 1 q (fun _ => 0) = 1 := by simp [Z, hq.2]
  have h := objective_le0 (lam := 1) (v := fun _ => 0) one_pos hq.1 (by rw [hZ]; exact one_pos)
    hp habs
  simp only [objective, hZ, log_one, mul_zero, sum_const_zero, zero_sub, one_mul] at h
  unfold kl; linarith

end Gibbs0

/-- `Z > 0` whenever the default is a probability vector. -/
theorem Z_pos_of_isProb {lam : ℝ} {P v : ι → ℝ} (hP : IsProb P) : 0 < Z lam P v := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < P j := by
    by_contra h
    push Not at h
    have : ∑ i, P i ≤ 0 := sum_nonpos fun i _ => h i
    linarith [hP.2]
  exact lt_of_lt_of_le (mul_pos hj (exp_pos _))
    (single_le_sum (f := fun i => P i * exp (v i / lam))
      (fun i _ => mul_nonneg (hP.1 i) (exp_pos _).le) (mem_univ j))

/-- **Matějka–McKay (2015), Theorem 1.** If `p` is an optimal rule with
marginal `P`, then in every state
`p ω i = P i e^{v ω i / λ} / Σⱼ P j e^{v ω j / λ}` (actions with `P i = 0` get
probability `0` on both sides). -/
theorem optimal_is_generalizedLogit [DecidableEq Ω] {lam : ℝ} (hlam : 0 < lam)
    {g : Ω → ℝ} (hg : IsPrior g) {v : Ω → ι → ℝ} {p : Ω → ι → ℝ}
    (hopt : IsOptimalRule lam g v p) (ω₀ : Ω) :
    p ω₀ = generalizedLogit lam (marginal g p) (v ω₀) := by
  set P := marginal g p
  set q := generalizedLogit lam P (v ω₀)
  have hPprob : IsProb P := marginal_isProb hg hopt.1
  have hZ : ∀ ω, 0 < Z lam P (v ω) := fun ω => Z_pos_of_isProb hPprob
  -- `p ω ≪ P` in every state
  have habs : ∀ ω i, P i = 0 → p ω i = 0 := fun ω i h =>
    rule_eq_zero_of_marginal_eq_zero hg hopt.1 h ω
  by_contra hne
  -- The deviation: use `q` in state `ω₀`, keep `p` elsewhere.
  set p' : Ω → ι → ℝ := Function.update p ω₀ q
  have hp' : IsRule p' := by
    intro ω
    by_cases h : ω = ω₀
    · subst h; simpa [p'] using gl_isProb hPprob.1 (hZ ω)
    · simpa [p', h] using hopt.1 ω
  have habs' : ∀ ω i, P i = 0 → p' ω i = 0 := by
    intro ω i h
    by_cases hω : ω = ω₀
    · subst hω; simp only [p', Function.update_self]; exact gl_eq_zero h
    · simp only [p', Function.update_of_ne hω]; exact habs ω i h
  -- The deviation's marginal also vanishes where `P` does.
  have hmarg' : ∀ i, P i = 0 → marginal g p' i = 0 := fun i h =>
    sum_eq_zero fun ω _ => by rw [habs' ω i h, mul_zero]
  -- Objective of `p` = per-state objectives with default `P`.
  have hp_eq : riObjective lam g v p = ∑ ω, g ω * objective lam P (v ω) (p ω) := by
    rw [sum_objective_eq]; rfl
  -- Objective of `p'` ≥ per-state objectives with default `P` (`I ≤ avgKL`).
  have hp'_ge : ∑ ω, g ω * objective lam P (v ω) (p' ω) ≤ riObjective lam g v p' := by
    rw [sum_objective_eq, riObjective, avgKL_eq]
    have := kl_nonneg0 (marginal_isProb hg hp') hPprob hmarg'
    nlinarith
  -- Per-state comparison: equal off `ω₀`, strictly better at `ω₀`.
  have hstrict : ∑ ω, g ω * objective lam P (v ω) (p ω) <
      ∑ ω, g ω * objective lam P (v ω) (p' ω) := by
    apply sum_lt_sum
    · intro ω _
      by_cases h : ω = ω₀
      · subst h
        simp only [p', Function.update_self]
        rw [objective_gl0 hlam hPprob.1 (hZ ω)]
        exact mul_le_mul_of_nonneg_left
          (objective_le0 hlam hPprob.1 (hZ ω) (hopt.1 ω) (habs ω)) (hg.1 ω).le
      · simp [p', h]
    · refine ⟨ω₀, mem_univ _, ?_⟩
      simp only [p', Function.update_self]
      apply mul_lt_mul_of_pos_left _ (hg.1 ω₀)
      rw [objective_gl0 hlam hPprob.1 (hZ ω₀)]
      rcases lt_or_eq_of_le (objective_le0 hlam hPprob.1 (hZ ω₀) (hopt.1 ω₀) (habs ω₀)) with
        h | h
      · exact h
      · exact absurd (eq_gl_of_optimal0 hlam hPprob.1 (hZ ω₀) (hopt.1 ω₀) (habs ω₀) h.ge) hne
  have := hopt.2 p' hp'
  linarith

/-- **Uniform marginal ⟹ multinomial logit.** If the optimal rule's marginal is
uniform, choice in every state is the standard logit (softmax) with
temperature `λ`. -/
theorem optimal_is_softmax_of_uniform [Nonempty ι] [DecidableEq Ω] {lam : ℝ} (hlam : 0 < lam)
    {g : Ω → ℝ} (hg : IsPrior g) {v : Ω → ι → ℝ} {p : Ω → ι → ℝ}
    (hopt : IsOptimalRule lam g v p) {c : ℝ} (hunif : ∀ i, marginal g p i = c)
    (ω : Ω) : p ω = softmax lam (v ω) := by
  have hc : 0 < c := by
    have h1 := (marginal_isProb hg hopt.1).2
    simp only [hunif, sum_const, card_univ, nsmul_eq_mul] at h1
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    nlinarith
  rw [optimal_is_generalizedLogit hlam hg hopt ω]
  funext i
  simp only [generalizedLogit, Z, softmax, hunif, ← mul_sum]
  field_simp

end RationalInattention

end Econ
