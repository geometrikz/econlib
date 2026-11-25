/-
# Logit choice as information-cost-regularized choice

References.
* F. Matějka and A. McKay (2015), "Rational Inattention to Discrete Choices:
  A New Foundation for the Multinomial Logit Model", *AER* 105(1). The key
  step of their Theorem 1: given the unconditional choice probabilities `P`,
  the rationally inattentive agent's choice probabilities in each state solve
  `max_p Σᵢ pᵢ vᵢ − λ KL(p ‖ P)`, whose solution is the
  **generalized logit** `pᵢ = Pᵢ e^{vᵢ/λ} / Σⱼ Pⱼ e^{vⱼ/λ}`.
* S. Anderson, A. de Palma and J.-F. Thisse (1988), "A Representative
  Consumer Theory of the Logit Model", *Rev. Econ. Stud.*: with uniform `P`
  this is entropy-regularized choice, and the solution is the multinomial
  logit (softmax).

**What is formalized.** The Gibbs variational principle in the form the
economics uses: for actions `ι` (finite, nonempty), payoffs `v`, information
cost `λ > 0` and a full-support default `P`,
* `generalizedLogit_optimal`: every probability vector `p` gets at most the
  value of the generalized logit, which equals `λ log Σⱼ Pⱼ e^{vⱼ/λ}`;
* `eq_generalizedLogit_of_optimal`: the maximizer is unique;
* `softmax_optimal`: the multinomial-logit special case, objective
  `Σ pᵢ vᵢ + λ H(p)` with Shannon entropy `H`.

**Scope (important).** This is the *per-state step* of Matějka–McKay, for
a fixed, exogenous, full-support `P`. It is **not** yet their theorem
"rational inattention ⟹ generalized logit": that also needs (i) mutual
information written as `min_P E_v KL(p(·|v) ‖ P)`, attained at the marginal,
(ii) the joint problem over state-contingent rules, and (iii) the fixed point
`Pᵢ = E_v[pᵢ(v)]`; MM also allow actions never chosen (`Pᵢ = 0`), which the
hypothesis `∀ i, 0 < P i` rules out. Those steps are in `RationalInattention.lean`
(Theorem 1, zero-probability actions) and `RISymmetric.lean` (the optimal marginal).
`P` need not sum to one here (only positivity is used).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

namespace Logit

open Finset Real

variable {ι : Type*} [Fintype ι]

/-- The information-cost-regularized objective `Σ pᵢ vᵢ − λ KL(p ‖ P)`, with
`KL(p ‖ P) = Σ (pᵢ log pᵢ − pᵢ log Pᵢ)` (Lean's `log 0 = 0` gives the usual
convention `0 log 0 = 0`). -/
noncomputable def objective (lam : ℝ) (P v p : ι → ℝ) : ℝ :=
  ∑ i, p i * v i - lam * ∑ i, (p i * log (p i) - p i * log (P i))

/-- The partition function `Z = Σⱼ Pⱼ e^{vⱼ/λ}`. -/
noncomputable def Z (lam : ℝ) (P v : ι → ℝ) : ℝ := ∑ j, P j * exp (v j / lam)

/-- The generalized logit choice probabilities `Pᵢ e^{vᵢ/λ} / Z`. -/
noncomputable def generalizedLogit (lam : ℝ) (P v : ι → ℝ) (i : ι) : ℝ :=
  P i * exp (v i / lam) / Z lam P v

/-- A probability vector. -/
def IsProb (p : ι → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

variable {lam : ℝ} {P v : ι → ℝ}

theorem Z_pos [Nonempty ι] (hP : ∀ i, 0 < P i) : 0 < Z lam P v :=
  sum_pos (fun j _ => mul_pos (hP j) (exp_pos _)) univ_nonempty

theorem generalizedLogit_pos [Nonempty ι] (hP : ∀ i, 0 < P i) (i : ι) :
    0 < generalizedLogit lam P v i :=
  div_pos (mul_pos (hP i) (exp_pos _)) (Z_pos hP)

theorem generalizedLogit_isProb [Nonempty ι] (hP : ∀ i, 0 < P i) :
    IsProb (generalizedLogit lam P v) := by
  refine ⟨fun i => (generalizedLogit_pos hP i).le, ?_⟩
  unfold generalizedLogit
  rw [← sum_div]
  exact div_self (Z_pos hP).ne'

/-- `log` of the generalized logit probability. -/
theorem log_generalizedLogit [Nonempty ι] (hP : ∀ i, 0 < P i) (i : ι) :
    log (generalizedLogit lam P v i) = log (P i) + v i / lam - log (Z lam P v) := by
  unfold generalizedLogit
  rw [log_div (mul_pos (hP i) (exp_pos _)).ne' (Z_pos hP).ne',
    log_mul (hP i).ne' (exp_pos _).ne', log_exp]

/-- The per-action inequality behind Gibbs' principle:
`pᵢ vᵢ − λ(pᵢ log pᵢ − pᵢ log Pᵢ) ≤ λ (qᵢ − pᵢ) + λ pᵢ log Z`, with equality
iff `pᵢ = qᵢ` (`q` the generalized logit). -/
theorem term_le [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i) {p : ι → ℝ} (i : ι)
    (hp : 0 ≤ p i) :
    p i * v i - lam * (p i * log (p i) - p i * log (P i)) ≤
      lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v) := by
  set q := generalizedLogit lam P v i
  have hq : 0 < q := generalizedLogit_pos hP i
  rcases eq_or_lt_of_le hp with h0 | hpos
  · rw [← h0]; simp; positivity
  · have hv : v i = lam * (log q - log (P i) + log (Z lam P v)) := by
      rw [log_generalizedLogit hP]; field_simp; ring
    have hlog : log (q / p i) ≤ q / p i - 1 := log_le_sub_one_of_pos (div_pos hq hpos)
    rw [log_div hq.ne' hpos.ne'] at hlog
    have key : p i * (log q - log (p i)) ≤ q - p i := by
      have e : p i * (q / p i - 1) = q - p i := by field_simp
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      rwa [e] at this
    rw [hv]
    nlinarith

/-- Strict version of `term_le` when `pᵢ ≠ qᵢ`. -/
theorem term_lt [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i) {p : ι → ℝ} (i : ι)
    (hp : 0 ≤ p i) (hne : p i ≠ generalizedLogit lam P v i) :
    p i * v i - lam * (p i * log (p i) - p i * log (P i)) <
      lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v) := by
  set q := generalizedLogit lam P v i
  have hq : 0 < q := generalizedLogit_pos hP i
  rcases eq_or_lt_of_le hp with h0 | hpos
  · rw [← h0]; simp; positivity
  · have hv : v i = lam * (log q - log (P i) + log (Z lam P v)) := by
      rw [log_generalizedLogit hP]; field_simp; ring
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

/-- The value of the generalized logit is `λ log Z`. -/
theorem objective_generalizedLogit [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i) :
    objective lam P v (generalizedLogit lam P v) = lam * log (Z lam P v) := by
  unfold objective
  have h : ∀ i, generalizedLogit lam P v i * v i - lam * (generalizedLogit lam P v i *
      log (generalizedLogit lam P v i) - generalizedLogit lam P v i * log (P i)) =
      lam * log (Z lam P v) * generalizedLogit lam P v i := by
    intro i
    rw [log_generalizedLogit hP]
    field_simp
    ring
  rw [mul_sum, ← sum_sub_distrib, sum_congr rfl fun i _ => h i, ← mul_sum,
    (generalizedLogit_isProb hP).2, mul_one]

/-- **Generalized logit is optimal** (Gibbs variational principle;
Matějka–McKay 2015). -/
theorem generalizedLogit_optimal [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i)
    {p : ι → ℝ} (hp : IsProb p) :
    objective lam P v p ≤ objective lam P v (generalizedLogit lam P v) := by
  rw [objective_generalizedLogit hlam hP]
  unfold objective
  rw [mul_sum, ← sum_sub_distrib]
  calc ∑ i, (p i * v i - lam * (p i * log (p i) - p i * log (P i)))
      ≤ ∑ i, (lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v)) :=
        sum_le_sum fun i _ => term_le hlam hP i (hp.1 i)
    _ = lam * log (Z lam P v) := by
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, (generalizedLogit_isProb hP).2, hp.2,
          ← sum_mul, ← mul_sum, hp.2]
        ring

/-- **The optimum is unique**: any probability vector attaining the optimal
value is the generalized logit. -/
theorem eq_generalizedLogit_of_optimal [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i)
    {p : ι → ℝ} (hp : IsProb p)
    (hopt : objective lam P v (generalizedLogit lam P v) ≤ objective lam P v p) :
    p = generalizedLogit lam P v := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hne
  rw [objective_generalizedLogit hlam hP] at hopt
  unfold objective at hopt
  rw [mul_sum, ← sum_sub_distrib] at hopt
  have hlt : ∑ i, (p i * v i - lam * (p i * log (p i) - p i * log (P i))) <
      ∑ i, (lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v)) :=
    sum_lt_sum (fun i _ => term_le hlam hP i (hp.1 i))
      ⟨i₀, mem_univ _, term_lt hlam hP i₀ (hp.1 i₀) hi₀⟩
  have hval : ∑ i, (lam * (generalizedLogit lam P v i - p i) + lam * p i * log (Z lam P v)) =
      lam * log (Z lam P v) := by
    rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, (generalizedLogit_isProb hP).2, hp.2,
      ← sum_mul, ← mul_sum, hp.2]
    ring
  linarith

/-- Shannon entropy `H(p) = −Σ pᵢ log pᵢ`. -/
noncomputable def entropy (p : ι → ℝ) : ℝ := -∑ i, p i * log (p i)

/-- Multinomial logit (softmax) `e^{vᵢ/λ} / Σⱼ e^{vⱼ/λ}`. -/
noncomputable def softmax (lam : ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  exp (v i / lam) / ∑ j, exp (v j / lam)

/-- With a uniform default (`P ≡ 1`; any constant works), the generalized logit
is the standard multinomial logit. -/
theorem generalizedLogit_const_eq_softmax (lam : ℝ) (v : ι → ℝ) :
    generalizedLogit lam (fun _ => 1) v = softmax lam v := by
  funext i; simp [softmax, generalizedLogit, Z]

/-- **Logit = entropy-regularized choice** (Anderson–de Palma–Thisse): softmax
maximizes `Σ pᵢ vᵢ + λ H(p)` over probability vectors, uniquely. -/
theorem softmax_optimal [Nonempty ι] (hlam : 0 < lam) {p : ι → ℝ} (hp : IsProb p) :
    IsProb (softmax lam v) ∧
      ∑ i, p i * v i + lam * entropy p ≤ ∑ i, softmax lam v i * v i + lam * entropy (softmax lam v) ∧
      (∑ i, softmax lam v i * v i + lam * entropy (softmax lam v) ≤ ∑ i, p i * v i + lam * entropy p →
        p = softmax lam v) := by
  have hP : ∀ _ : ι, (0 : ℝ) < 1 := fun _ => one_pos
  have hs : softmax lam v = generalizedLogit lam (fun _ => 1) v :=
    (generalizedLogit_const_eq_softmax lam v).symm
  have hobj : ∀ p : ι → ℝ, objective lam (fun _ => 1) v p = ∑ i, p i * v i + lam * entropy p := by
    intro p; simp [objective, entropy]; ring
  rw [hs, ← hobj, ← hobj]
  exact ⟨generalizedLogit_isProb hP, generalizedLogit_optimal hlam hP hp,
    eq_generalizedLogit_of_optimal hlam hP hp⟩

end Logit

end Econ
