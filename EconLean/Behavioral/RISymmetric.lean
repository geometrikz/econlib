/-
# Rational inattention: the optimal marginal and symmetric problems

References. F. Matějka and A. McKay (2015), "Rational Inattention to Discrete
Choices: A New Foundation for the Multinomial Logit Model", *AER* 105(1),
Lemma 2 and their result on a-priori symmetric options (the section deriving
the multinomial logit);
A. Caplin and M. Dean (2013), "Behavioral Implications of Rational
Inattention with Shannon Entropy", NBER WP 19318 (the posterior-free problem).

Builds on `RationalInattention.lean` (model, Theorem 1, existence).

**The problem in unconditional probabilities.** For a probability vector `P`
over actions let

    F(P) = Σ_ω g ω · λ log Σ_i P i e^{v ω i / λ}      (`valueF`).

* `riObjective_le_valueF`: every rule `p` earns at most `F` of its own
  marginal (per-state Gibbs bound with default `P`).
* `valueF_le_riObjective_gl`: the generalized-logit rule built on any `P`
  earns at least `F(P)` (mutual information is at most the average
  divergence from `P`).
* `isOptimalRule_gl_of_isMax` (**MM Lemma 2, sufficiency**): if `P` maximizes
  `F` over probability vectors then the generalized-logit rule built on `P` is
  optimal. So the RI problem reduces to maximizing the concave function `F`.
* `valueF_avg_ge`: equal-weight Jensen for `F` (concavity of `log`), which is
  all the averaging argument needs.

**Symmetric problems.** A permutation `τ` of actions is a *symmetry*
(`IsSymmetry`) if some permutation `ρ` of states preserves the prior and maps
payoffs accordingly: `g (ρ ω) = g ω` and `v (ρ ω) (τ i) = v ω i`.
* `isSymmetry_mul`: symmetries compose.
* `valueF_comp`: `F` is invariant under symmetries.
* `softmax_optimal_of_symmetric` (**MM: symmetric problems give the
  multinomial logit**): if a set `S` of symmetries is closed under composition
  and acts transitively on actions, the plain logit (softmax) rule
  `p ω i = e^{v ω i / λ} / Σ_j e^{v ω j / λ}` is optimal. Proof: averaging any
  marginal over `S` gives the uniform vector and, by concavity and invariance,
  does not lower `F`. `softmax_optimal_of_transitive` needs only that every
  action can be carried to every other by some symmetry.
* `guess_isSymmetric`, `guess_softmax_optimal`: non-vacuity, the
  "guess the state" problem on `n + 1` equally likely states.

This supplies the derivation of uniform marginals from a symmetric problem
that `optimal_is_softmax_of_uniform` takes as a hypothesis. **Scope.** The
result says the logit rule is *an* optimal rule; uniqueness of the optimal
rule (it can fail, e.g. with duplicate actions), the necessity half of
Lemma 2, and Caplin–Dean's necessary and sufficient conditions on the support
of the optimal marginal are not formalized; from Caplin–Dean only the
posterior-free objective `F` is used.
-/
module

public import EconLean.Behavioral.RationalInattention
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

namespace Econ

namespace RationalInattention

open Finset Real Logit

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- The objective of the problem in unconditional choice probabilities. -/
noncomputable def valueF (lam : ℝ) (g : Ω → ℝ) (v : Ω → ι → ℝ) (P : ι → ℝ) : ℝ :=
  ∑ ω, g ω * (lam * log (Z lam P (v ω)))

/-- Every rule earns at most `F` of its own marginal. -/
theorem riObjective_le_valueF {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ} (hg : IsPrior g)
    (v : Ω → ι → ℝ) {p : Ω → ι → ℝ} (hp : IsRule p) :
    riObjective lam g v p ≤ valueF lam g v (marginal g p) := by
  set P := marginal g p
  have hP := marginal_isProb hg hp
  have h : riObjective lam g v p = ∑ ω, g ω * objective lam P (v ω) (p ω) := by
    rw [sum_objective_eq]; rfl
  rw [h, valueF]
  exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
    (objective_le0 hlam hP.1 (Z_pos_of_isProb hP) (hp ω)
      fun i hi => rule_eq_zero_of_marginal_eq_zero hg hp hi ω) (hg.1 ω).le

omit [Fintype Ω] in
/-- The generalized-logit rule built on `P` is a rule. -/
theorem isRule_gl {lam : ℝ} {P : ι → ℝ} (hP : IsProb P) (v : Ω → ι → ℝ) :
    IsRule fun ω => generalizedLogit lam P (v ω) :=
  fun _ => gl_isProb hP.1 (Z_pos_of_isProb hP)

/-- The generalized-logit rule built on `P` earns at least `F(P)`. -/
theorem valueF_le_riObjective_gl {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ} (hg : IsPrior g)
    (v : Ω → ι → ℝ) {P : ι → ℝ} (hP : IsProb P) :
    valueF lam g v P ≤ riObjective lam g v fun ω => generalizedLogit lam P (v ω) := by
  set p : Ω → ι → ℝ := fun ω => generalizedLogit lam P (v ω)
  have hp : IsRule p := isRule_gl hP v
  have hmarg : ∀ i, P i = 0 → marginal g p i = 0 := fun i h =>
    sum_eq_zero fun ω _ => by simp only [p, gl_eq_zero h, mul_zero]
  have h1 : valueF lam g v P = ∑ ω, g ω * objective lam P (v ω) (p ω) := by
    rw [valueF]
    exact sum_congr rfl fun ω _ => by rw [objective_gl0 hlam hP.1 (Z_pos_of_isProb hP)]
  rw [h1, sum_objective_eq, riObjective, avgKL_eq]
  have := kl_nonneg0 (marginal_isProb hg hp) hP hmarg
  nlinarith

/-- **Matějka–McKay, Lemma 2 (sufficiency).** A maximizer of `F` over
probability vectors yields an optimal rule: the generalized logit built on it. -/
theorem isOptimalRule_gl_of_isMax {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ} (hg : IsPrior g)
    (v : Ω → ι → ℝ) {P : ι → ℝ} (hP : IsProb P)
    (hmax : ∀ P', IsProb P' → valueF lam g v P' ≤ valueF lam g v P) :
    IsOptimalRule lam g v fun ω => generalizedLogit lam P (v ω) :=
  ⟨isRule_gl hP v, fun _ hp' =>
    ((riObjective_le_valueF hlam hg v hp').trans (hmax _ (marginal_isProb hg hp'))).trans
      (valueF_le_riObjective_gl hlam hg v hP)⟩

/-- **Concavity of `F`** (equal-weight Jensen over a finite family). -/
theorem valueF_avg_ge {κ : Type*} {lam : ℝ} (hlam : 0 ≤ lam) {g : Ω → ℝ} (hg : ∀ ω, 0 ≤ g ω)
    (v : Ω → ι → ℝ) {S : Finset κ} (hS : S.Nonempty) (Pk : κ → ι → ℝ)
    (hPk : ∀ k ∈ S, IsProb (Pk k)) :
    ∑ k ∈ S, (1 / (#S : ℝ)) * valueF lam g v (Pk k) ≤
      valueF lam g v fun i => ∑ k ∈ S, (1 / (#S : ℝ)) * Pk k i := by
  have hc : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  have hw1 : ∑ _k ∈ S, (1 / (#S : ℝ)) = 1 := by
    rw [sum_const, nsmul_eq_mul]; field_simp
  unfold valueF
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_le_sum fun ω _ => ?_
  have hZ : Z lam (fun i => ∑ k ∈ S, (1 / (#S : ℝ)) * Pk k i) (v ω) =
      ∑ k ∈ S, (1 / (#S : ℝ)) • Z lam (Pk k) (v ω) := by
    simp only [Z, smul_eq_mul, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := S)
    (w := fun _ => 1 / (#S : ℝ)) (p := fun k => Z lam (Pk k) (v ω))
    (fun _ _ => by positivity) hw1 fun k hk => Set.mem_Ioi.2 (Z_pos_of_isProb (hPk k hk))
  rw [hZ]
  have : ∑ k ∈ S, 1 / (#S : ℝ) * (g ω * (lam * log (Z lam (Pk k) (v ω)))) =
      g ω * lam * ∑ k ∈ S, (1 / (#S : ℝ)) • log (Z lam (Pk k) (v ω)) := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by rw [smul_eq_mul]; ring
  rw [this, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left hJ (mul_nonneg (hg ω) hlam)

/-- A permutation `τ` of actions is a **symmetry** of the problem if a
permutation of states preserves the prior and carries payoffs along. -/
def IsSymmetry (g : Ω → ℝ) (v : Ω → ι → ℝ) (τ : Equiv.Perm ι) : Prop :=
  ∃ ρ : Equiv.Perm Ω, (∀ ω, g (ρ ω) = g ω) ∧ ∀ ω i, v (ρ ω) (τ i) = v ω i

/-- `F` is invariant under symmetries. -/
theorem valueF_comp {lam : ℝ} {g : Ω → ℝ} {v : Ω → ι → ℝ} {τ : Equiv.Perm ι}
    (hτ : IsSymmetry g v τ) (P : ι → ℝ) :
    valueF lam g v (fun i => P (τ i)) = valueF lam g v P := by
  obtain ⟨ρ, hg, hv⟩ := hτ
  have hZ : ∀ ω, Z lam (fun i => P (τ i)) (v ω) = Z lam P (v (ρ ω)) := fun ω => by
    unfold Z
    simp_rw [← hv ω]
    exact Equiv.sum_comp τ (fun j => P j * exp (v (ρ ω) j / lam))
  unfold valueF
  simp_rw [hZ]
  calc ∑ ω, g ω * (lam * log (Z lam P (v (ρ ω))))
      = ∑ ω, g (ρ ω) * (lam * log (Z lam P (v (ρ ω)))) := sum_congr rfl fun ω _ => by rw [hg]
    _ = _ := Equiv.sum_comp ρ (fun ω => g ω * (lam * log (Z lam P (v ω))))

omit [Fintype Ω] [Fintype ι] in
/-- Symmetries compose. -/
theorem isSymmetry_mul {g : Ω → ℝ} {v : Ω → ι → ℝ} {σ τ : Equiv.Perm ι}
    (hσ : IsSymmetry g v σ) (hτ : IsSymmetry g v τ) : IsSymmetry g v (σ * τ) := by
  obtain ⟨ρ₁, hg₁, hv₁⟩ := hσ
  obtain ⟨ρ₂, hg₂, hv₂⟩ := hτ
  refine ⟨ρ₁ * ρ₂, fun ω => ?_, fun ω i => ?_⟩
  · rw [Equiv.Perm.mul_apply, hg₁, hg₂]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv₁, hv₂]

/-- With a constant positive default, the generalized logit is the softmax. -/
theorem gl_const {lam c : ℝ} (hc : 0 < c) (v : ι → ℝ) :
    generalizedLogit lam (fun _ => c) v = softmax lam v := by
  funext i
  simp only [generalizedLogit, Z, softmax, ← mul_sum]
  field_simp

/-- **Matějka–McKay: symmetric problems give the multinomial logit.** If a set
of symmetries is closed under composition and acts transitively on actions,
the softmax rule is optimal. -/
theorem softmax_optimal_of_symmetric [Nonempty ι] {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ}
    (hg : IsPrior g) {v : Ω → ι → ℝ} (S : Finset (Equiv.Perm ι))
    (hS : ∀ τ ∈ S, IsSymmetry g v τ) (hmul : ∀ σ ∈ S, ∀ τ ∈ S, σ * τ ∈ S)
    (htrans : ∀ i j, ∃ σ ∈ S, σ i = j) :
    IsOptimalRule lam g v fun ω => softmax lam (v ω) := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hSne : S.Nonempty := by obtain ⟨σ, hσ, _⟩ := htrans i₀ i₀; exact ⟨σ, hσ⟩
  have hc : (0 : ℝ) < #S := by exact_mod_cast hSne.card_pos
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set u : ι → ℝ := fun _ => 1 / (Fintype.card ι : ℝ)
  have hu : IsProb u := ⟨fun _ => by positivity, by
    simp only [u, sum_const, card_univ, nsmul_eq_mul]; field_simp⟩
  have hsm : (fun ω => softmax lam (v ω)) = fun ω => generalizedLogit lam u (v ω) := by
    funext ω; rw [gl_const (by positivity)]
  rw [hsm]
  refine isOptimalRule_gl_of_isMax hlam hg v hu fun P hP => ?_
  -- the symmetrized marginal
  have hPτ : ∀ τ : Equiv.Perm ι, IsProb fun i => P (τ i) := fun τ =>
    ⟨fun i => hP.1 _, by rw [Equiv.sum_comp τ P]; exact hP.2⟩
  -- the sum over `S` of `P (τ i)` does not depend on `i`
  have hconst : ∀ i j, ∑ τ ∈ S, P (τ i) = ∑ τ ∈ S, P (τ j) := by
    intro i j
    obtain ⟨σ, hσ, hσj⟩ := htrans j i
    have himg : S.image (· * σ) = S := by
      apply eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hx
        exact hmul τ hτ σ hσ
      · rw [card_image_of_injective _ (mul_left_injective σ)]
    calc ∑ τ ∈ S, P (τ i) = ∑ τ ∈ S, P ((τ * σ) j) := by
          refine sum_congr rfl fun τ _ => ?_
          rw [Equiv.Perm.mul_apply, hσj]
      _ = ∑ τ ∈ S.image (· * σ), P (τ j) :=
          (sum_image (f := fun τ => P (τ j)) fun a _ b _ h => mul_left_injective σ h).symm
      _ = ∑ τ ∈ S, P (τ j) := by rw [himg]
  have havg : (fun i => ∑ τ ∈ S, (1 / (#S : ℝ)) * P (τ i)) = u := by
    funext i
    have hsum : ∑ j, ∑ τ ∈ S, P (τ j) = #S := by
      rw [sum_comm]
      simp_rw [Equiv.sum_comp _ P, hP.2, sum_const, nsmul_eq_mul, mul_one]
    have : ∑ j, ∑ τ ∈ S, P (τ j) = Fintype.card ι * ∑ τ ∈ S, P (τ i) := by
      rw [sum_congr rfl fun j _ => hconst j i, sum_const, card_univ, nsmul_eq_mul]
    rw [← mul_sum, show u i = 1 / (Fintype.card ι : ℝ) from rfl]
    rw [hsum] at this
    field_simp
    nlinarith
  have hJ := valueF_avg_ge (lam := lam) hlam.le (fun ω => (hg.1 ω).le) v hSne
    (fun τ i => P (τ i)) fun τ _ => hPτ τ
  rw [havg] at hJ
  have : ∑ τ ∈ S, (1 / (#S : ℝ)) * valueF lam g v (fun i => P (τ i)) = valueF lam g v P := by
    rw [sum_congr rfl fun τ hτ => by rw [valueF_comp (hS τ hτ)], ← sum_mul, sum_const,
      nsmul_eq_mul]
    field_simp
  linarith

/-- **Symmetric problems give the logit**, transitivity form: if every action
can be carried to every other by a symmetry, the softmax rule is optimal. -/
theorem softmax_optimal_of_transitive [Nonempty ι] {lam : ℝ} (hlam : 0 < lam) {g : Ω → ℝ}
    (hg : IsPrior g) {v : Ω → ι → ℝ} (htrans : ∀ i j, ∃ τ, IsSymmetry g v τ ∧ τ i = j) :
    IsOptimalRule lam g v fun ω => softmax lam (v ω) := by
  classical
  refine softmax_optimal_of_symmetric hlam hg (univ.filter (IsSymmetry g v))
    (fun τ hτ => (mem_filter.1 hτ).2)
    (fun σ hσ τ hτ => mem_filter.2 ⟨mem_univ _, isSymmetry_mul (mem_filter.1 hσ).2
      (mem_filter.1 hτ).2⟩) fun i j => ?_
  obtain ⟨τ, hτ, h⟩ := htrans i j
  exact ⟨τ, mem_filter.2 ⟨mem_univ _, hτ⟩, h⟩

/-! ### Example: guessing the state -/

/-- Uniform prior on `n + 1` states. -/
noncomputable def guessPrior (n : ℕ) : Fin (n + 1) → ℝ := fun _ => 1 / (n + 1 : ℝ)

/-- Payoff `1` for naming the true state, `0` otherwise. -/
noncomputable def guessPayoff (n : ℕ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun ω i => if i = ω then 1 else 0

theorem guessPrior_isPrior (n : ℕ) : IsPrior (guessPrior n) := by
  refine ⟨fun _ => by unfold guessPrior; positivity, ?_⟩
  simp only [guessPrior, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; field_simp

/-- Every permutation of actions is a symmetry of the guessing problem. -/
theorem guess_isSymmetric (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) :
    IsSymmetry (guessPrior n) (guessPayoff n) τ :=
  ⟨τ, fun _ => rfl, fun ω i => by simp only [guessPayoff, τ.injective.eq_iff]⟩

/-- In the guessing problem the softmax rule is optimal. -/
theorem guess_softmax_optimal (n : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    IsOptimalRule lam (guessPrior n) (guessPayoff n) fun ω => softmax lam (guessPayoff n ω) :=
  softmax_optimal_of_symmetric hlam (guessPrior_isPrior n) univ
    (fun τ _ => guess_isSymmetric n τ) (fun _ _ _ _ => mem_univ _)
    fun i j => ⟨Equiv.swap i j, mem_univ _, Equiv.swap_apply_left i j⟩

end RationalInattention

end Econ
