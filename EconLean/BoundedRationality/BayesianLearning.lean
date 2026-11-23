/-
# Bayesian learning: consistency and merging (finite hypotheses)

References. A. Wald (1949), "Note on the Consistency of the Maximum
Likelihood Estimate", *Ann. Math. Stat.* 20 (the log-likelihood-ratio
argument); J. L. Doob (1949), "Application of the theory of martingales";
D. Blackwell and L. Dubins (1962), "Merging of Opinions with Increasing
Information", *Ann. Math. Stat.* 33; E. Kalai and E. Lehrer (1993),
"Rational Learning Leads to Nash Equilibrium", *Econometrica* 61, and (1994),
"Weak and Strong Merging of Opinions", *J. Math. Econ.* 23 (weak merging);
cf. R. H. Berk (1966) for the misspecified case.

A Bayesian agent has a finite set of hypotheses `Θ`; hypothesis `θ` says the
observations are i.i.d. draws from the distribution `q θ` on a finite set
`O`. With a prior `p₀` and observations `x 0, x 1, …`, the posterior after `n`
observations is `p₀(θ) Lₙ(θ) / Σ p₀ Lₙ`, `Lₙ(θ) = ∏_{k<n} q θ (x k)`
(`lik`, `posterior`), and the one-step-ahead forecast is the posterior mixture
`Σ_θ posterior(θ) q θ` (`predictive`).

**Results.**
* `tendsto_posterior_of_llr` (deterministic): if, for every `θ ≠ θ*`, the
  average log-likelihood ratio `(1/n) Σ_{k<n} log(q θ (x k) / q θ* (x k))`
  converges to a negative number, the posterior concentrates on `θ*`.
* `ae_tendsto_llr` (strong law): if the observations are i.i.d. with law
  `q θ*`, the average log-likelihood ratio converges almost surely to
  `−KL(q θ* ‖ q θ)`.
* `posterior_consistent` (**Wald/Doob consistency**): if the data are i.i.d.
  from `q θ*`, all likelihoods are positive, the prior is positive, and the
  hypotheses are identified (`q θ ≠ q θ*` for `θ ≠ θ*`), then almost surely
  the posterior probability of `θ*` tends to `1`. These hypotheses are
  sufficient, not minimal: a prior positive only at `θ*` and likelihoods
  without full support would also do.
* `predictive_merges` (**weak merging of forecasts**, Kalai–Lehrer 1994):
  almost surely, the agent's one-step-ahead forecast converges to the true
  distribution `q θ*`. It is derived from posterior consistency and so
  assumes identification, which Blackwell–Dubins do not need.
* `coord_posterior_consistent`: non-vacuity, on the canonical i.i.d. product
  space `(ℕ → O, ⊗ q θ*)`.

The Blackwell–Dubins theorem (two measures on a filtered space, absolute
continuity only, strong merging: total-variation convergence of conditional
distributions over the whole future) and Doob's theorem for general parameter
spaces are not formalized; here the truth is one of finitely many identified
i.i.d. hypotheses, and merging is weak (next-period forecasts).
-/
module

public import EconLean.Behavioral.RationalInattention
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

noncomputable section

namespace Econ

namespace BayesianLearning

open Finset Filter Topology Real MeasureTheory ProbabilityTheory Function

variable {Θ O : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype O]

/-- Likelihood of the first `n` observations under `θ`. -/
def lik (q : Θ → O → ℝ) (x : ℕ → O) (n : ℕ) (θ : Θ) : ℝ := ∏ k ∈ range n, q θ (x k)

/-- Posterior probability of `θ` after `n` observations. -/
def posterior (p0 : Θ → ℝ) (q : Θ → O → ℝ) (x : ℕ → O) (n : ℕ) (θ : Θ) : ℝ :=
  p0 θ * lik q x n θ / ∑ θ', p0 θ' * lik q x n θ'

/-- One-step-ahead forecast: the posterior mixture of the hypotheses. -/
def predictive (p0 : Θ → ℝ) (q : Θ → O → ℝ) (x : ℕ → O) (n : ℕ) (o : O) : ℝ :=
  ∑ θ, posterior p0 q x n θ * q θ o

/-- Log-likelihood ratio of `θ` against `θs` at observation `o`. -/
def llr (q : Θ → O → ℝ) (θ θs : Θ) (o : O) : ℝ := log (q θ o / q θs o)

omit [Fintype Θ] [DecidableEq Θ] [Fintype O] in
theorem lik_pos {q : Θ → O → ℝ} (hq : ∀ θ o, 0 < q θ o) (x : ℕ → O) (n : ℕ) (θ : Θ) :
    0 < lik q x n θ :=
  prod_pos fun k _ => hq θ (x k)

omit [Fintype Θ] [DecidableEq Θ] [Fintype O] in
theorem lik_div {q : Θ → O → ℝ} (hq : ∀ θ o, 0 < q θ o) (x : ℕ → O) (n : ℕ) (θ θs : Θ) :
    lik q x n θ / lik q x n θs = exp (∑ k ∈ range n, llr q θ θs (x k)) := by
  rw [lik, lik, ← prod_div_distrib, exp_sum]
  refine prod_congr rfl fun k _ => ?_
  rw [llr, exp_log (div_pos (hq θ (x k)) (hq θs (x k)))]

omit [Fintype Θ] [DecidableEq Θ] [Fintype O] in
/-- If the average of `S n` tends to a negative limit, `exp (S n) → 0`. -/
theorem tendsto_exp_of_avg {S : ℕ → ℝ} {c : ℝ} (hc : c < 0)
    (h : Tendsto (fun n => S n / n) atTop (𝓝 c)) :
    Tendsto (fun n => exp (S n)) atTop (𝓝 0) := by
  have hev : ∀ᶠ n : ℕ in atTop, S n / n < c / 2 ∧ 0 < n :=
    (h.eventually (gt_mem_nhds (by linarith))).and (eventually_gt_atTop 0)
  have hr : Tendsto (fun n : ℕ => exp (c / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (exp_pos _).le (exp_lt_one_iff.2 (by linarith))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Eventually.of_forall fun n => (exp_pos _).le) ?_
  filter_upwards [hev] with n hn
  obtain ⟨h1, h2⟩ := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast h2
  rw [← exp_nat_mul]
  refine exp_le_exp.2 ?_
  rw [div_lt_iff₀ hn'] at h1
  linarith

omit [Fintype O] in
/-- **Posterior concentration** (deterministic form). -/
theorem tendsto_posterior_of_llr {p0 : Θ → ℝ} {q : Θ → O → ℝ} {x : ℕ → O} {θs : Θ}
    (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o)
    (h : ∀ θ, θ ≠ θs → ∃ c < 0,
      Tendsto (fun n : ℕ => (∑ k ∈ range n, llr q θ θs (x k)) / n) atTop (𝓝 c)) :
    ∀ θ, Tendsto (fun n => posterior p0 q x n θ) atTop (𝓝 (if θ = θs then 1 else 0)) := by
  -- posterior odds against `θs`
  set R : ℕ → Θ → ℝ := fun n θ => p0 θ * lik q x n θ / (p0 θs * lik q x n θs)
  have hden : ∀ n, 0 < p0 θs * lik q x n θs := fun n => mul_pos (hp0 θs) (lik_pos hq x n θs)
  have hR : ∀ θ, Tendsto (fun n => R n θ) atTop (𝓝 (if θ = θs then 1 else 0)) := by
    intro θ
    by_cases hθ : θ = θs
    · subst hθ
      simp only [ite_true, R]
      exact tendsto_const_nhds.congr fun n => (div_self (hden n).ne').symm
    · obtain ⟨c, hc, hlim⟩ := h θ hθ
      simp only [hθ, ite_false]
      have e : ∀ n, R n θ = p0 θ / p0 θs * exp (∑ k ∈ range n, llr q θ θs (x k)) := by
        intro n
        simp only [R]
        rw [← lik_div hq]
        have := (lik_pos hq x n θs).ne'
        have := (hp0 θs).ne'
        field_simp
      simp only [e]
      simpa using (tendsto_exp_of_avg hc hlim).const_mul (p0 θ / p0 θs)
  have hpost : ∀ n θ, posterior p0 q x n θ = R n θ / ∑ θ', R n θ' := by
    intro n θ
    simp only [R, posterior, ← sum_div]
    rw [div_div_div_cancel_right₀ (hden n).ne']
  have hsum : Tendsto (fun n => ∑ θ', R n θ') atTop (𝓝 1) := by
    have := tendsto_finsetSum (s := univ) fun θ' _ => hR θ'
    simpa using this
  intro θ
  have := (hR θ).div hsum one_ne_zero
  simp only [div_one] at this
  exact this.congr fun n => (hpost n θ).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace O] [MeasurableSingletonClass O]

/-- The data are i.i.d. with law `qs`. -/
structure IsIID (X : ℕ → Ω → O) (μ : Measure Ω) (qs : O → ℝ) : Prop where
  meas : ∀ n, Measurable (X n)
  indep : iIndepFun X μ
  ident : ∀ n, IdentDistrib (X n) (X 0) μ μ
  law : ∀ o, μ.real (X 0 ⁻¹' {o}) = qs o

omit [Fintype Θ] [DecidableEq Θ] in
/-- **Strong law for log-likelihood ratios.** -/
theorem ae_tendsto_llr {X : ℕ → Ω → O} {q : Θ → O → ℝ} {θs : Θ} (hX : IsIID X μ (q θs))
    (hq : ∀ θ o, 0 < q θ o) (θ : Θ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ range n, llr q θ θs (X k ω)) / n) atTop
      (𝓝 (-RationalInattention.kl (q θs) (q θ))) := by
  set g : O → ℝ := llr q θ θs
  have hg : Measurable g := measurable_of_finite g
  have hint : Integrable (g ∘ X 0) μ :=
    Integrable.comp_measurable Integrable.of_finite (hX.meas 0)
  have hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun k => g ∘ X k) :=
    fun i j hij => (hX.indep.indepFun hij).comp hg hg
  have h := strong_law_ae_real (fun k => g ∘ X k) hint hindep fun k => (hX.ident k).comp hg
  have hE : μ[g ∘ X 0] = -RationalInattention.kl (q θs) (q θ) := by
    have h1 : μ[g ∘ X 0] = ∫ o, g o ∂(μ.map (X 0)) :=
      (integral_map (hX.meas 0).aemeasurable hg.aestronglyMeasurable).symm
    rw [h1, integral_fintype Integrable.of_finite]
    simp only [map_measureReal_apply (hX.meas 0) (measurableSet_singleton _), hX.law,
      smul_eq_mul, RationalInattention.kl, g, llr, ← sum_neg_distrib]
    refine sum_congr rfl fun o _ => ?_
    rw [log_div (hq θ o).ne' (hq θs o).ne']
    ring
  rw [hE] at h
  exact h

omit [Fintype Θ] [DecidableEq Θ] [MeasurableSpace O] [MeasurableSingletonClass O] in
theorem kl_pos {q : Θ → O → ℝ} (hq : ∀ θ o, 0 < q θ o) (hsum : ∀ θ, ∑ o, q θ o = 1)
    {θ θs : Θ} (hid : q θ ≠ q θs) : 0 < RationalInattention.kl (q θs) (q θ) := by
  have hne : Nonempty O := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hsum θ
    simp at this
  have hp : ∀ θ, Logit.IsProb (q θ) := fun θ => ⟨fun o => (hq θ o).le, hsum θ⟩
  refine lt_of_le_of_ne (RationalInattention.kl_nonneg (hp θs) (hp θ) (hq θ)) fun h0 => ?_
  exact hid ((RationalInattention.kl_eq_zero_iff (hp θs) (hp θ) (hq θ)).1 h0.symm).symm

/-- **Bayesian consistency** (finite hypotheses, Wald/Doob). The hypotheses are
sufficient, not minimal. -/
theorem posterior_consistent {X : ℕ → Ω → O} {p0 : Θ → ℝ} {q : Θ → O → ℝ} {θs : Θ}
    (hX : IsIID X μ (q θs)) (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o)
    (hsum : ∀ θ, ∑ o, q θ o = 1) (hid : ∀ θ, θ ≠ θs → q θ ≠ q θs) :
    ∀ᵐ ω ∂μ, ∀ θ, Tendsto (fun n => posterior p0 q (fun k => X k ω) n θ) atTop
      (𝓝 (if θ = θs then 1 else 0)) := by
  have h := ae_all_iff.2 fun θ => ae_tendsto_llr (θ := θ) hX hq
  filter_upwards [h] with ω hω
  exact tendsto_posterior_of_llr hp0 hq fun θ hθ =>
    ⟨_, neg_neg_of_pos (kl_pos hq hsum (hid θ hθ)), hω θ⟩

/-- **Weak merging of forecasts**: the one-step-ahead forecast converges
almost surely to the true distribution. -/
theorem predictive_merges {X : ℕ → Ω → O} {p0 : Θ → ℝ} {q : Θ → O → ℝ} {θs : Θ}
    (hX : IsIID X μ (q θs)) (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o)
    (hsum : ∀ θ, ∑ o, q θ o = 1) (hid : ∀ θ, θ ≠ θs → q θ ≠ q θs) :
    ∀ᵐ ω ∂μ, ∀ o, Tendsto (fun n => predictive p0 q (fun k => X k ω) n o) atTop
      (𝓝 (q θs o)) := by
  filter_upwards [posterior_consistent hX hp0 hq hsum hid] with ω hω o
  have := tendsto_finsetSum (s := univ) fun θ _ => (hω θ).mul_const (q θ o)
  simpa [predictive, ite_mul] using this

/-! ### Non-vacuity: the canonical i.i.d. space -/

/-- The distribution on `O` with masses `qs`. -/
def pmfMeasure (qs : O → ℝ) : Measure O := ∑ o, ENNReal.ofReal (qs o) • Measure.dirac o

theorem pmfMeasure_singleton (qs : O → ℝ) (o : O) :
    pmfMeasure qs {o} = ENNReal.ofReal (qs o) := by
  simp [pmfMeasure]
  rw [sum_eq_single o (fun b _ hb => by
    rw [Set.indicator_of_notMem (by simpa using hb), mul_zero]) (by simp)]
  simp

theorem isProbabilityMeasure_pmfMeasure {qs : O → ℝ} (hqs : ∀ o, 0 ≤ qs o)
    (hsum : ∑ o, qs o = 1) : IsProbabilityMeasure (pmfMeasure qs) := by
  constructor
  have : (Set.univ : Set O) = ⋃ o ∈ (univ : Finset O), {o} := by ext; simp
  rw [this, measure_biUnion_finset (fun a _ b _ hab => Set.disjoint_singleton.2 hab)
    (fun o _ => measurableSet_singleton o)]
  simp only [pmfMeasure_singleton qs]
  rw [← ENNReal.ofReal_sum_of_nonneg fun o _ => hqs o, hsum, ENNReal.ofReal_one]

/-- The coordinate process on `(ℕ → O, ⊗ qs)` is i.i.d. with law `qs`. -/
theorem isIID_coord {qs : O → ℝ} (hqs : ∀ o, 0 ≤ qs o) (hsum : ∑ o, qs o = 1) :
    haveI := isProbabilityMeasure_pmfMeasure hqs hsum
    IsIID (fun n (ω : ℕ → O) => ω n) (Measure.infinitePi fun _ => pmfMeasure qs) qs := by
  have := isProbabilityMeasure_pmfMeasure hqs hsum
  refine ⟨fun n => measurable_pi_apply n, ?_, fun n => ?_, fun o => ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ (a : O) => a) fun _ => measurable_id
  · refine ⟨(measurable_pi_apply n).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
  · rw [← map_measureReal_apply (measurable_pi_apply 0) (measurableSet_singleton o),
      Measure.infinitePi_map_eval, measureReal_def, pmfMeasure_singleton qs,
      ENNReal.toReal_ofReal (hqs o)]

/-- Non-vacuity: on the canonical i.i.d. space, the posterior is consistent. -/
theorem coord_posterior_consistent {p0 : Θ → ℝ} {q : Θ → O → ℝ} {θs : Θ}
    (hp0 : ∀ θ, 0 < p0 θ) (hq : ∀ θ o, 0 < q θ o) (hsum : ∀ θ, ∑ o, q θ o = 1)
    (hid : ∀ θ, θ ≠ θs → q θ ≠ q θs) :
    haveI := isProbabilityMeasure_pmfMeasure (fun o => (hq θs o).le) (hsum θs)
    ∀ᵐ ω ∂(Measure.infinitePi fun _ => pmfMeasure (q θs)), ∀ θ,
      Tendsto (fun n => posterior p0 q ω n θ) atTop (𝓝 (if θ = θs then 1 else 0)) := by
  have := isProbabilityMeasure_pmfMeasure (fun o => (hq θs o).le) (hsum θs)
  exact posterior_consistent (isIID_coord (fun o => (hq θs o).le) (hsum θs)) hp0 hq hsum hid

end BayesianLearning

end Econ
