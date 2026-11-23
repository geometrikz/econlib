/-
# Existence of logit QRE and of Berk–Nash equilibrium

References.
* R. McKelvey and T. Palfrey (1995), *GEB* 10, Theorem 1: every finite game
  has a logit QRE for every `λ ≥ 0` (any `λ`, in fact).
* I. Esponda and D. Pouzo (2016), *Econometrica* 84(3), Theorem 1: a Berk–Nash
  equilibrium exists.

**QRE.** The logit response map `σ ↦ (exp(λUᵢ(b,σ)) / Σ_c exp(λUᵢ(c,σ)))ᵢ,b`
is continuous and maps mixed profiles to mixed profiles, a nonempty compact
convex set in `∏ᵢ ℝ^{Aᵢ}`; Brouwer gives a fixed point (`exists_isLogitQRE`).

**Berk–Nash.** On `Δ(X) × Δ(Θ)` consider the correspondence sending `(σ, μ)`
to the pairs `(σ', μ')` with `σ'` supported on subjective best responses to
`μ` and `μ'` supported on KL-minimizers given `σ`. Values are nonempty
(finite argmax/argmin) and convex; the graph is closed because "supported on
maximizers of `f`" is the family of closed conditions
`σ'(x) (f x' - f x) ≤ 0`. Kakutani gives a fixed point, which is a Berk–Nash
equilibrium (`exists_isBerkNash`). The setting is EP's with finite `X`, `Θ`
and full-support model distributions (`Qθ_pos`), so `K` is finite and
continuous.
-/
module

public import EconLean.BoundedRationality.QRE
public import EconLean.BoundedRationality.BerkNash
public import EconLean.Foundations.FixedPoint

@[expose] public section

namespace Econ

namespace BoundedRationality

open Finset Real Set

/-! ### Logit QRE -/

section QRE

variable {I : Type*} [Fintype I] [DecidableEq I] (G : FiniteGame I)

theorem continuous_U (i : I) (b : G.A i) :
    Continuous fun σ : (∀ i, G.A i → ℝ) => U G σ i b := by
  unfold U profileProb
  refine continuous_finsetSum _ fun a _ => (continuous_finsetProd _ fun j _ => ?_).mul
    continuous_const
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; exact continuous_const
  · simp only [Function.update_of_ne hj]
    exact (continuous_apply (a j)).comp (continuous_apply j)

variable [∀ i, Nonempty (G.A i)]

/-- The set of mixed profiles. -/
def mixedProfiles : Set (∀ i, G.A i → ℝ) := {σ | IsMixedProfile G σ}

omit [Fintype I] [DecidableEq I] [∀ i, Nonempty (G.A i)] in
theorem convex_mixedProfiles : Convex ℝ (mixedProfiles G) := by
  intro σ hσ τ hτ a b ha hb hab i
  refine ⟨fun c => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha ((hσ i).1 c)) (mul_nonneg hb ((hτ i).1 c))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, (hσ i).2,
      (hτ i).2]
    linarith

omit [Fintype I] [DecidableEq I] [∀ i, Nonempty (G.A i)] in
theorem isCompact_mixedProfiles : IsCompact (mixedProfiles G) := by
  have hcl : IsClosed (mixedProfiles G) := by
    have e : mixedProfiles G = (⋂ i, ⋂ b, {σ : ∀ i, G.A i → ℝ | 0 ≤ σ i b}) ∩
        ⋂ i, {σ | ∑ b, σ i b = 1} := by
      ext σ; simp [mixedProfiles, IsMixedProfile, forall_and]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun b => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply b).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun b _ =>
        (continuous_apply b).comp (continuous_apply i)) continuous_const
  have hsub : mixedProfiles G ⊆ Set.pi univ fun i => Set.pi univ fun _ => Icc (0 : ℝ) 1 := by
    intro σ hσ i _ b _
    refine ⟨(hσ i).1 b, ?_⟩
    rw [← (hσ i).2]
    exact single_le_sum (f := σ i) (fun c _ => (hσ i).1 c) (mem_univ b)
  exact (isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
    hcl hsub

/-- **McKelvey–Palfrey (1995), Theorem 1.** Every finite game has a logit QRE
at every precision `λ`. -/
theorem exists_isLogitQRE (lam : ℝ) : ∃ σ, IsLogitQRE G lam σ := by
  let T : (∀ i, G.A i → ℝ) → (∀ i, G.A i → ℝ) := fun σ i b => logitResponse G lam σ i b
  have hT : Continuous T := by
    refine continuous_pi fun i => continuous_pi fun b => ?_
    show Continuous fun σ => logitResponse G lam σ i b
    unfold logitResponse
    refine Continuous.div ((continuous_const.mul (continuous_U G i b)).rexp)
      (continuous_finsetSum _ fun c _ => (continuous_const.mul (continuous_U G i c)).rexp)
      fun σ => (sum_exp_pos G lam σ i).ne'
  have hne : (mixedProfiles G).Nonempty := by
    refine ⟨fun i _ => 1 / Fintype.card (G.A i), fun i => ⟨fun _ => by positivity, ?_⟩⟩
    simp
  have hmaps : MapsTo T (mixedProfiles G) (mixedProfiles G) := by
    intro σ _ i
    refine ⟨fun b => (div_pos (exp_pos _) (sum_exp_pos G lam σ i)).le, ?_⟩
    simp only [T, logitResponse]
    rw [← sum_div, div_self (sum_exp_pos G lam σ i).ne']
  obtain ⟨σ, -, hσ⟩ := brouwer_fixedPoint (convex_mixedProfiles G) (isCompact_mixedProfiles G)
    hne hmaps hT.continuousOn
  exact ⟨σ, fun i b => (congrFun (congrFun hσ i) b).symm⟩

end QRE

/-! ### Berk–Nash equilibrium -/

namespace SubjectiveProblem

open Logit RationalInattention

variable {X Y Θ : Type*} [Fintype X] [Fintype Y] [Fintype Θ] (M : SubjectiveProblem X Y Θ)

/-- Probability vectors. -/
def probs (α : Type*) [Fintype α] : Set (α → ℝ) := {p | IsProb p}

theorem convex_probs (α : Type*) [Fintype α] : Convex ℝ (probs α) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun s => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 s)) (mul_nonneg hb (hq.1 s))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.2, hq.2]
    linarith

theorem isClosed_probs (α : Type*) [Fintype α] : IsClosed (probs α) := by
  have e : probs α = (⋂ s, {p : α → ℝ | 0 ≤ p s}) ∩ {p | ∑ s, p s = 1} := by
    ext p; simp [probs, IsProb]
  rw [e]
  exact (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter
    (isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const)

theorem isCompact_probs (α : Type*) [Fintype α] : IsCompact (probs α) := by
  have hsub : probs α ⊆ Set.pi univ fun _ => Icc (0 : ℝ) 1 := by
    intro p hp s _
    refine ⟨hp.1 s, ?_⟩
    rw [← hp.2]
    exact single_le_sum (f := p) (fun c _ => hp.1 c) (mem_univ s)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_probs α) hsub

/-- A probability vector supported on maximizers of `f`. -/
theorem exists_prob_supported_max {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ p ∈ probs α, ∀ x x', p x * (f x' - f x) ≤ 0 := by
  classical
  obtain ⟨x₀, -, hx₀⟩ := univ.exists_max_image f univ_nonempty
  refine ⟨fun x => if x = x₀ then 1 else 0, ⟨fun x => by dsimp only; split_ifs <;> norm_num,
    by simp⟩, fun x x' => ?_⟩
  dsimp only
  split_ifs with h
  · subst h; linarith [hx₀ x' (mem_univ x')]
  · simp

theorem continuous_K (θ : Θ) : Continuous fun σ : X → ℝ => M.K σ θ :=
  continuous_finsetSum _ fun x _ => (continuous_apply x).mul continuous_const

theorem continuous_subjEU (x : X) : Continuous fun μ : Θ → ℝ => M.subjEU μ x :=
  continuous_finsetSum _ fun θ _ => (continuous_apply θ).mul continuous_const

/-- **Esponda–Pouzo (2016), Theorem 1, special case** with finitely many
actions and parameters and full-support model distributions (EP allow a
compact parameter space and infinite KL divergence). A Berk–Nash equilibrium
exists. -/
theorem exists_isBerkNash [Nonempty X] [Nonempty Θ] : ∃ σ μ, M.IsBerkNash σ μ := by
  classical
  let s : Set ((X → ℝ) × (Θ → ℝ)) := probs X ×ˢ probs Θ
  let φ : (X → ℝ) × (Θ → ℝ) → Set ((X → ℝ) × (Θ → ℝ)) := fun p =>
    {q | q.1 ∈ probs X ∧ q.2 ∈ probs Θ ∧
      (∀ x x', q.1 x * (M.subjEU p.2 x' - M.subjEU p.2 x) ≤ 0) ∧
      (∀ θ θ', q.2 θ * (M.K p.1 θ - M.K p.1 θ') ≤ 0)}
  have hconv : Convex ℝ s := (convex_probs X).prod (convex_probs Θ)
  have hcomp : IsCompact s := (isCompact_probs X).prod (isCompact_probs Θ)
  have hne : s.Nonempty := by
    obtain ⟨p, hp, -⟩ := exists_prob_supported_max (α := X) (fun _ => (0 : ℝ))
    obtain ⟨q, hq, -⟩ := exists_prob_supported_max (α := Θ) (fun _ => (0 : ℝ))
    exact ⟨(p, q), hp, hq⟩
  have hmaps : ∀ p ∈ s, φ p ⊆ s := fun p _ q hq => ⟨hq.1, hq.2.1⟩
  have hφne : ∀ p ∈ s, (φ p).Nonempty := by
    intro p _
    obtain ⟨a, ha, ha'⟩ := exists_prob_supported_max (fun x => M.subjEU p.2 x)
    obtain ⟨b, hb, hb'⟩ := exists_prob_supported_max (fun θ => -M.K p.1 θ)
    exact ⟨(a, b), ha, hb, ha', fun θ θ' => by have := hb' θ θ'; linarith⟩
  have hφconv : ∀ p ∈ s, Convex ℝ (φ p) := by
    intro p _ q hq r hr a b ha hb hab
    refine ⟨convex_probs X hq.1 hr.1 ha hb hab, convex_probs Θ hq.2.1 hr.2.1 ha hb hab,
      fun x x' => ?_, fun θ θ' => ?_⟩
    · have h1 := hq.2.2.1 x x'
      have h2 := hr.2.2.1 x x'
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨ha, h1⟩), mul_le_mul_of_nonneg_left h1 ha,
        mul_le_mul_of_nonneg_left h2 hb]
    · have h1 := hq.2.2.2 θ θ'
      have h2 := hr.2.2.2 θ θ'
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  have hgraph : IsClosed {pq : ((X → ℝ) × (Θ → ℝ)) × ((X → ℝ) × (Θ → ℝ)) |
      pq.1 ∈ s ∧ pq.2 ∈ φ pq.1} := by
    have e : {pq : ((X → ℝ) × (Θ → ℝ)) × ((X → ℝ) × (Θ → ℝ)) | pq.1 ∈ s ∧ pq.2 ∈ φ pq.1} =
        (Prod.fst ⁻¹' s) ∩ ((fun pq => pq.2.1) ⁻¹' probs X) ∩ ((fun pq => pq.2.2) ⁻¹' probs Θ) ∩
        (⋂ x, ⋂ x', {pq | pq.2.1 x * (M.subjEU pq.1.2 x' - M.subjEU pq.1.2 x) ≤ 0}) ∩
        (⋂ θ, ⋂ θ', {pq | pq.2.2 θ * (M.K pq.1.1 θ - M.K pq.1.1 θ') ≤ 0}) := by
      ext pq
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, φ]
      tauto
    rw [e]
    have c11 : Continuous fun pq : ((X → ℝ) × (Θ → ℝ)) × ((X → ℝ) × (Θ → ℝ)) => pq.1.1 :=
      continuous_fst.comp continuous_fst
    have c12 : Continuous fun pq : ((X → ℝ) × (Θ → ℝ)) × ((X → ℝ) × (Θ → ℝ)) => pq.1.2 :=
      continuous_snd.comp continuous_fst
    have c21 : Continuous fun pq : ((X → ℝ) × (Θ → ℝ)) × ((X → ℝ) × (Θ → ℝ)) => pq.2.1 :=
      continuous_fst.comp continuous_snd
    have c22 : Continuous fun pq : ((X → ℝ) × (Θ → ℝ)) × ((X → ℝ) × (Θ → ℝ)) => pq.2.2 :=
      continuous_snd.comp continuous_snd
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
    · exact (((isClosed_probs X).preimage continuous_fst).inter
        ((isClosed_probs Θ).preimage continuous_snd)).preimage continuous_fst
    · exact (isClosed_probs X).preimage c21
    · exact (isClosed_probs Θ).preimage c22
    · refine isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_le ?_ continuous_const
      exact ((continuous_apply x).comp c21).mul
        (((M.continuous_subjEU x').comp c12).sub ((M.continuous_subjEU x).comp c12))
    · refine isClosed_iInter fun θ => isClosed_iInter fun θ' => isClosed_le ?_ continuous_const
      exact ((continuous_apply θ).comp c22).mul
        (((M.continuous_K θ).comp c11).sub ((M.continuous_K θ').comp c11))
  obtain ⟨p, hp, hfix⟩ := kakutani_fixedPoint hconv hcomp hne hmaps hφne hφconv hgraph
  refine ⟨p.1, p.2, hfix.1, hfix.2.1, fun x hx x' => ?_, fun θ hθ θ' => ?_⟩
  · have := hfix.2.2.1 x x'
    by_contra h
    push Not at h
    nlinarith
  · have := hfix.2.2.2 θ θ'
    by_contra h
    push Not at h
    nlinarith

end SubjectiveProblem

end BoundedRationality

end Econ
