/-
# The Gilboa–Schmeidler maxmin expected utility theorem

Reference: I. Gilboa and D. Schmeidler (1989), "Maxmin expected utility with
non-unique prior", *J. Math. Econ.* 18: 141–153.

**Setting.** Finitely many states `S`. As in GS's proof, we work with *utility
acts* `f : S → ℝ`: the Anscombe–Aumann act composed with the vN–M utility of
lotteries (GS Lemma 3.1 obtains that utility from the axioms on constant acts;
here it is taken as given). A constant act is `const c`; the mixture
`α f + (1-α) h` is taken statewise.

**Part 1 (functional form, GS Lemma 3.5).** A functional `I` on utility acts
that is monotone, constant-additive (`I (f + c) = I f + c`), positively
homogeneous and superadditive is a minimum of expected utilities:
`I f = min_{p ∈ C} E_p f` for the nonempty, closed, convex set of priors
`C = {p ∈ Δ(S) | E_p g ≥ I g for all g}` (`maxmin_of_isMaxminFunctional`).
The converse also holds (`isMaxminFunctional_of_isLeast`).
The proof is Hahn–Banach: at each act `f₀` the superlinear `I` has a linear
functional above it that touches at `f₀`; monotonicity and normalization make
it an expectation.

**Part 2 (preferences, GS Theorem 1).** A preference `R f g` ("`f` is weakly
preferred to `g`") on utility acts that is a complete preorder, monotone,
nondegenerate, Archimedean (GS A3), C-independent (GS A2) and uncertainty
averse (GS A5) is represented by maxmin expected utility over a nonempty,
closed, convex set of priors (`gilboa_schmeidler`). The certainty
equivalent `I f` (`f ~ const (I f)`) exists by the Archimedean axiom, and
C-independence and uncertainty aversion make it a maxmin functional.

**Necessity.** Conversely, ranking acts by any maxmin functional satisfies all
the axioms (`gsAxioms_of_isMaxminFunctional`); with `isMaxminFunctional_of_isLeast`
this covers maxmin EU over any set of priors at which the minimum is attained.
Non-vacuity: maxmin EU over the two Ellsberg priors satisfies the axioms
(`gsAxioms_ellsberg`).

**Uniqueness.** A nonempty closed convex set of priors representing a maxmin
functional is `priorSet I` (`eq_priorSet`, by separation), so the set in GS
Theorem 1 is unique (`gilboa_schmeidler_unique`).

**Domain.** Utility acts range over all of `ℝ^S`, i.e. the utility of
outcomes is assumed onto `ℝ` (GS allow `u(X)` to be any interval; with a
bounded range our C-independence and monotonicity apply to fewer acts).

**Not formalized.** GS Lemma 3.1 (the vN–M step from lottery acts to utility
acts) and the bounded-utility-range case.
-/
module

public import EconLean.Behavioral.Ambiguity
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.LinearAlgebra.Pi

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace Econ

namespace Ambiguity

open Finset

variable {S : Type*} [Fintype S]

/-! ### Part 1: maxmin functionals -/

/-- The probability simplex `Δ(S)`. -/
def priors (S : Type*) [Fintype S] : Set (S → ℝ) := {p | (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1}

/-- The properties GS derive for the certainty-equivalent functional. -/
structure IsMaxminFunctional (I : (S → ℝ) → ℝ) : Prop where
  mono : ∀ f g : S → ℝ, (∀ s, f s ≤ g s) → I f ≤ I g
  const_add : ∀ (f : S → ℝ) (c : ℝ), I (fun s => f s + c) = I f + c
  pos_hom : ∀ t : ℝ, 0 < t → ∀ f : S → ℝ, I (fun s => t * f s) = t * I f
  superadd : ∀ f g : S → ℝ, I f + I g ≤ I (fun s => f s + g s)

/-- The priors whose expectation dominates `I` everywhere. -/
def priorSet (I : (S → ℝ) → ℝ) : Set (S → ℝ) :=
  {p | p ∈ priors S ∧ ∀ g, I g ≤ eu p g}

namespace IsMaxminFunctional

variable {I : (S → ℝ) → ℝ} (hI : IsMaxminFunctional I)
include hI

omit [Fintype S] in
theorem map_zero : I 0 = 0 := by
  have h := hI.pos_hom 2 (by norm_num) 0
  simp only [Pi.zero_apply, mul_zero] at h
  have : I (fun _ : S => (0 : ℝ)) = I 0 := rfl
  linarith

omit [Fintype S] in
theorem map_const (c : ℝ) : I (fun _ => c) = c := by
  have h := hI.const_add 0 c
  simp only [Pi.zero_apply, zero_add] at h
  rw [h, hI.map_zero, zero_add]

omit [Fintype S] in
theorem smul (t : ℝ) (ht : 0 < t) (f : S → ℝ) : I (t • f) = t * I f :=
  hI.pos_hom t ht f

omit [Fintype S] in
theorem add_neg_le (f : S → ℝ) : I f + I (-f) ≤ 0 := by
  have h := hI.superadd f (-f)
  simp only [Pi.neg_apply, add_neg_cancel] at h
  have : I (fun _ : S => (0 : ℝ)) = 0 := hI.map_const 0
  linarith

/-- **Supporting expectation.** At every act `f₀` there is a prior whose
expectation dominates `I` and equals it at `f₀` (Hahn–Banach). -/
theorem exists_support (f₀ : S → ℝ) : ∃ p ∈ priorSet I, eu p f₀ = I f₀ := by
  classical
  -- a linear functional `L ≥ I` with `L x = I x`, for `x ≠ 0`
  have key : ∀ x : S → ℝ, x ≠ 0 →
      ∃ L : (S → ℝ) →ₗ[ℝ] ℝ, (∀ g, I g ≤ L g) ∧ L x = I x := by
    intro x hx
    let N : (S → ℝ) → ℝ := fun g => -I (-g)
    have N_hom : ∀ c : ℝ, 0 < c → ∀ y, N (c • y) = c * N y := by
      intro c hc y
      simp only [N, ← smul_neg, hI.smul c hc]
      ring
    have N_add : ∀ y z, N (y + z) ≤ N y + N z := by
      intro y z
      have := hI.superadd (-y) (-z)
      simp only [N, neg_add]
      have e : (fun s => (-y) s + (-z) s) = -y + -z := rfl
      rw [e] at this
      linarith
    let φ := LinearPMap.mkSpanSingleton' (σ := RingHom.id ℝ) x (I x) (fun c hc => by
      rcases smul_eq_zero.1 hc with h | h
      · simp [h]
      · exact absurd h hx)
    have hφ : ∀ y : φ.domain, φ y ≤ N y := by
      rintro ⟨y, hy⟩
      have hy' : y ∈ ℝ ∙ x := by simpa [φ, LinearPMap.domain_mkSpanSingleton] using hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      rw [LinearPMap.mkSpanSingleton'_apply]
      simp only [RingHom.id_apply, smul_eq_mul, N]
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · have e : -(c • x) = (-c) • x := by rw [neg_smul]
        rw [e, hI.smul (-c) (by linarith)]
        linarith
      · simp [hI.map_zero]
      · rw [← smul_neg, hI.smul c hc]
        nlinarith [hI.add_neg_le x]
    obtain ⟨L, hLφ, hLN⟩ := exists_extension_of_le_sublinear φ N N_hom N_add hφ
    refine ⟨L, fun g => ?_, ?_⟩
    · have := hLN (-g)
      simp only [N, neg_neg, map_neg] at this
      linarith
    · have hxm : x ∈ φ.domain := by
        simp [φ, LinearPMap.domain_mkSpanSingleton, Submodule.mem_span_singleton_self]
      have := hLφ ⟨x, hxm⟩
      rw [this, LinearPMap.mkSpanSingleton'_apply_self]
  -- turn `L` into a prior
  have toPrior : ∀ L : (S → ℝ) →ₗ[ℝ] ℝ, (∀ g, I g ≤ L g) →
      ∃ p ∈ priorSet I, ∀ g, eu p g = L g := by
    intro L hL
    let p : S → ℝ := fun s => L (fun j => if s = j then 1 else 0)
    have hrep : ∀ g, eu p g = L g := by
      intro g
      rw [LinearMap.pi_apply_eq_sum_univ L g, eu]
      exact sum_congr rfl (fun s _ => by simp [p, smul_eq_mul, mul_comm])
    refine ⟨p, ⟨⟨fun s => ?_, ?_⟩, fun g => (hrep g) ▸ hL g⟩, hrep⟩
    · have h1 := hL (fun j => if s = j then 1 else 0)
      have h2 := hI.mono 0 (fun j => if s = j then (1 : ℝ) else 0)
        (fun j => by split_ifs <;> simp)
      rw [hI.map_zero] at h2
      exact le_trans h2 h1
    · have h1 := hL (fun _ => 1)
      have h2 := hL (fun _ => -1)
      rw [hI.map_const] at h1 h2
      have e : (fun _ : S => (-1 : ℝ)) = -(fun _ => 1) := by funext; simp
      rw [e, map_neg] at h2
      have hs : ∑ s, p s = L (fun _ => 1) := by
        rw [← hrep]; simp [eu]
      rw [hs]; linarith
  by_cases h0 : f₀ = 0
  · have hx : (fun _ : S => (1 : ℝ)) ≠ 0 := by
      intro h
      have := hI.map_const 1
      rw [h, hI.map_zero] at this
      norm_num at this
    obtain ⟨L, hL, -⟩ := key _ hx
    obtain ⟨p, hp, -⟩ := toPrior L hL
    refine ⟨p, hp, ?_⟩
    subst h0
    simp [eu, hI.map_zero]
  · obtain ⟨L, hL, hx⟩ := key f₀ h0
    obtain ⟨p, hp, hpL⟩ := toPrior L hL
    exact ⟨p, hp, (hpL f₀).trans hx⟩

end IsMaxminFunctional

theorem eu_add_smul (a b : ℝ) (p q g : S → ℝ) : eu (a • p + b • q) g = a * eu p g + b * eu q g := by
  simp only [eu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_sum,
    mul_assoc]

theorem convex_priors : Convex ℝ (priors S) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun s => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 s)) (mul_nonneg hb (hq.1 s))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.2, hq.2]
    linarith

theorem isClosed_priors : IsClosed (priors S) := by
  have e : priors S = (⋂ s, {p : S → ℝ | 0 ≤ p s}) ∩ {p | ∑ s, p s = 1} := by
    ext p; simp [priors]
  rw [e]
  exact (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter
    (isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const)

theorem continuous_eu (g : S → ℝ) : Continuous fun p : S → ℝ => eu p g :=
  continuous_finsetSum _ fun s _ => (continuous_apply s).mul continuous_const

/-- **GS Lemma 3.5 (functional form).** A maxmin functional is the minimum of
expected utilities over a nonempty, closed, convex set of priors, namely
`priorSet I`. -/
theorem maxmin_of_isMaxminFunctional {I : (S → ℝ) → ℝ} (hI : IsMaxminFunctional I) :
    priorSet I ⊆ priors S ∧ (priorSet I).Nonempty ∧ Convex ℝ (priorSet I) ∧
      IsClosed (priorSet I) ∧ ∀ f, IsLeast ((fun p => eu p f) '' priorSet I) (I f) := by
  refine ⟨fun p hp => hp.1, ?_, ?_, ?_, fun f => ?_⟩
  · obtain ⟨p, hp, -⟩ := hI.exists_support 0
    exact ⟨p, hp⟩
  · intro p hp q hq a b ha hb hab
    refine ⟨convex_priors hp.1 hq.1 ha hb hab, fun g => ?_⟩
    rw [eu_add_smul]
    have h1 := hp.2 g
    have h2 := hq.2 g
    have : I g = a * I g + b * I g := by rw [← add_mul, hab, one_mul]
    rw [this]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  · have e : priorSet I = priors S ∩ ⋂ g, {p | I g ≤ eu p g} := by
      ext p; simp [priorSet]
    rw [e]
    exact (isClosed_priors).inter
      (isClosed_iInter fun g => isClosed_le continuous_const (continuous_eu g))
  · obtain ⟨p, hp, hpf⟩ := hI.exists_support f
    exact ⟨⟨p, hp, hpf⟩, by rintro _ ⟨q, hq, rfl⟩; exact hq.2 f⟩

theorem eu_const_add {p : S → ℝ} (hp : p ∈ priors S) (f : S → ℝ) (c : ℝ) :
    eu p (fun s => f s + c) = eu p f + c := by
  simp only [eu, mul_add, sum_add_distrib, ← sum_mul, hp.2, one_mul]

theorem eu_smul' (p f : S → ℝ) (t : ℝ) : eu p (fun s => t * f s) = t * eu p f := by
  simp only [eu, mul_sum]
  exact sum_congr rfl fun s _ => by ring

theorem eu_add' (p f g : S → ℝ) : eu p (fun s => f s + g s) = eu p f + eu p g := by
  simp only [eu, mul_add, sum_add_distrib]

theorem eu_mono' {p : S → ℝ} (hp : p ∈ priors S) {f g : S → ℝ} (h : ∀ s, f s ≤ g s) :
    eu p f ≤ eu p g :=
  sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hp.1 s)

/-- **Converse.** A minimum of expected utilities over any set of priors
(attained at every act) is a maxmin functional. -/
theorem isMaxminFunctional_of_isLeast {I : (S → ℝ) → ℝ} {C : Set (S → ℝ)}
    (hC : C ⊆ priors S) (h : ∀ f, IsLeast ((fun p => eu p f) '' C) (I f)) :
    IsMaxminFunctional I := by
  have att : ∀ f, ∃ p ∈ C, eu p f = I f := fun f => (h f).1
  have low : ∀ f, ∀ q ∈ C, I f ≤ eu q f := fun f q hq => (h f).2 ⟨q, hq, rfl⟩
  refine ⟨fun f g hfg => ?_, fun f c => ?_, fun t ht f => ?_, fun f g => ?_⟩
  · obtain ⟨p, hp, hpg⟩ := att g
    exact (low f p hp).trans (hpg ▸ eu_mono' (hC hp) hfg)
  · obtain ⟨p, hp, hp1⟩ := att f
    obtain ⟨q, hq, hq1⟩ := att (fun s => f s + c)
    have a1 := low (fun s => f s + c) p hp
    have a2 := low f q hq
    rw [eu_const_add (hC hp)] at a1
    rw [eu_const_add (hC hq)] at hq1
    linarith
  · obtain ⟨p, hp, hp1⟩ := att f
    obtain ⟨q, hq, hq1⟩ := att (fun s => t * f s)
    have a1 := low (fun s => t * f s) p hp
    have a2 := mul_le_mul_of_nonneg_left (low f q hq) ht.le
    rw [eu_smul', hp1] at a1
    rw [eu_smul'] at hq1
    linarith
  · obtain ⟨p, hp, hp1⟩ := att (fun s => f s + g s)
    rw [← hp1, eu_add']
    exact add_le_add (low f p hp) (low g p hp)

/-! ### Part 2: preferences -/

/-- The constant act. -/
def constAct (c : ℝ) : S → ℝ := fun _ => c

/-- Statewise mixture `α f + (1 - α) g`. -/
def mixAct (α : ℝ) (f g : S → ℝ) : S → ℝ := fun s => α * f s + (1 - α) * g s

/-- Strict part of a preference. -/
def StrictPref (R : (S → ℝ) → (S → ℝ) → Prop) (f g : S → ℝ) : Prop := R f g ∧ ¬ R g f

/-- The Gilboa–Schmeidler axioms on a preference over utility acts; `R f g`
reads "`f` is weakly preferred to `g`". A1 weak order (`total`, `trans`);
A2 C-independence (`cindep`, mixing with a constant act); A3 Archimedean
(`arch`); A4 monotonicity (`mono`); A5 uncertainty aversion (`uncAverse`);
A6 nondegeneracy (`nondeg`, with utility normalized so `const 1 ≻ const 0`). -/
structure GSAxioms (R : (S → ℝ) → (S → ℝ) → Prop) : Prop where
  total : ∀ f g, R f g ∨ R g f
  trans : ∀ f g h, R f g → R g h → R f h
  cindep : ∀ (f g : S → ℝ) (c α : ℝ), 0 < α → α < 1 →
    (R f g ↔ R (mixAct α f (constAct c)) (mixAct α g (constAct c)))
  arch : ∀ f g h, StrictPref R f g → StrictPref R g h →
    ∃ α β : ℝ, 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
      StrictPref R (mixAct α f h) g ∧ StrictPref R g (mixAct β f h)
  mono : ∀ f g : S → ℝ, (∀ s, g s ≤ f s) → R f g
  uncAverse : ∀ f g, R f g → R g f → ∀ α : ℝ, 0 < α → α < 1 → R (mixAct α f g) f
  nondeg : ¬ R (constAct 0) (constAct 1)

omit [Fintype S] in
theorem mixAct_const (α a c : ℝ) :
    mixAct α (constAct a) (constAct c) = (constAct (α * a + (1 - α) * c) : S → ℝ) := rfl

namespace GSAxioms

variable {R : (S → ℝ) → (S → ℝ) → Prop} (hR : GSAxioms R)
include hR

omit [Fintype S] in
theorem refl (f : S → ℝ) : R f f := hR.mono f f fun _ => le_rfl

omit [Fintype S] in
theorem nonempty : Nonempty S := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : (constAct 0 : S → ℝ) = constAct 1 := funext fun s => isEmptyElim s
  exact hR.nondeg (this ▸ hR.refl _)

omit [Fintype S] in
/-- Constants are ranked by their utility. -/
theorem const_le_iff (a b : ℝ) : R (constAct a) (constAct b) ↔ b ≤ a := by
  refine ⟨fun h => ?_, fun h => hR.mono _ _ fun _ => h⟩
  by_contra hab
  push Not at hab
  set d := b - a with hd
  have hdpos : 0 < d := by linarith
  set α := 1 / (2 * d + 2) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by linarith)]; linarith
  have h1 := (hR.cindep _ _ (-(α * a) / (1 - α)) α hα0 hα1).1 h
  rw [mixAct_const, mixAct_const] at h1
  have e0 : α * a + (1 - α) * (-(α * a) / (1 - α)) = 0 := by
    field_simp [show (1 - α) ≠ 0 by linarith]; ring
  have e1 : α * b + (1 - α) * (-(α * a) / (1 - α)) = α * d := by
    field_simp [show (1 - α) ≠ 0 by linarith]; ring
  rw [e0, e1] at h1
  have hδ0 : 0 < α * d := mul_pos hα0 hdpos
  have hδ1 : α * d < 1 := by
    rw [hα, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
  have h2 := (hR.cindep (constAct 0) (constAct 1) 0 (α * d) hδ0 hδ1).2
  rw [mixAct_const, mixAct_const] at h2
  apply hR.nondeg
  apply h2
  convert h1 using 2 <;> ring_nf

omit [Fintype S] in
theorem strict_of_not (f g : S → ℝ) (h : ¬ R f g) : StrictPref R g f :=
  ⟨(hR.total f g).resolve_left h, h⟩

/-- **Certainty equivalents exist** (from the Archimedean axiom). -/
theorem exists_ce (f : S → ℝ) : ∃ c, R f (constAct c) ∧ R (constAct c) f := by
  have := hR.nonempty
  set m := univ.inf' univ_nonempty f
  set M := univ.sup' univ_nonempty f
  have hm : R f (constAct m) := hR.mono _ _ fun s => inf'_le _ (mem_univ s)
  have hM : R (constAct M) f := hR.mono _ _ fun s => le_sup' _ (mem_univ s)
  set T := {c | R f (constAct c)}
  have bdd : ∀ c ∈ T, c ≤ M := fun c hc => (hR.const_le_iff M c).1 (hR.trans _ _ _ hM hc)
  have hT : T.Nonempty := ⟨m, hm⟩
  have hTb : BddAbove T := ⟨M, bdd⟩
  set c := sSup T
  have hmc : m ≤ c := le_csSup hTb hm
  have hcM : c ≤ M := csSup_le hT bdd
  refine ⟨c, ?_, ?_⟩
  · by_contra h1
    have hs := hR.strict_of_not _ _ h1
    by_cases hmf : R (constAct m) f
    · have : c ≤ m := csSup_le hT fun d hd => (hR.const_le_iff m d).1 (hR.trans _ _ _ hmf hd)
      have hcm : c = m := le_antisymm this hmc
      exact h1 (hcm ▸ hm)
    · have hs2 := hR.strict_of_not _ _ hmf
      have hne : m ≠ c := fun h => h1 (h ▸ hm)
      have hlt : m < c := lt_of_le_of_ne hmc hne
      obtain ⟨α, -, hα0, hα1, -, -, hA, -⟩ := hR.arch _ _ _ hs hs2
      rw [mixAct_const] at hA
      have hc' : α * c + (1 - α) * m < c := by nlinarith
      obtain ⟨d, hd, hdlt⟩ := exists_lt_of_lt_csSup hT hc'
      have := (hR.const_le_iff _ _).1 (hR.trans _ _ _ hA.1 hd)
      linarith
  · by_contra h2
    have hs := hR.strict_of_not _ _ h2
    by_cases hfM : R f (constAct M)
    · have : M ≤ c := le_csSup hTb hfM
      have hcM' : c = M := le_antisymm hcM this
      exact h2 (hcM' ▸ hM)
    · have hs2 := hR.strict_of_not _ _ hfM
      have hne : c ≠ M := fun h => h2 (h ▸ hM)
      have hlt : c < M := lt_of_le_of_ne hcM hne
      obtain ⟨-, β, -, -, hβ0, hβ1, -, hB⟩ := hR.arch _ _ _ hs2 hs
      rw [mixAct_const] at hB
      have hin : β * M + (1 - β) * c ∈ T := hB.1
      have := le_csSup hTb hin
      nlinarith

/-- The certainty equivalent. -/
noncomputable def ce (f : S → ℝ) : ℝ := Classical.choose (hR.exists_ce f)

theorem ce_spec (f : S → ℝ) : R f (constAct (hR.ce f)) ∧ R (constAct (hR.ce f)) f :=
  Classical.choose_spec (hR.exists_ce f)

theorem ce_eq {f : S → ℝ} {c : ℝ} (h1 : R f (constAct c)) (h2 : R (constAct c) f) :
    hR.ce f = c := by
  have a := (hR.const_le_iff _ _).1 (hR.trans _ _ _ (hR.ce_spec f).2 h1)
  have b := (hR.const_le_iff _ _).1 (hR.trans _ _ _ h2 (hR.ce_spec f).1)
  linarith

/-- The certainty equivalent represents the preference. -/
theorem rep (f g : S → ℝ) : R f g ↔ hR.ce g ≤ hR.ce f := by
  constructor
  · intro h
    exact (hR.const_le_iff _ _).1
      (hR.trans _ _ _ (hR.ce_spec f).2 (hR.trans _ _ _ h (hR.ce_spec g).1))
  · intro h
    exact hR.trans _ _ _ (hR.ce_spec f).1
      (hR.trans _ _ _ ((hR.const_le_iff _ _).2 h) (hR.ce_spec g).2)

theorem ce_const (c : ℝ) : hR.ce (constAct c) = c := ce_eq hR (hR.refl _) (hR.refl _)

theorem ce_mix_const (f : S → ℝ) (d α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    hR.ce (mixAct α f (constAct d)) = α * hR.ce f + (1 - α) * d := by
  apply hR.ce_eq
  · have := (hR.cindep _ _ d α h0 h1).1 (hR.ce_spec f).1
    rwa [mixAct_const] at this
  · have := (hR.cindep _ _ d α h0 h1).1 (hR.ce_spec f).2
    rwa [mixAct_const] at this

theorem ce_smul_lt_one (f : S → ℝ) (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    hR.ce (fun s => t * f s) = t * hR.ce f := by
  have := hR.ce_mix_const f 0 t h0 h1
  simp only [mul_zero, add_zero] at this
  rw [← this]
  congr 1
  funext s
  simp [mixAct, constAct]

theorem ce_pos_hom (t : ℝ) (ht : 0 < t) (f : S → ℝ) :
    hR.ce (fun s => t * f s) = t * hR.ce f := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · exact hR.ce_smul_lt_one f t ht h
  · simp
  · have hinv0 : 0 < 1 / t := by positivity
    have hinv1 : 1 / t < 1 := by rw [div_lt_one ht]; exact h
    have := hR.ce_smul_lt_one (fun s => t * f s) (1 / t) hinv0 hinv1
    have e : (fun s => 1 / t * (t * f s)) = f := by
      funext s; field_simp
    rw [e] at this
    rw [this]; field_simp

theorem ce_const_add (f : S → ℝ) (c : ℝ) : hR.ce (fun s => f s + c) = hR.ce f + c := by
  have e : (fun s => f s + c) = fun s => 2 * mixAct (1 / 2) f (constAct c) s := by
    funext s; simp [mixAct, constAct]; ring
  rw [e, hR.ce_pos_hom 2 (by norm_num), hR.ce_mix_const f c _ (by norm_num) (by norm_num)]
  ring

theorem isMaxminFunctional_ce : IsMaxminFunctional hR.ce := by
  refine ⟨fun f g h => (hR.rep g f).1 (hR.mono g f h), hR.ce_const_add, hR.ce_pos_hom,
    fun f g => ?_⟩
  set a := hR.ce f
  set b := hR.ce g
  set f' : S → ℝ := fun s => f s + -a
  set g' : S → ℝ := fun s => g s + -b
  have hf' : hR.ce f' = 0 := by simp [f', hR.ce_const_add, a]
  have hg' : hR.ce g' = 0 := by simp [g', hR.ce_const_add, b]
  have h1 : R f' g' := (hR.rep _ _).2 (by rw [hf', hg'])
  have h2 : R g' f' := (hR.rep _ _).2 (by rw [hf', hg'])
  have hua := (hR.rep _ _).1 (hR.uncAverse f' g' h1 h2 (1 / 2) (by norm_num) (by norm_num))
  rw [hf'] at hua
  have e : (fun s => f s + g s) =
      fun s => 2 * mixAct (1 / 2) f' g' s + (a + b) := by
    funext s; simp [mixAct, f', g']; ring
  rw [e, hR.ce_const_add, hR.ce_pos_hom 2 (by norm_num)]
  linarith

end GSAxioms

/-- **Gilboa–Schmeidler (1989), Theorem 1 (existence of the representation;
uniqueness is `gilboa_schmeidler_unique`, necessity
`gsAxioms_of_isMaxminFunctional`).** A preference on utility acts
satisfying the GS axioms is represented by maxmin expected utility over a
nonempty, closed, convex set of priors. -/
theorem gilboa_schmeidler {R : (S → ℝ) → (S → ℝ) → Prop} (hR : GSAxioms R) :
    ∃ C : Set (S → ℝ), C ⊆ priors S ∧ C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧
      ∃ I : (S → ℝ) → ℝ, (∀ f, IsLeast ((fun p => eu p f) '' C) (I f)) ∧
        ∀ f g, R f g ↔ I g ≤ I f := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := maxmin_of_isMaxminFunctional hR.isMaxminFunctional_ce
  exact ⟨_, h1, h2, h3, h4, hR.ce, h5, hR.rep⟩

/-- **Necessity.** Ranking acts by a maxmin functional satisfies the GS axioms. -/
theorem gsAxioms_of_isMaxminFunctional {I : (S → ℝ) → ℝ} (hI : IsMaxminFunctional I) :
    GSAxioms (fun f g => I g ≤ I f) := by
  have hmix : ∀ (f : S → ℝ) (c α : ℝ), 0 < α → α < 1 →
      I (mixAct α f (constAct c)) = α * I f + (1 - α) * c := by
    intro f c α h0 _
    have e : mixAct α f (constAct c) = fun s => (fun s => α * f s) s + (1 - α) * c := rfl
    rw [e, hI.const_add, hI.pos_hom α h0]
  have hconc : ∀ (f g : S → ℝ) (α : ℝ), 0 < α → α < 1 →
      α * I f + (1 - α) * I g ≤ I (mixAct α f g) := by
    intro f g α h0 h1
    have := hI.superadd (fun s => α * f s) (fun s => (1 - α) * g s)
    rwa [hI.pos_hom α h0, hI.pos_hom (1 - α) (by linarith)] at this
  refine ⟨fun f g => le_total _ _, fun f g h a b => b.trans a, fun f g c α h0 h1 => ?_,
    fun f g h hfg hgh => ?_, fun f g hfg => hI.mono g f hfg, fun f g h1 h2 α h0 hα => ?_, ?_⟩
  · rw [hmix f c α h0 h1, hmix g c α h0 h1]
    constructor <;> intro h <;> nlinarith
  · simp only [StrictPref, not_le] at hfg hgh
    obtain ⟨-, hfg⟩ := hfg
    obtain ⟨-, hgh⟩ := hgh
    -- `α` close to `1` (concavity) and `β` close to `0` (`I` is 1-Lipschitz)
    set r := (I g - I h) / (I f - I h)
    have hr0 : 0 < r := div_pos (by linarith) (by linarith)
    have hr1 : r < 1 := (div_lt_one (by linarith)).2 (by linarith)
    set K := ∑ s, |f s - h s|
    have hK : 0 ≤ K := sum_nonneg fun s _ => abs_nonneg _
    set β := min (1 / 2) ((I g - I h) / (2 * (K + 1)))
    have hβ0 : 0 < β := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hβ1 : β < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨(1 + r) / 2, β, by linarith, by linarith, hβ0, hβ1, ?_, ?_⟩
    · have hc := hconc f h ((1 + r) / 2) (by linarith) (by linarith)
      have hfh : 0 < I f - I h := by linarith
      have key : I g < (1 + r) / 2 * I f + (1 - (1 + r) / 2) * I h := by
        have : I g = I h + r * (I f - I h) := by
          simp only [r]; field_simp; ring
        rw [this]; nlinarith
      exact ⟨by linarith, by simp only [not_le]; linarith⟩
    · have hub : I (mixAct β f h) ≤ I h + β * K := by
        have := hI.mono (mixAct β f h) (fun s => h s + β * K) fun s => by
          simp only [mixAct]
          have h1 : f s - h s ≤ K :=
            (le_abs_self _).trans (single_le_sum (f := fun s => |f s - h s|)
              (fun s _ => abs_nonneg _) (mem_univ s))
          nlinarith
        rwa [hI.const_add] at this
      have hβK : β * K < I g - I h := by
        have h1 : β ≤ (I g - I h) / (2 * (K + 1)) := min_le_right _ _
        have h2 : β * K ≤ (I g - I h) / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right h1 hK
        have h3 : (I g - I h) / (2 * (K + 1)) * K < I g - I h := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      exact ⟨by linarith, by simp only [not_le]; linarith⟩
  · have := hconc f g α h0 hα
    nlinarith
  · simp only [not_le]
    have e : ∀ c : ℝ, I (constAct c) = c := hI.map_const
    rw [e, e]; norm_num

/-- Maxmin EU over a finite set of priors is a maxmin functional. -/
theorem isMaxminFunctional_meu (C : Finset (S → ℝ)) (hC : C.Nonempty)
    (hCp : ∀ p ∈ C, p ∈ priors S) : IsMaxminFunctional (meu C hC) := by
  apply isMaxminFunctional_of_isLeast (C := (C : Set (S → ℝ))) (fun p hp => hCp p hp)
  intro f
  obtain ⟨p, hp, hpf⟩ := exists_eq_meu C hC f
  exact ⟨⟨p, hp, hpf⟩, by rintro _ ⟨q, hq, rfl⟩; exact meu_le_eu C hC f hq⟩

/-- **Non-vacuity.** Maxmin EU over the two Ellsberg priors satisfies the GS
axioms. -/
theorem gsAxioms_ellsberg :
    GSAxioms (fun f g => meu ellsbergPriors ellsbergPriors_nonempty g ≤
      meu ellsbergPriors ellsbergPriors_nonempty f) := by
  apply gsAxioms_of_isMaxminFunctional
  apply isMaxminFunctional_meu
  intro p hp
  simp only [ellsbergPriors, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;>
    refine ⟨fun s => ?_, ?_⟩ <;> simp [Fin.sum_univ_three] <;> (try fin_cases s) <;> norm_num

/-- **Uniqueness of the set of priors.** A closed convex set of priors at
which a functional is an attained minimum of expected utilities is exactly
`priorSet I`. -/
theorem eq_priorSet {I : (S → ℝ) → ℝ} {C : Set (S → ℝ)} (hC : C ⊆ priors S)
    (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h : ∀ f, IsLeast ((fun p => eu p f) '' C) (I f)) : C = priorSet I := by
  ext p
  constructor
  · intro hp
    exact ⟨hC hp, fun g => (h g).2 ⟨p, hp, rfl⟩⟩
  · classical
    intro hp
    by_contra hpC
    obtain ⟨φ, u, hφC, hφp⟩ := geometric_hahn_banach_closed_point hconv hcl hpC
    -- `φ` is an expectation against the vector `g s = φ (e_s)`
    set g : S → ℝ := fun s => φ (fun j => if s = j then 1 else 0)
    have hφ : ∀ q, φ q = eu q g := by
      intro q
      have := LinearMap.pi_apply_eq_sum_univ (φ : (S → ℝ) →ₗ[ℝ] ℝ) q
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, eu]
      exact sum_congr rfl fun s _ => by simp [g, smul_eq_mul]
    -- `-g` separates: every prior in `C` gives more than `p` does
    obtain ⟨q, hq, hqI⟩ := (h (fun s => -g s)).1
    have h1 : I (fun s => -g s) ≤ eu p (fun s => -g s) := hp.2 _
    have e : ∀ r, eu r (fun s => -g s) = -eu r g := fun r => by
      simp [eu, Finset.sum_neg_distrib]
    simp only at hqI
    rw [← hqI, e, e] at h1
    have := hφC q hq
    rw [hφ] at this hφp
    linarith

/-- **Gilboa–Schmeidler, uniqueness.** Two maxmin-EU representations of the
same preference by nonempty closed convex sets of priors use the same set. -/
theorem gilboa_schmeidler_unique {R : (S → ℝ) → (S → ℝ) → Prop} {C₁ C₂ : Set (S → ℝ)}
    {I₁ I₂ : (S → ℝ) → ℝ} (hC₁ : C₁ ⊆ priors S) (hC₂ : C₂ ⊆ priors S)
    (hconv₁ : Convex ℝ C₁) (hconv₂ : Convex ℝ C₂) (hcl₁ : IsClosed C₁) (hcl₂ : IsClosed C₂)
    (h₁ : ∀ f, IsLeast ((fun p => eu p f) '' C₁) (I₁ f))
    (h₂ : ∀ f, IsLeast ((fun p => eu p f) '' C₂) (I₂ f))
    (hR₁ : ∀ f g, R f g ↔ I₁ g ≤ I₁ f) (hR₂ : ∀ f g, R f g ↔ I₂ g ≤ I₂ f) : C₁ = C₂ := by
  have hm₁ := isMaxminFunctional_of_isLeast hC₁ h₁
  have hm₂ := isMaxminFunctional_of_isLeast hC₂ h₂
  have hI : I₁ = I₂ := by
    funext f
    have c1 := hm₁.map_const (I₁ f)
    have c2 := hm₂.map_const (I₁ f)
    have a := (hR₁ f (fun _ => I₁ f)).2 (by rw [c1])
    have b := (hR₁ (fun _ => I₁ f) f).2 (by rw [c1])
    have a' := (hR₂ _ _).1 a
    have b' := (hR₂ _ _).1 b
    rw [c2] at a' b'
    linarith
  subst hI
  rw [eq_priorSet hC₁ hconv₁ hcl₁ h₁, eq_priorSet hC₂ hconv₂ hcl₂ h₂]

end Ambiguity

end Econ
