/-
# Variational preferences: the representation theorem

Reference. F. Maccheroni, M. Marinacci and A. Rustichini (2006), "Ambiguity
Aversion, Robustness, and the Variational Representation of Preferences",
*Econometrica* 74(6), Theorem 3 and its key Lemma (the functional step).

MMR's axioms (weak order, monotonicity, continuity, weak certainty
independence, uncertainty aversion, non-degeneracy) give a utility index `u`
and a functional `I` on utility acts `f = u ∘ act : S → ℝ` with
`act ≿ act' ↔ I(u ∘ act) ≥ I(u ∘ act')`, where `I` is monotone, constant
additive (`I(f + k) = I(f) + k`), normalized (`I(0) = 0`) and concave
(`IsVariationalFunctional`: a normalized concave niveloid in the sense of
Dolecki–Greco). `I` is taken on all of `ℝ^S`, i.e. unbounded utility,
`u(X) = ℝ`; for bounded `u(X)` MMR's minimal index is the conjugate over
`u(X)`-valued acts, which is not treated. The heart of the theorem is the variational representation of
such a functional, formalized here for a finite state space `S`:

    I(f) = min_{p ∈ Δ(S)} ( ⟨p, f⟩ + c(p) ),   c(p) = sup_g ( I(g) − ⟨p, g⟩ ),

with `c` the (concave-conjugate) ambiguity index, `c ≥ 0` and `c(p) = 0` for
some `p` (grounded).

Since `c` may be `+∞` (e.g. for maxmin preferences, outside the set of
priors), it is valued in `ℝ` only on its effective domain `InDom` (where the
supremum is finite); `cost` is the real supremum there.

**Results.**
* `exists_supergradient`: at every act `f`, `I` has a supergradient that is
  a probability vector: `I(g) − ⟨p, g⟩ ≤ I(f) − ⟨p, f⟩` for all `g`
  (geometric Hahn–Banach applied to the strict hypograph, which is open
  because `I` is `1`-Lipschitz in the sup norm, `lipschitz`).
* `le_dot_add_cost`, `exists_eq_dot_add_cost` (**MMR representation**):
  `I(f) ≤ ⟨p, f⟩ + c(p)` for every `p` in the domain of `c`, with equality for
  some such `p`, so the minimum is attained.
* `cost_nonneg`, `exists_cost_eq_zero`: the index is nonnegative and grounded.
* `isProb_of_inDom`: the domain of `c` consists of probabilities, so the
  minimum is over `Δ(S)`; `convex_inDom`, `cost_convex`: the domain is convex
  and `c` is convex on it.
* `isVariationalFunctional_expected`: expected utility is a variational
  functional, with index `0` at its prior (`cost_expected_self`) and `+∞`
  elsewhere (`expected_inDom_iff`); non-vacuity.

The derivation of `I` from MMR's preference axioms (the "niveloid" step) and
the uniqueness of the minimal index and lower semicontinuity of `c` are not
formalized.
-/
module

public import EconLean.Behavioral.Logit
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

@[expose] public section

noncomputable section

namespace Econ

namespace Variational

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- MMR's functional: monotone, constant additive, normalized and concave. -/
structure IsVariationalFunctional (I : (S → ℝ) → ℝ) : Prop where
  mono : Monotone I
  add_const : ∀ f (k : ℝ), I (f + fun _ => k) = I f + k
  zero : I 0 = 0
  concave : ConcaveOn ℝ Set.univ I

/-- `⟨p, f⟩`. -/
def dot (p f : S → ℝ) : ℝ := ∑ s, p s * f s

/-- `p` is in the effective domain of the ambiguity index. -/
def InDom (I : (S → ℝ) → ℝ) (p : S → ℝ) : Prop := BddAbove (Set.range fun g => I g - dot p g)

/-- The ambiguity index `c(p) = sup_g (I(g) − ⟨p, g⟩)` (meaningful on `InDom`). -/
def cost (I : (S → ℝ) → ℝ) (p : S → ℝ) : ℝ := ⨆ g, (I g - dot p g)

variable {I : (S → ℝ) → ℝ}

omit [DecidableEq S] in
/-- A niveloid is `1`-Lipschitz in the sup norm. -/
theorem lipschitz (hI : IsVariationalFunctional I) : LipschitzWith 1 I := by
  refine LipschitzWith.of_le_add fun x y => ?_
  have hle : x ≤ y + fun _ => dist x y := fun s => by
    have h1 := dist_le_pi_dist x y s
    rw [Real.dist_eq] at h1
    simp only [Pi.add_apply]
    linarith [le_abs_self (x s - y s)]
  calc I x ≤ I (y + fun _ => dist x y) := hI.mono hle
    _ = I y + dist x y := hI.add_const y _

/-- Coordinates of a linear functional on `S → ℝ`. -/
theorem linear_eq_sum (L : (S → ℝ) →L[ℝ] ℝ) (x : S → ℝ) :
    L x = ∑ s, x s * L (fun j => if s = j then 1 else 0) := by
  have := LinearMap.pi_apply_eq_sum_univ L.toLinearMap x
  simpa [smul_eq_mul] using this

/-- **Supergradients are probabilities.** -/
theorem exists_supergradient (hI : IsVariationalFunctional I) (f : S → ℝ) :
    ∃ p, Logit.IsProb p ∧ ∀ g, I g - dot p g ≤ I f - dot p f := by
  -- the strict hypograph is open and convex
  set H : Set ((S → ℝ) × ℝ) := {x | x.2 < I x.1}
  have hcont : Continuous I := (lipschitz hI).continuous
  have hopen : IsOpen H := isOpen_lt continuous_snd (hcont.comp continuous_fst)
  have hconv : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [H, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hx hy ⊢
    have hc := hI.concave.2 (Set.mem_univ x.1) (Set.mem_univ y.1) ha hb hab
    simp only [smul_eq_mul] at hc
    rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_add] at hab
      subst hab
      simp only [zero_mul, zero_add, one_mul, zero_smul, one_smul] at hc ⊢
      exact hy
    · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]
  have hnot : (f, I f) ∉ H := by simp [H]
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hconv hopen hnot
  -- decompose `φ (g, t) = L g + t α`
  set L : (S → ℝ) →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ (S → ℝ) ℝ)
  set α : ℝ := φ (0, 1)
  have hφe : ∀ g t, φ (g, t) = L g + t * α := fun g t => by
    have : ((g, t) : (S → ℝ) × ℝ) = (g, 0) + t • ((0 : S → ℝ), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have hsep : ∀ g t, t < I g → L g + t * α < L f + I f * α := fun g t ht => by
    rw [← hφe, ← hφe]; exact hφ (g, t) ht
  have hα : 0 < α := by
    have := hsep f (I f - 1) (by linarith)
    nlinarith
  -- the supergradient `q`
  set e : S → S → ℝ := fun s j => if s = j then 1 else 0
  set q : S → ℝ := fun s => -L (e s) / α
  have hsup : ∀ g, I g ≤ I f + dot q g - dot q f := by
    intro g
    have hkey : dot q g - dot q f = (L f - L g) / α := by
      rw [linear_eq_sum L f, linear_eq_sum L g]
      simp only [dot, q, e, ← sum_sub_distrib, sum_div]
      refine sum_congr rfl fun s _ => ?_
      field_simp
      ring
    rw [add_sub_assoc, hkey]
    refine le_of_forall_lt fun c hc => ?_
    have := hsep g c hc
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hα]
    linarith
  have hdot_e : ∀ s, dot q (e s) = q s := fun s => by
    simp [dot, e]
  have hdot_add : ∀ g h, dot q (g + h) = dot q g + dot q h := fun g h => by
    simp [dot, mul_add, sum_add_distrib]
  have hdot_const : ∀ k : ℝ, dot q (fun _ => k) = k * ∑ s, q s := fun k => by
    simp only [dot, mul_sum]; exact sum_congr rfl fun s _ => mul_comm _ _
  refine ⟨q, ⟨fun s => ?_, ?_⟩, fun g => by linarith [hsup g]⟩
  · have h1 := hsup (f + e s)
    have h2 : I f ≤ I (f + e s) := hI.mono fun j => by
      simp only [Pi.add_apply, e]; split_ifs <;> linarith
    rw [hdot_add, hdot_e] at h1
    linarith
  · have h1 := hsup (f + fun _ => 1)
    have h2 := hsup (f + fun _ => -1)
    rw [hI.add_const, hdot_add, hdot_const] at h1 h2
    linarith

omit [DecidableEq S] in
theorem le_cost {p : S → ℝ} (hp : InDom I p) (f : S → ℝ) : I f - dot p f ≤ cost I p :=
  le_ciSup (f := fun g => I g - dot p g) hp f

omit [DecidableEq S] in
/-- `I(f) ≤ ⟨p, f⟩ + c(p)` on the domain of `c`. -/
theorem le_dot_add_cost {p : S → ℝ} (hp : InDom I p) (f : S → ℝ) :
    I f ≤ dot p f + cost I p := by
  linarith [le_cost hp f]

/-- **MMR variational representation**: the minimum of `⟨p, f⟩ + c(p)` over
probabilities in the domain of `c` is attained and equals `I(f)`. -/
theorem exists_eq_dot_add_cost (hI : IsVariationalFunctional I) (f : S → ℝ) :
    ∃ p, Logit.IsProb p ∧ InDom I p ∧ I f = dot p f + cost I p := by
  obtain ⟨p, hp, hsg⟩ := exists_supergradient hI f
  have hdom : InDom I p := ⟨I f - dot p f, by rintro _ ⟨g, rfl⟩; exact hsg g⟩
  refine ⟨p, hp, hdom, ?_⟩
  have h1 : cost I p ≤ I f - dot p f := ciSup_le hsg
  linarith [le_cost hdom f]

omit [DecidableEq S] in
/-- The ambiguity index is nonnegative. -/
theorem cost_nonneg (hI : IsVariationalFunctional I) {p : S → ℝ} (hp : InDom I p) : 0 ≤ cost I p := by
  have := le_cost hp 0
  simpa [dot, hI.zero] using this

/-- The ambiguity index is grounded: it vanishes at some probability. -/
theorem exists_cost_eq_zero (hI : IsVariationalFunctional I) :
    ∃ p, Logit.IsProb p ∧ InDom I p ∧ cost I p = 0 := by
  obtain ⟨p, hp, hdom, h⟩ := exists_eq_dot_add_cost hI 0
  refine ⟨p, hp, hdom, ?_⟩
  simpa [dot, hI.zero] using h.symm

/-- The domain of the ambiguity index consists of probability vectors. -/
theorem isProb_of_inDom (hI : IsVariationalFunctional I) {p : S → ℝ} (hp : InDom I p) :
    Logit.IsProb p := by
  obtain ⟨C, hC⟩ := hp
  have hval : ∀ g, I g - dot p g ≤ C := fun g => hC ⟨g, rfl⟩
  have hconst : ∀ k : ℝ, I (fun _ => k) = k := fun k => by
    have := hI.add_const 0 k
    simpa [hI.zero] using this
  have hC0 : 0 ≤ C := by simpa [dot, hI.zero] using hval 0
  refine ⟨fun s => ?_, ?_⟩
  · by_contra hs
    rw [not_le] at hs
    set t : ℝ := (C + 1) / (-p s)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    set g : S → ℝ := fun j => if s = j then t else 0
    have h1 : 0 ≤ I g := by
      rw [← hI.zero]; exact hI.mono fun j => by simp only [g]; split_ifs <;> simp [ht]
    have h2 : dot p g = p s * t := by simp [dot, g]
    have h3 : p s * t = -(C + 1) := by
      simp only [t]; field_simp; rw [div_self hs.ne]
    have := hval g
    linarith
  · by_contra hs
    set k : ℝ := (C + 1) / (1 - ∑ s, p s)
    have hk : k * (1 - ∑ s, p s) = C + 1 := div_mul_cancel₀ _ (sub_ne_zero.2 (Ne.symm hs))
    have := hval (fun _ => k)
    rw [hconst] at this
    have e : dot p (fun _ => k) = k * ∑ s, p s := by
      simp only [dot, mul_sum]; exact sum_congr rfl fun s _ => mul_comm _ _
    rw [e] at this
    nlinarith

omit [DecidableEq S] in
/-- The domain of the ambiguity index is convex and the index is convex on it. -/
theorem cost_convex_combo {p₁ p₂ : S → ℝ} (h₁ : InDom I p₁) (h₂ : InDom I p₂) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    InDom I (a • p₁ + b • p₂) ∧ cost I (a • p₁ + b • p₂) ≤ a * cost I p₁ + b * cost I p₂ := by
  have key : ∀ g, I g - dot (a • p₁ + b • p₂) g ≤ a * cost I p₁ + b * cost I p₂ := by
    intro g
    have e : I g - dot (a • p₁ + b • p₂) g =
        a * (I g - dot p₁ g) + b * (I g - dot p₂ g) := by
      have : I g = a * I g + b * I g := by rw [← add_mul, hab, one_mul]
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
        mul_assoc, ← mul_sum]
      linarith
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_cost h₁ g) ha)
      (mul_le_mul_of_nonneg_left (le_cost h₂ g) hb)
  exact ⟨⟨_, by rintro _ ⟨g, rfl⟩; exact key g⟩, ciSup_le key⟩

omit [DecidableEq S] in
theorem convex_inDom : Convex ℝ {p : S → ℝ | InDom I p} :=
  fun _ h₁ _ h₂ _ _ ha hb hab => (cost_convex_combo h₁ h₂ ha hb hab).1

omit [DecidableEq S] in
theorem cost_convex : ConvexOn ℝ {p : S → ℝ | InDom I p} (cost I) :=
  ⟨convex_inDom, fun _ h₁ _ h₂ _ _ ha hb hab => by
    simpa [smul_eq_mul] using (cost_convex_combo h₁ h₂ ha hb hab).2⟩

omit [DecidableEq S] in
/-- Non-vacuity: subjective expected utility is a niveloid. -/
theorem isVariationalFunctional_expected {q : S → ℝ} (hq : Logit.IsProb q) :
    IsVariationalFunctional (fun f => dot q f) where
  mono f g h := sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hq.1 s)
  add_const f k := by simp [dot, mul_add, sum_add_distrib, ← sum_mul, hq.2]
  zero := by simp [dot]
  concave := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
    simp only [dot, smul_eq_mul, Pi.add_apply, Pi.smul_apply, mul_sum]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring

omit [DecidableEq S] in
/-- For expected utility with prior `q`, the index vanishes at `q`. -/
theorem cost_expected_self (q : S → ℝ) :
    InDom (fun f => dot q f) q ∧ cost (fun f => dot q f) q = 0 := by
  refine ⟨⟨0, by rintro _ ⟨g, rfl⟩; simp⟩, ?_⟩
  simp [cost]

omit [DecidableEq S] in
/-- For expected utility with prior `q`, the index is finite only at `q`:
elsewhere it is `+∞`. -/
theorem expected_inDom_iff (q p : S → ℝ) : InDom (fun f => dot q f) p ↔ p = q := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hpos : 0 < ∑ s, (q s - p s) ^ 2 := by
      obtain ⟨s, hs⟩ : ∃ s, p s ≠ q s := by
        by_contra h
        exact hne (funext fun s => by by_contra h'; exact h ⟨s, h'⟩)
      have hd : q s - p s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      have h1 : 0 < (q s - p s) ^ 2 := by positivity
      exact lt_of_lt_of_le h1
        (single_le_sum (f := fun s => (q s - p s) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ s))
    set t : ℝ := (|C| + 1) / ∑ s, (q s - p s) ^ 2
    have h := hC ⟨fun s => t * (q s - p s), rfl⟩
    have e : dot q (fun s => t * (q s - p s)) - dot p (fun s => t * (q s - p s)) =
        t * ∑ s, (q s - p s) ^ 2 := by
      simp only [dot, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun s _ => by ring
    simp only at h
    rw [e, div_mul_cancel₀ _ hpos.ne'] at h
    linarith [le_abs_self C]
  · rintro rfl
    exact (cost_expected_self p).1

end Variational

end Econ
