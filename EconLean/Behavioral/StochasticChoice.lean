/-
# Stochastic choice: Luce, random utility, Block–Marschak

References.
* R. D. Luce (1959), *Individual Choice Behavior*: the choice axiom.
* H. D. Block and J. Marschak (1960), "Random orderings and stochastic theories
  of responses": the Block–Marschak polynomials.
* J.-C. Falmagne (1978), *J. Math. Psych.* 18: nonnegative BM polynomials
  characterize random utility.
* D. McFadden (1974): logit is a random utility model.

**Setting.** A finite set of alternatives `X`. A stochastic choice rule gives,
for every nonempty menu `A ⊆ X`, a probability `P A a` of choosing `a`,
supported on `A` (`IsChoiceRule`).

**Luce.** `luce w A a = w a / Σ_{b∈A} w b` for positive weights `w`. It
satisfies IIA (`luce_iia`: odds between two alternatives do not depend on the
menu) and Luce's choice axiom (`luce_choiceAxiom`). **Luce's theorem**
(`eq_luce_of_choiceAxiom`): a choice rule with full support on every menu that
satisfies the choice axiom is Luce, with `w a = P X a`. Logit (`softmax`) is
Luce with `w = exp(v/λ)` (`softmax_eq_luce`).

**Random utility.** A random utility model is a probability `μ` over strict
rankings (`Ranking X := X ≃ Fin |X|`, smaller rank is better); `rumP μ A a`
is the probability that `a` is the best element of `A`. RUMs are choice rules
(`rumP_isChoiceRule`) and satisfy regularity (`rumP_regularity`: adding
alternatives never raises a choice probability).

**Block–Marschak.** `bm P A a = Σ_{A ⊆ B} (-1)^{|B∖A|} P B a`. For a RUM,
`bm` is the probability that the alternatives ranked above `a` are exactly
those outside `A` (`bm_rumP`), so all BM polynomials are nonnegative
(`bm_rumP_nonneg`, Block–Marschak's necessity theorem).

Falmagne's sufficiency theorem (nonnegative BM polynomials ⇒ RUM) is in
`Falmagne.lean`. **Not formalized:** McFadden's derivation of logit from
Gumbel shocks.
-/
module

public import EconLean.Behavioral.Logit
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace Econ

namespace StochasticChoice

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A stochastic choice rule: on each nonempty menu, a probability supported on
the menu. -/
def IsChoiceRule (P : Finset X → X → ℝ) : Prop :=
  ∀ A : Finset X, A.Nonempty →
    (∀ a, 0 ≤ P A a) ∧ (∀ a, a ∉ A → P A a = 0) ∧ ∑ a ∈ A, P A a = 1

/-! ### Luce -/

/-- The Luce rule with weights `w`. -/
noncomputable def luce (w : X → ℝ) (A : Finset X) (a : X) : ℝ :=
  if a ∈ A then w a / ∑ b ∈ A, w b else 0

omit [Fintype X] in
theorem luce_isChoiceRule {w : X → ℝ} (hw : ∀ a, 0 < w a) : IsChoiceRule (luce w) := by
  intro A hA
  have hS : 0 < ∑ b ∈ A, w b := sum_pos (fun b _ => hw b) hA
  refine ⟨fun a => ?_, fun a ha => by simp [luce, ha], ?_⟩
  · unfold luce; split_ifs
    · exact div_nonneg (hw a).le hS.le
    · exact le_rfl
  · rw [sum_congr rfl (fun a ha => by rw [luce, ite_eq_left ha]), ← sum_div, div_self hS.ne']

omit [Fintype X] in
/-- **IIA**: the odds of `a` against `b` are `w a / w b` on every menu
containing both. -/
theorem luce_iia {w : X → ℝ} (hw : ∀ a, 0 < w a) {A : Finset X} {a b : X} (ha : a ∈ A)
    (hb : b ∈ A) : luce w A a / luce w A b = w a / w b := by
  have hS : 0 < ∑ c ∈ A, w c := sum_pos (fun c _ => hw c) ⟨a, ha⟩
  simp only [luce, ha, hb, ite_true]
  field_simp [hS.ne', (hw b).ne']

/-- Probability that the choice from `A` lies in `B`. -/
noncomputable def probSet (P : Finset X → X → ℝ) (A B : Finset X) : ℝ := ∑ b ∈ B, P A b

/-- **Luce's choice axiom**: for `a ∈ B ⊆ A`, choosing `a` from `A` is choosing
something in `B` and then `a` from `B`. -/
def ChoiceAxiom (P : Finset X → X → ℝ) : Prop :=
  ∀ A B : Finset X, B ⊆ A → ∀ a ∈ B, P A a = probSet P A B * P B a

omit [Fintype X] in
theorem luce_choiceAxiom {w : X → ℝ} (hw : ∀ a, 0 < w a) : ChoiceAxiom (luce w) := by
  intro A B hBA a ha
  have hSA : 0 < ∑ c ∈ A, w c := sum_pos (fun c _ => hw c) ⟨a, hBA ha⟩
  have hSB : 0 < ∑ c ∈ B, w c := sum_pos (fun c _ => hw c) ⟨a, ha⟩
  have hp : probSet (luce w) A B = (∑ c ∈ B, w c) / ∑ c ∈ A, w c := by
    rw [probSet, sum_congr rfl (fun c hc => by rw [luce, ite_eq_left (hBA hc)]), ← sum_div]
  rw [hp]
  simp only [luce, ha, hBA ha, ite_true]
  field_simp

/-- **Luce's theorem.** A choice rule that gives every alternative on a menu
positive probability and satisfies the choice axiom is a Luce rule, with
weights the choice probabilities from the grand menu. -/
theorem eq_luce_of_choiceAxiom {P : Finset X → X → ℝ} (hP : IsChoiceRule P)
    (hpos : ∀ A : Finset X, ∀ a ∈ A, 0 < P A a) (hax : ChoiceAxiom P) {A : Finset X}
    (hA : A.Nonempty) (a : X) :
    P A a = luce (fun b => P univ b) A a := by
  by_cases ha : a ∈ A
  · have h := hax univ A (subset_univ A) a ha
    have hpA : 0 < probSet P univ A := sum_pos (fun b hb => hpos univ b (mem_univ b)) ⟨a, ha⟩
    rw [luce, ite_eq_left ha, h]
    change P A a = probSet P univ A * P A a / probSet P univ A
    field_simp
  · rw [luce, ite_eq_right ha, (hP A hA).2.1 a ha]

/-- **Logit is Luce** with weights `exp (v / λ)`. Here `λ` is a temperature
(`Logit.softmax`), not the QRE precision (`logitResponse` uses `exp (λ U)`).
At `λ = 0` both sides read `v / 0 = 0` and are uniform, a Lean convention. -/
theorem softmax_eq_luce (lam : ℝ) (v : X → ℝ) (a : X) :
    Logit.softmax lam v a = luce (fun b => Real.exp (v b / lam)) univ a := by
  simp [Logit.softmax, luce]

/-! ### Random utility -/

/-- A strict ranking: `r a < r b` means `a` is ranked above `b`. -/
abbrev Ranking (X : Type*) [Fintype X] := X ≃ Fin (Fintype.card X)

/-- `a` is the best element of `A` under `r`. -/
def IsTop (r : Ranking X) (A : Finset X) (a : X) : Prop := a ∈ A ∧ ∀ b ∈ A, r a ≤ r b

instance (r : Ranking X) (A : Finset X) (a : X) : Decidable (IsTop r A a) := by
  unfold IsTop; infer_instance

/-- A random utility model: a probability over rankings. -/
def IsRUM (μ : Ranking X → ℝ) : Prop := (∀ r, 0 ≤ μ r) ∧ ∑ r, μ r = 1

/-- Choice probabilities of a random utility model. -/
noncomputable def rumP (μ : Ranking X → ℝ) (A : Finset X) (a : X) : ℝ :=
  ∑ r, μ r * if IsTop r A a then 1 else 0

/-- On a nonempty menu exactly one alternative is best. -/
theorem sum_isTop (r : Ranking X) {A : Finset X} (hA : A.Nonempty) :
    ∑ a ∈ A, (if IsTop r A a then (1 : ℝ) else 0) = 1 := by
  obtain ⟨a, ha, hmin⟩ := A.exists_min_image r hA
  rw [sum_eq_single_of_mem a ha]
  · rw [ite_eq_left ⟨ha, hmin⟩]
  · intro b hb hba
    rw [ite_eq_right]
    rintro ⟨-, hb'⟩
    exact hba (r.injective (le_antisymm (hb' a ha) (hmin b hb)))

theorem rumP_isChoiceRule {μ : Ranking X → ℝ} (hμ : IsRUM μ) : IsChoiceRule (rumP μ) := by
  intro A hA
  refine ⟨fun a => sum_nonneg fun r _ => mul_nonneg (hμ.1 r) (by split_ifs <;> norm_num),
    fun a ha => sum_eq_zero fun r _ => by rw [ite_eq_right (fun h => ha h.1), mul_zero], ?_⟩
  simp only [rumP]
  rw [sum_comm]
  simp_rw [← mul_sum, sum_isTop _ hA, mul_one]
  exact hμ.2

/-- **Regularity**: adding alternatives never raises a RUM choice
probability. -/
theorem rumP_regularity {μ : Ranking X → ℝ} (hμ : IsRUM μ) {A B : Finset X} (hAB : A ⊆ B)
    {a : X} (ha : a ∈ A) : rumP μ B a ≤ rumP μ A a := by
  refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (hμ.1 r)
  by_cases h : IsTop r B a
  · rw [ite_eq_left h, ite_eq_left ⟨ha, fun b hb => h.2 b (hAB hb)⟩]
  · rw [ite_eq_right h]; split_ifs <;> norm_num

/-! ### Block–Marschak polynomials -/

/-- The Block–Marschak polynomial `Σ_{A ⊆ B} (-1)^{|B∖A|} P B a`, indexing
`B = A ∪ C` by `C ⊆ X ∖ A`. -/
noncomputable def bm (P : Finset X → X → ℝ) (A : Finset X) (a : X) : ℝ :=
  ∑ C ∈ (univ \ A).powerset, (-1 : ℝ) ^ C.card * P (A ∪ C) a

theorem isTop_union (r : Ranking X) {A C : Finset X} {a : X} (ha : a ∈ A) :
    IsTop r (A ∪ C) a ↔ IsTop r A a ∧ ∀ c ∈ C, r a ≤ r c := by
  constructor
  · rintro ⟨-, h⟩
    exact ⟨⟨ha, fun b hb => h b (mem_union_left _ hb)⟩, fun c hc => h c (mem_union_right _ hc)⟩
  · rintro ⟨⟨ha, h1⟩, h2⟩
    exact ⟨mem_union_left _ ha, fun b hb => (mem_union.1 hb).elim (h1 b) (h2 b)⟩

/-- For one ranking, the alternating sum collapses: it is `1` exactly when `a`
is best in `A` and every alternative outside `A` is ranked above `a`. -/
theorem bm_rank_term (r : Ranking X) {A : Finset X} {a : X} (ha : a ∈ A) :
    ∑ C ∈ (univ \ A).powerset, (-1 : ℝ) ^ C.card * (if IsTop r (A ∪ C) a then 1 else 0) =
      if IsTop r A a ∧ ∀ c, c ∉ A → r c < r a then 1 else 0 := by
  set D := (univ \ A).filter (fun c => r a ≤ r c) with hD
  set t : ℝ := if IsTop r A a then 1 else 0
  have step : ∀ C ∈ (univ \ A).powerset,
      (-1 : ℝ) ^ C.card * (if IsTop r (A ∪ C) a then 1 else 0) =
        t * (if C ⊆ D then (-1 : ℝ) ^ C.card else 0) := by
    intro C hC
    rw [mem_powerset] at hC
    have hCD : C ⊆ D ↔ ∀ c ∈ C, r a ≤ r c :=
      ⟨fun h c hc => (mem_filter.1 (h hc)).2, fun h c hc => mem_filter.2 ⟨hC hc, h c hc⟩⟩
    by_cases h1 : IsTop r A a <;> by_cases h2 : ∀ c ∈ C, r a ≤ r c <;>
      simp [t, isTop_union r ha, h1, h2, hCD]
  rw [sum_congr rfl step, ← mul_sum, ← sum_filter]
  have hfil : ((univ \ A).powerset.filter (fun C => C ⊆ D)) = D.powerset := by
    ext C
    simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans (filter_subset _ _), h⟩⟩
  rw [hfil]
  have hint : (∑ C ∈ D.powerset, (-1 : ℝ) ^ C.card) = if D = ∅ then 1 else 0 := by
    have := Finset.sum_powerset_neg_one_pow_card (x := D)
    split_ifs at this ⊢ <;> exact_mod_cast this
  rw [hint]
  have hDe : D = ∅ ↔ ∀ c, c ∉ A → r c < r a := by
    rw [hD, filter_eq_empty_iff]
    simp only [mem_sdiff, mem_univ, true_and, not_le]
  by_cases h1 : IsTop r A a <;> by_cases h2 : ∀ c, c ∉ A → r c < r a <;>
    simp [t, h1, h2, hDe]

/-- **Block–Marschak polynomials of a RUM**: the probability that `a` is best
in `A` and every alternative outside `A` is ranked above `a`. -/
theorem bm_rumP (μ : Ranking X → ℝ) {A : Finset X} {a : X} (ha : a ∈ A) :
    bm (rumP μ) A a = ∑ r, μ r * if IsTop r A a ∧ ∀ c, c ∉ A → r c < r a then 1 else 0 := by
  unfold bm rumP
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [← bm_rank_term r ha, mul_sum]
  exact sum_congr rfl fun C _ => by ring

/-- **Block–Marschak (1960)**: every BM polynomial of a random utility model is
nonnegative. -/
theorem bm_rumP_nonneg {μ : Ranking X → ℝ} (hμ : IsRUM μ) {A : Finset X} {a : X} (ha : a ∈ A) :
    0 ≤ bm (rumP μ) A a := by
  rw [bm_rumP μ ha]
  exact sum_nonneg fun r _ => mul_nonneg (hμ.1 r) (by split_ifs <;> norm_num)

/-- Non-vacuity: a point mass on one ranking is a RUM. -/
theorem isRUM_pointMass (r₀ : Ranking X) : IsRUM (fun r => if r = r₀ then 1 else 0) :=
  ⟨fun r => by dsimp only; split_ifs <;> norm_num, by simp⟩

end StochasticChoice

end Econ
