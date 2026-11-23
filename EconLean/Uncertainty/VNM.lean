/-
# Lotteries and the von Neumann–Morgenstern expected utility theorem

MWG §6.B (Defs. 6.B.1–6.B.5, Props. 6.B.2–6.B.3).

**The economics.** There is a finite set `C` of outcomes. A (simple)
*lottery* is a probability vector `L = (L_c)_{c ∈ C}`, i.e. a point of the
standard simplex `Δ(C)`. The decision maker has a preference `≿` over
lotteries. It satisfies
* **rationality**: complete and transitive (MWG Ch. 1);
* **continuity** (Def. 6.B.3): for all `L, L', L''`, the sets
  `{α ∈ [0,1] | αL + (1-α)L' ≿ L''}` and `{α ∈ [0,1] | L'' ≿ αL + (1-α)L'}`
  are closed;
* **independence** (Def. 6.B.4): for all `L, L', L''` and `α ∈ (0,1)`,
  `L ≿ L' ⟺ αL + (1-α)L'' ≿ αL' + (1-α)L''`.

**vN–M theorem** (Prop. 6.B.3): these axioms hold iff `≿` has an expected
utility representation: there are numbers `u_c` with
`L ≿ L' ⟺ ∑ L_c u_c ≥ ∑ L'_c u_c`.
**Uniqueness** (Prop. 6.B.2): `u` is unique up to a positive affine
transformation (when `≿` is not total indifference).

**Proof outline** (follows MWG, with one Lean-friendly change):
1. A best outcome `c̄` and a worst outcome `c̲` exist (finite set).
2. Independence gives *betweenness*: the lotteries below `δ_c̄` form a convex
   set; since every lottery is a convex combination of degenerate ones,
   `δ_c̄ ≿ L ≿ δ_c̲` for all `L`.
3. If `δ_c̄ ∼ δ_c̲` everything is indifferent and `u = 0` works.
4. Otherwise, `α ↦ αδ_c̄ + (1-α)δ_c̲` is strictly increasing in `≻`, and by
   continuity + connectedness of `[0,1]` each `L` is indifferent to exactly one
   such mixture; call its weight `U(L)`. `U` represents `≿`.
5. Independence makes `U` *mixture-linear*.
6. A mixture-linear function on the simplex is both convex and concave,
   so two applications of **Jensen's inequality** (Mathlib) give
   `U(L) = ∑ L_c U(δ_c)`. (MWG does this step by induction.)

**Prior Lean work.** J. Li (arXiv 2506.07066) states vN–M in Lean 4, but the
representation theorem is not fully proved there (placeholders and an
axiom). This file is an independent, complete proof.

**Lean conventions.** Lotteries live in the ambient space `C → ℝ` with
membership in the simplex `lotteries C`; the preference is a relation on
`C → ℝ` whose values off the simplex are irrelevant (every axiom and the
representation only quantify over lotteries). Rationality reuses the
`Rational` structure of `Preferences/Basic.lean` on the subtype of lotteries.
-/
module

public import EconLean.Preferences.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace Econ

open Set

variable {C : Type*}

/-! ### Lotteries -/

/-- The compound lottery `αL + (1-α)L'`, reduced to a simple lottery
(MWG Def. 6.B.2 and the reduction discussion after it). -/
def mix (α : ℝ) (L L' : C → ℝ) : C → ℝ := α • L + (1 - α) • L'

@[simp] theorem mix_one (L L' : C → ℝ) : mix 1 L L' = L := by simp [mix]
@[simp] theorem mix_zero (L L' : C → ℝ) : mix 0 L L' = L' := by simp [mix]
@[simp] theorem mix_self (α : ℝ) (L : C → ℝ) : mix α L L = L := by
  funext c; simp [mix]; ring

theorem mix_comm (α : ℝ) (L L' : C → ℝ) : mix α L L' = mix (1 - α) L' L := by
  funext c; simp [mix]; ring

/-- Reals in `[0,1]` mixing two numbers in `[0,1]` stay in `[0,1]`. -/
theorem mem_Icc_mix {β a a' : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (ha' : a' ∈ Set.Icc (0 : ℝ) 1) : β * a + (1 - β) * a' ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨ha0', ha1'⟩ := ha'
  constructor <;> nlinarith

variable [Fintype C]

/-- The set of lotteries over `C`: probability vectors, i.e. nonnegative
weights summing to one (MWG Def. 6.B.1). -/
def lotteries (C : Type*) [Fintype C] : Set (C → ℝ) := {L | (∀ c, 0 ≤ L c) ∧ ∑ c, L c = 1}

/-- The set of lotteries is convex. -/
theorem convex_lotteries : Convex ℝ (lotteries C) := by
  intro L hL L' hL' a b ha hb hab
  refine ⟨fun c => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hL.1 c)) (mul_nonneg hb (hL'.1 c))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hL.2, hL'.2, mul_one, hab]

/-- The degenerate lottery `δ_c` giving outcome `c` for sure. -/
def degenerate [DecidableEq C] (c : C) : C → ℝ := fun j => if c = j then 1 else 0

/-- Expected utility `U(L) = ∑_c L_c u_c` (MWG Def. 6.B.5). -/
def expectedUtility (u : C → ℝ) (L : C → ℝ) : ℝ := ∑ c, L c * u c

/-- The **vN–M axioms** on a preference over lotteries (MWG 6.B.3–6.B.4). -/
structure VNMAxioms (R : (C → ℝ) → (C → ℝ) → Prop) : Prop where
  /-- Complete and transitive on lotteries. -/
  rational : Rational (fun L L' : lotteries C => R L L')
  /-- Continuity (MWG Def. 6.B.3). -/
  continuity : ∀ L ∈ lotteries C, ∀ L' ∈ lotteries C, ∀ L'' ∈ lotteries C,
    IsClosed {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ R (mix α L L') L''} ∧
    IsClosed {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ R L'' (mix α L L')}
  /-- Independence (MWG Def. 6.B.4). -/
  independence : ∀ L ∈ lotteries C, ∀ L' ∈ lotteries C, ∀ L'' ∈ lotteries C,
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, (R L L' ↔ R (mix α L L'') (mix α L' L''))

/-- `u` gives an **expected utility representation** of `R` on lotteries. -/
def HasEURepresentation (R : (C → ℝ) → (C → ℝ) → Prop) (u : C → ℝ) : Prop :=
  ∀ L ∈ lotteries C, ∀ L' ∈ lotteries C, (R L L' ↔ expectedUtility u L' ≤ expectedUtility u L)

/-! ### Algebra of mixtures -/

theorem mix_mem {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {L L' : C → ℝ} (hL : L ∈ lotteries C)
    (hL' : L' ∈ lotteries C) : mix α L L' ∈ lotteries C :=
  convex_lotteries hL hL' hα.1 (sub_nonneg.2 hα.2) (by ring)

theorem expectedUtility_mix (u : C → ℝ) (α : ℝ) (L L' : C → ℝ) :
    expectedUtility u (mix α L L') = α * expectedUtility u L + (1 - α) * expectedUtility u L' := by
  simp only [expectedUtility, mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expectedUtility_degenerate [DecidableEq C] (u : C → ℝ) (c : C) :
    expectedUtility u (degenerate c) = u c := by
  simp [expectedUtility, degenerate]

theorem degenerate_mem [DecidableEq C] (c : C) : degenerate c ∈ lotteries C := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold degenerate; split_ifs <;> norm_num
  · simp [degenerate]

/-- Every lottery is the convex combination of degenerate lotteries. -/
theorem sum_degenerate [DecidableEq C] (L : C → ℝ) : ∑ c, L c • degenerate c = L :=
  (pi_eq_sum_univ L).symm

/-- On a lottery, expected utility of `a u + b` is `a U + b`. -/
theorem expectedUtility_affine {L : C → ℝ} (hL : L ∈ lotteries C) (u : C → ℝ) (a b : ℝ) :
    expectedUtility (fun c => a * u c + b) L = a * expectedUtility u L + b := by
  have h1 : ∑ c, L c = 1 := hL.2
  simp only [expectedUtility, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← Finset.sum_mul, h1, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### The easy direction: expected utility satisfies the axioms -/

/-- **vN–M, sufficiency.** An expected-utility preference satisfies the
vN–M axioms. -/
theorem vnmAxioms_of_eu {R : (C → ℝ) → (C → ℝ) → Prop} {u : C → ℝ}
    (hu : HasEURepresentation R u) : VNMAxioms R := by
  refine ⟨⟨fun L L' => ?_, fun {L L' L''} h1 h2 => ?_⟩, fun L hL L' hL' L'' hL'' => ?_,
    fun L hL L' hL' L'' hL'' α hα => ?_⟩
  · rw [hu L L.2 L' L'.2, hu L' L'.2 L L.2]; exact le_total _ _
  · rw [hu _ L.2 _ L'.2] at h1; rw [hu _ L'.2 _ L''.2] at h2
    rw [hu _ L.2 _ L''.2]; exact h2.trans h1
  · -- Both sets are `[0,1] ∩ {α | affine function ≤ constant}`, hence closed.
    have hcont : Continuous fun α : ℝ =>
        α * expectedUtility u L + (1 - α) * expectedUtility u L' := by fun_prop
    constructor
    · have : {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ R (mix α L L') L''} =
          Icc 0 1 ∩ {α | expectedUtility u L'' ≤
            α * expectedUtility u L + (1 - α) * expectedUtility u L'} := by
        ext α
        simp only [mem_ofPred_eq, mem_inter_iff]
        exact and_congr_right fun h => by
          rw [hu _ (mix_mem h hL hL') _ hL'', expectedUtility_mix]
      rw [this]; exact isClosed_Icc.inter (isClosed_le continuous_const hcont)
    · have : {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ R L'' (mix α L L')} =
          Icc 0 1 ∩ {α | α * expectedUtility u L + (1 - α) * expectedUtility u L' ≤
            expectedUtility u L''} := by
        ext α
        simp only [mem_ofPred_eq, mem_inter_iff]
        exact and_congr_right fun h => by
          rw [hu _ hL'' _ (mix_mem h hL hL'), expectedUtility_mix]
      rw [this]; exact isClosed_Icc.inter (isClosed_le hcont continuous_const)
  · have hα' : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα.1.le, hα.2.le⟩
    rw [hu _ hL _ hL', hu _ (mix_mem hα' hL hL'') _ (mix_mem hα' hL' hL''),
      expectedUtility_mix, expectedUtility_mix, add_le_add_iff_right,
      mul_le_mul_iff_right₀ hα.1]

/-! ### The hard direction -/

/-- A total transitive relation has a top element on a nonempty finset. -/
theorem exists_top_of_total_finset {α : Type*} [DecidableEq α] (r : α → α → Prop)
    (htot : ∀ a b, r a b ∨ r b a) (htr : ∀ a b c, r a b → r b c → r a c) (s : Finset α)
    (hs : s.Nonempty) : ∃ m ∈ s, ∀ x ∈ s, r m x := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, by simp, fun x hx => ?_⟩
      have hxa : x = a := by simpa using hx
      rw [hxa]
      exact (htot a a).elim id id
    · obtain ⟨m, hm, hmx⟩ := ih hne
      rcases htot a m with ham | hma
      · refine ⟨a, by simp, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact (htot x x).elim id id
        · exact htr _ _ _ ham (hmx x hx)
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hma
        · exact hmx x hx

section Hard

variable {R : (C → ℝ) → (C → ℝ) → Prop} (hR : VNMAxioms R)
include hR

local notation "S" => lotteries C

theorem VNMAxioms.complete' {L L' : C → ℝ} (hL : L ∈ S) (hL' : L' ∈ S) : R L L' ∨ R L' L :=
  hR.rational.complete ⟨L, hL⟩ ⟨L', hL'⟩

theorem VNMAxioms.refl' {L : C → ℝ} (hL : L ∈ S) : R L L :=
  (hR.complete' hL hL).elim id id

theorem VNMAxioms.trans' {L L' L'' : C → ℝ} (hL : L ∈ S) (hL' : L' ∈ S) (hL'' : L'' ∈ S)
    (h1 : R L L') (h2 : R L' L'') : R L L'' :=
  hR.rational.trans (x := ⟨L, hL⟩) (y := ⟨L', hL'⟩) (z := ⟨L'', hL''⟩) h1 h2

/-- Independence for strict preference. -/
theorem VNMAxioms.indep_strict {L L' L'' : C → ℝ} (hL : L ∈ S) (hL' : L' ∈ S) (hL'' : L'' ∈ S)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (R L L' ∧ ¬ R L' L) ↔ (R (mix α L L'') (mix α L' L'') ∧ ¬ R (mix α L' L'') (mix α L L'')) := by
  rw [hR.independence L hL L' hL' L'' hL'' α hα, hR.independence L' hL' L hL L'' hL'' α hα]

/-- **Step 1 of MWG's proof.** If `L ≻ L'` and `α ∈ (0,1)`, then
`L ≻ αL + (1-α)L' ≻ L'`. -/
theorem VNMAxioms.strict_mix {L L' : C → ℝ} (hL : L ∈ S) (hL' : L' ∈ S)
    (hs : R L L' ∧ ¬ R L' L) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (R L (mix α L L') ∧ ¬ R (mix α L L') L) ∧ (R (mix α L L') L' ∧ ¬ R L' (mix α L L')) := by
  have hα' : 1 - α ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  constructor
  · have := (hR.indep_strict hL hL' hL hα').1 hs
    rwa [mix_self, ← mix_comm α L L'] at this
  · have := (hR.indep_strict hL hL' hL' hα).1 hs
    rwa [mix_self] at this

/-- **Betweenness (upper).** If `M ≿ L` and `M ≿ L'` then `M ≿` any mixture. -/
theorem VNMAxioms.le_mix {M L L' : C → ℝ} (hM : M ∈ S) (hL : L ∈ S) (hL' : L' ∈ S)
    (h1 : R M L) (h2 : R M L') {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) : R M (mix α L L') := by
  rcases hα.1.eq_or_lt with rfl | h0
  · simpa using h2
  rcases hα.2.eq_or_lt with rfl | h1'
  · simpa using h1
  have hα' : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1'⟩
  have hα'' : 1 - α ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hI : α ∈ Set.Icc (0 : ℝ) 1 := hα
  -- `M ≿ αM + (1-α)L'` and `αM + (1-α)L' ≿ αL + (1-α)L'`.
  have a := (hR.independence M hM L hL L' hL' α hα').1 h1
  have b := (hR.independence M hM L' hL' M hM (1 - α) hα'').1 h2
  rw [mix_self, ← mix_comm α M L'] at b
  exact hR.trans' hM (mix_mem hI hM hL') (mix_mem hI hL hL') b a

/-- **Betweenness (lower).** -/
theorem VNMAxioms.mix_le {M L L' : C → ℝ} (hM : M ∈ S) (hL : L ∈ S) (hL' : L' ∈ S)
    (h1 : R L M) (h2 : R L' M) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) : R (mix α L L') M := by
  rcases hα.1.eq_or_lt with rfl | h0
  · simpa using h2
  rcases hα.2.eq_or_lt with rfl | h1'
  · simpa using h1
  have hα' : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1'⟩
  have hα'' : 1 - α ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hI : α ∈ Set.Icc (0 : ℝ) 1 := hα
  have a := (hR.independence L hL M hM L' hL' α hα').1 h1
  have b := (hR.independence L' hL' M hM M hM (1 - α) hα'').1 h2
  rw [mix_self, ← mix_comm α M L'] at b
  exact hR.trans' (mix_mem hI hL hL') (mix_mem hI hM hL') hM a b

/-- Convexity of `{L | M ≿ L}` lets us pass to all convex combinations. -/
theorem VNMAxioms.le_of_degenerate [DecidableEq C] {M : C → ℝ} (hM : M ∈ S)
    (h : ∀ c, R M (degenerate c)) {L : C → ℝ} (hL : L ∈ S) : R M L := by
  have hconv : Convex ℝ {L | L ∈ S ∧ R M L} := by
    rintro x ⟨hx, hMx⟩ y ⟨hy, hMy⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    have hIa : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
    have : a • x + b • y = mix a x y := by rw [hb']; rfl
    rw [this]
    exact ⟨mix_mem hIa hx hy, hR.le_mix hM hx hy hMx hMy hIa⟩
  have := hconv.sum_mem (t := Finset.univ) (w := L) (z := degenerate)
    (fun c _ => hL.1 c) hL.2 (fun c _ => ⟨degenerate_mem c, h c⟩)
  rw [sum_degenerate] at this
  exact this.2

theorem VNMAxioms.degenerate_le [DecidableEq C] {M : C → ℝ} (hM : M ∈ S)
    (h : ∀ c, R (degenerate c) M) {L : C → ℝ} (hL : L ∈ S) : R L M := by
  have hconv : Convex ℝ {L | L ∈ S ∧ R L M} := by
    rintro x ⟨hx, hMx⟩ y ⟨hy, hMy⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    have hIa : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
    have : a • x + b • y = mix a x y := by rw [hb']; rfl
    rw [this]
    exact ⟨mix_mem hIa hx hy, hR.mix_le hM hx hy hMx hMy hIa⟩
  have := hconv.sum_mem (t := Finset.univ) (w := L) (z := degenerate)
    (fun c _ => hL.1 c) hL.2 (fun c _ => ⟨degenerate_mem c, h c⟩)
  rw [sum_degenerate] at this
  exact this.2

/-- Indifference is preserved under mixing with a common third lottery. -/
theorem VNMAxioms.indiff_mix {L K L'' : C → ℝ} (hL : L ∈ S) (hK : K ∈ S) (hL'' : L'' ∈ S)
    (h : R L K ∧ R K L) {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    R (mix β L L'') (mix β K L'') ∧ R (mix β K L'') (mix β L L'') := by
  rcases hβ.1.eq_or_lt with rfl | h0
  · simp only [mix_zero]; exact ⟨hR.refl' hL'', hR.refl' hL''⟩
  rcases hβ.2.eq_or_lt with rfl | h1
  · simpa using h
  exact ⟨(hR.independence L hL K hK L'' hL'' β ⟨h0, h1⟩).1 h.1,
    (hR.independence K hK L hL L'' hL'' β ⟨h0, h1⟩).1 h.2⟩

/-- **The vN–M expected utility theorem, existence** (MWG Prop. 6.B.3, ⟹). -/
theorem exists_eu_of_vnmAxioms : ∃ u : C → ℝ, HasEURepresentation R u := by
  classical
  rcases isEmpty_or_nonempty C with hC | hC
  · -- No outcomes: there are no lotteries at all.
    refine ⟨0, fun L hL => ?_⟩
    have := hL.2
    simp at this
  -- Step 1: best and worst outcomes.
  have hdeg := fun c => degenerate_mem (C := C) c
  obtain ⟨cb, -, hcb⟩ := exists_top_of_total_finset (fun c c' => R (degenerate c) (degenerate c'))
    (fun a b => hR.complete' (hdeg a) (hdeg b))
    (fun a b c => hR.trans' (hdeg a) (hdeg b) (hdeg c)) Finset.univ Finset.univ_nonempty
  obtain ⟨cw, -, hcw⟩ := exists_top_of_total_finset (fun c c' => R (degenerate c') (degenerate c))
    (fun a b => hR.complete' (hdeg b) (hdeg a))
    (fun a b c h1 h2 => hR.trans' (hdeg c) (hdeg b) (hdeg a) h2 h1) Finset.univ
    Finset.univ_nonempty
  set b := degenerate (C := C) cb
  set w := degenerate (C := C) cw
  have hb : b ∈ S := hdeg cb
  have hw : w ∈ S := hdeg cw
  -- Step 2: every lottery lies between `w` and `b`.
  have hbest : ∀ L ∈ S, R b L := fun L hL =>
    hR.le_of_degenerate hb (fun c => hcb c (Finset.mem_univ c)) hL
  have hworst : ∀ L ∈ S, R L w := fun L hL =>
    hR.degenerate_le hw (fun c => hcw c (Finset.mem_univ c)) hL
  -- Step 3: the degenerate case of total indifference.
  by_cases hwb : R w b
  · refine ⟨0, fun L hL L' hL' => ?_⟩
    simp only [expectedUtility, Pi.zero_apply, mul_zero, Finset.sum_const_zero, le_refl,
      iff_true]
    exact hR.trans' hL hb hL' (hR.trans' hL hw hb (hworst L hL) hwb) (hbest L' hL')
  have hs : R b w ∧ ¬ R w b := ⟨hbest w hw, hwb⟩
  -- Step 4: the scale of mixtures `M α = α b + (1-α) w`.
  set M : ℝ → C → ℝ := fun α => mix α b w with hMdef
  have hMmem : ∀ α ∈ Set.Icc (0 : ℝ) 1, M α ∈ S := fun α hα => mix_mem hα hb hw
  have hbM : ∀ β ∈ Set.Icc (0 : ℝ) 1, β < 1 → R b (M β) ∧ ¬ R (M β) b := by
    intro β hβ hβ1
    rcases hβ.1.eq_or_lt with rfl | hβ0
    · simpa [hMdef] using hs
    · exact (hR.strict_mix hb hw hs ⟨hβ0, hβ1⟩).1
  have hMstrict : ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ β ∈ Set.Icc (0 : ℝ) 1, β < α →
      R (M α) (M β) ∧ ¬ R (M β) (M α) := by
    intro α hα β hβ hβα
    have hβ1 : β < 1 := hβα.trans_le hα.2
    have h1β : 0 < 1 - β := by linarith
    set γ := (α - β) / (1 - β)
    have hγ0 : 0 < γ := div_pos (by linarith) h1β
    have hγ1 : γ ≤ 1 := (div_le_one h1β).2 (by linarith [hα.2])
    -- `M α` mixes `b` with `M β` using weight `γ`.
    have hmix : M α = mix γ b (M β) := by
      funext c
      simp only [hMdef, mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, γ]
      field_simp
      ring
    rcases hγ1.eq_or_lt with hγ | hγ
    · rw [hmix, hγ, mix_one]; exact hbM β hβ hβ1
    · rw [hmix]
      exact (hR.strict_mix hb (hMmem β hβ) (hbM β hβ hβ1) ⟨hγ0, hγ⟩).2
  have hMiff : ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ β ∈ Set.Icc (0 : ℝ) 1, (R (M α) (M β) ↔ β ≤ α) := by
    intro α hα β hβ
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      exact (hMstrict β hβ α hα hlt).2 h
    · intro h
      rcases h.eq_or_lt with rfl | hlt
      · exact hR.refl' (hMmem β hβ)
      · exact (hMstrict α hα β hβ hlt).1
  -- Each lottery is indifferent to some `M α` (continuity + connectedness).
  have hex : ∀ L, ∃ α : ℝ, L ∈ S → α ∈ Set.Icc (0 : ℝ) 1 ∧ R L (M α) ∧ R (M α) L := by
    intro L
    by_cases hL : L ∈ S
    · obtain ⟨hA, hB⟩ := hR.continuity b hb w hw L hL
      have hcover : Set.Icc (0 : ℝ) 1 ⊆ {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ R (mix α b w) L} ∪
          {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ R L (mix α b w)} := by
        intro α hα
        rcases hR.complete' (hMmem α hα) hL with h | h
        · exact Or.inl ⟨hα, h⟩
        · exact Or.inr ⟨hα, h⟩
      have h1 : (Set.Icc (0 : ℝ) 1 ∩ {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ R (mix α b w) L}).Nonempty :=
        ⟨1, ⟨⟨zero_le_one, le_rfl⟩, ⟨zero_le_one, le_rfl⟩, by simpa using hbest L hL⟩⟩
      have h0 : (Set.Icc (0 : ℝ) 1 ∩ {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ R L (mix α b w)}).Nonempty :=
        ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩, by simpa using hworst L hL⟩⟩
      obtain ⟨α, hα, ⟨-, hαA⟩, ⟨-, hαB⟩⟩ :=
        isPreconnected_closed_iff.1 isPreconnected_Icc _ _ hA hB hcover h1 h0
      exact ⟨α, fun _ => ⟨hα, hαB, hαA⟩⟩
    · exact ⟨0, fun h => absurd h hL⟩
  choose U hU using hex
  -- Uniqueness of the weight.
  have hUuniq : ∀ L ∈ S, ∀ α ∈ Set.Icc (0 : ℝ) 1, R L (M α) → R (M α) L → U L = α := by
    intro L hL α hα h1 h2
    obtain ⟨hUI, hU1, hU2⟩ := hU L hL
    apply le_antisymm
    · exact (hMiff α hα _ hUI).1 (hR.trans' (hMmem α hα) hL (hMmem _ hUI) h2 hU1)
    · exact (hMiff _ hUI α hα).1 (hR.trans' (hMmem _ hUI) hL (hMmem α hα) hU2 h1)
  -- `U` represents `R`.
  have hUrep : ∀ L ∈ S, ∀ L' ∈ S, (R L L' ↔ U L' ≤ U L) := by
    intro L hL L' hL'
    obtain ⟨hUI, hU1, hU2⟩ := hU L hL
    obtain ⟨hUI', hU1', hU2'⟩ := hU L' hL'
    rw [← hMiff _ hUI _ hUI']
    constructor
    · intro h
      exact hR.trans' (hMmem _ hUI) hL (hMmem _ hUI') hU2
        (hR.trans' hL hL' (hMmem _ hUI') h hU1')
    · intro h
      exact hR.trans' hL (hMmem _ hUI) hL' hU1 (hR.trans' (hMmem _ hUI) (hMmem _ hUI') hL' h hU2')
  -- Step 5: `U` is mixture-linear.
  have hUlin : ∀ L ∈ S, ∀ L' ∈ S, ∀ β ∈ Set.Icc (0 : ℝ) 1,
      U (mix β L L') = β * U L + (1 - β) * U L' := by
    intro L hL L' hL' β hβ
    obtain ⟨hUI, hU1, hU2⟩ := hU L hL
    obtain ⟨hUI', hU1', hU2'⟩ := hU L' hL'
    have hβ' : 1 - β ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
    set K := M (U L)
    set K' := M (U L')
    have hK := hMmem _ hUI
    have hK' := hMmem _ hUI'
    -- `βL + (1-β)L' ∼ βK + (1-β)L' ∼ βK + (1-β)K'`.
    have e1 := hR.indiff_mix hL hK hL' ⟨hU1, hU2⟩ hβ
    have e2 := hR.indiff_mix hL' hK' hK ⟨hU1', hU2'⟩ hβ'
    rw [← mix_comm β K L', ← mix_comm β K K'] at e2
    have hγ := mem_Icc_mix hβ hUI hUI'
    have hKK : mix β K K' = M (β * U L + (1 - β) * U L') := by
      funext c; simp only [K, K', hMdef, mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have m1 := mix_mem hβ hL hL'
    have m2 := mix_mem hβ hK hL'
    have m3 := mix_mem hβ hK hK'
    rw [hKK] at e2 m3
    exact hUuniq _ m1 _ hγ (hR.trans' m1 m2 m3 e1.1 e2.1) (hR.trans' m3 m2 m1 e2.2 e1.2)
  -- Step 6: Jensen twice ⟹ `U L = ∑ L_c U(δ_c)`.
  have hconvex : ConvexOn ℝ S U := ⟨convex_lotteries, fun x hx y hy a b' ha hb' hab => by
    have : a • x + b' • y = mix a x y := by rw [show b' = 1 - a by linarith]; rfl
    rw [this, hUlin x hx y hy a ⟨ha, by linarith⟩, smul_eq_mul, smul_eq_mul,
      show b' = 1 - a by linarith]⟩
  have hconcave : ConcaveOn ℝ S U := ⟨convex_lotteries, fun x hx y hy a b' ha hb' hab => by
    have : a • x + b' • y = mix a x y := by rw [show b' = 1 - a by linarith]; rfl
    rw [this, hUlin x hx y hy a ⟨ha, by linarith⟩, smul_eq_mul, smul_eq_mul,
      show b' = 1 - a by linarith]⟩
  have hUsum : ∀ L ∈ S, U L = expectedUtility (fun c => U (degenerate c)) L := by
    intro L hL
    have h1 := hconvex.map_sum_le (t := Finset.univ) (w := L) (p := degenerate)
      (fun c _ => hL.1 c) hL.2 (fun c _ => hdeg c)
    have h2 := hconcave.le_map_sum (t := Finset.univ) (w := L) (p := degenerate)
      (fun c _ => hL.1 c) hL.2 (fun c _ => hdeg c)
    rw [sum_degenerate] at h1 h2
    simp only [smul_eq_mul] at h1 h2
    exact le_antisymm h1 h2
  refine ⟨fun c => U (degenerate c), fun L hL L' hL' => ?_⟩
  rw [hUrep L hL L' hL', hUsum L hL, hUsum L' hL']

end Hard

/-- **The von Neumann–Morgenstern expected utility theorem** (MWG Prop. 6.B.3).
A preference over lotteries on a finite outcome set satisfies rationality,
continuity and independence iff it has an expected utility representation. -/
theorem vnm_theorem (R : (C → ℝ) → (C → ℝ) → Prop) :
    VNMAxioms R ↔ ∃ u : C → ℝ, HasEURepresentation R u :=
  ⟨fun h => exists_eu_of_vnmAxioms h, fun ⟨_, hu⟩ => vnmAxioms_of_eu hu⟩

/-! ### Uniqueness up to positive affine transformations (MWG Prop. 6.B.2) -/

/-- A positive affine transformation of a vN–M utility represents the same
preference. -/
theorem HasEURepresentation.affine {R : (C → ℝ) → (C → ℝ) → Prop} {u : C → ℝ}
    (hu : HasEURepresentation R u) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    HasEURepresentation R (fun c => a * u c + b) := by
  intro L hL L' hL'
  rw [expectedUtility_affine hL, expectedUtility_affine hL', hu L hL L' hL', add_le_add_iff_right,
    mul_le_mul_iff_right₀ ha]

/-- **Uniqueness** (MWG Prop. 6.B.2). If `u` and `v` both represent `R`,
then `v = a u + b` with `a > 0`. (If `R` is total indifference both are
constant and `a = 1` works.) -/
theorem HasEURepresentation.unique [DecidableEq C] {R : (C → ℝ) → (C → ℝ) → Prop} {u v : C → ℝ}
    (hu : HasEURepresentation R u) (hv : HasEURepresentation R v) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ c, v c = a * u c + b := by
  rcases isEmpty_or_nonempty C with hE | hne
  · exact ⟨1, one_pos, 0, fun c => isEmptyElim c⟩
  have hC : (Finset.univ : Finset C).Nonempty := Finset.univ_nonempty
  have hdeg := fun c => degenerate_mem (C := C) c
  obtain ⟨cM, -, hcM⟩ := Finset.exists_max_image Finset.univ u hC
  obtain ⟨cm, -, hcm⟩ := Finset.exists_min_image Finset.univ u hC
  rcases lt_or_ge (u cm) (u cM) with hlt | hle
  swap
  · -- `u` is constant, so every outcome is indifferent, so `v` is constant too.
    have hconst : ∀ c, u c = u cm := fun c =>
      le_antisymm ((hcM c (Finset.mem_univ c)).trans hle) (hcm c (Finset.mem_univ c))
    have hvconst : ∀ c, v c = v cm := by
      intro c
      have h1 : R (degenerate c) (degenerate cm) := by
        rw [hu _ (hdeg c) _ (hdeg cm), expectedUtility_degenerate, expectedUtility_degenerate,
          hconst c]
      have h2 : R (degenerate cm) (degenerate c) := by
        rw [hu _ (hdeg cm) _ (hdeg c), expectedUtility_degenerate, expectedUtility_degenerate,
          hconst c]
      rw [hv _ (hdeg c) _ (hdeg cm), expectedUtility_degenerate,
        expectedUtility_degenerate] at h1
      rw [hv _ (hdeg cm) _ (hdeg c), expectedUtility_degenerate,
        expectedUtility_degenerate] at h2
      exact le_antisymm h2 h1
    exact ⟨1, one_pos, v cm - u cm, fun c => by rw [hvconst c, hconst c]; ring⟩
  have hdeg := fun c => degenerate_mem (C := C) c
  -- `v` ranks the best and worst `u`-outcomes the same way.
  have hvlt : v cm < v cM := by
    have h1 : ¬ R (degenerate cm) (degenerate cM) := by
      rw [hu _ (hdeg cm) _ (hdeg cM), expectedUtility_degenerate, expectedUtility_degenerate]
      exact not_le.2 hlt
    rw [hv _ (hdeg cm) _ (hdeg cM), expectedUtility_degenerate, expectedUtility_degenerate] at h1
    exact not_le.1 h1
  set a := (v cM - v cm) / (u cM - u cm)
  have hd : 0 < u cM - u cm := by linarith
  refine ⟨a, div_pos (by linarith) hd, v cm - a * u cm, fun c => ?_⟩
  -- `δ_c ∼ α δ_{cM} + (1-α) δ_{cm}` with `α = (u c - u cm)/(u cM - u cm)`.
  set α := (u c - u cm) / (u cM - u cm)
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hcm c (Finset.mem_univ c)]) hd.le
    · rw [div_le_one hd]; linarith [hcM c (Finset.mem_univ c)]
  have hm := mix_mem hα (hdeg cM) (hdeg cm)
  have hEUu : expectedUtility u (mix α (degenerate cM) (degenerate cm)) = u c := by
    rw [expectedUtility_mix, expectedUtility_degenerate, expectedUtility_degenerate]
    simp only [α]; field_simp; ring
  have hI1 : R (degenerate c) (mix α (degenerate cM) (degenerate cm)) := by
    rw [hu _ (hdeg c) _ hm, hEUu, expectedUtility_degenerate]
  have hI2 : R (mix α (degenerate cM) (degenerate cm)) (degenerate c) := by
    rw [hu _ hm _ (hdeg c), hEUu, expectedUtility_degenerate]
  rw [hv _ (hdeg c) _ hm, expectedUtility_degenerate, expectedUtility_mix,
    expectedUtility_degenerate, expectedUtility_degenerate] at hI1
  rw [hv _ hm _ (hdeg c), expectedUtility_degenerate, expectedUtility_mix,
    expectedUtility_degenerate, expectedUtility_degenerate] at hI2
  have hvc : v c = α * v cM + (1 - α) * v cm := le_antisymm hI2 hI1
  rw [hvc]
  simp only [α, a]
  field_simp
  ring

/-! ### Non-vacuity -/

/-- **Witness.** With two outcomes and `u = (1, 0)`, the expected-utility
preference satisfies all vN–M axioms, is not total indifference, and so its
utility is pinned down up to positive affine transformations. -/
example : VNMAxioms (fun L L' : Bool → ℝ => L' true ≤ L true) ∧
    ∃ L ∈ lotteries Bool, ∃ L' ∈ lotteries Bool,
      ¬ (fun L L' : Bool → ℝ => L' true ≤ L true) L L' := by
  have hu : HasEURepresentation (fun L L' : Bool → ℝ => L' true ≤ L true)
      (fun c => if c then 1 else 0) := by
    intro L _ L' _
    simp [expectedUtility]
  refine ⟨vnmAxioms_of_eu hu, degenerate false, degenerate_mem false, degenerate true,
    degenerate_mem true, ?_⟩
  simp [degenerate]

end Econ
