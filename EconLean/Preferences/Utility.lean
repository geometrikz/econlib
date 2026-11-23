/-
# Utility representations

MWG §1.B (Def. 1.B.2, Prop. 1.B.2) and §3.C; Kreps ch. 2.

**The economics.** A function `u : X → ℝ` *represents* the preference `R` if

    R x y   ⟺   u x ≥ u y        for all x, y.

Three classic facts, all proved below:
1. Only rational preferences can be represented by a utility function.
2. Utility is *ordinal*: composing a representation with any strictly
   increasing `f : ℝ → ℝ` gives another representation.
3. On a **finite** set of alternatives, every rational preference has a
   utility representation. (Construction: `u x` = number of alternatives
   that `x` is at least as good as.)

The famous extension, Debreu's theorem (continuous rational preferences on
ℝⁿ have a *continuous* utility representation), is on the roadmap; the
countable case is the natural next step after the finite one.
-/
import EconLean.Preferences.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card

namespace Econ

variable {X : Type*}

/-- `u` represents `R`: x ≿ y exactly when u x ≥ u y. -/
def Represents (u : X → ℝ) (R : X → X → Prop) : Prop :=
  ∀ x y, R x y ↔ u y ≤ u x

namespace Represents

variable {u : X → ℝ} {R : X → X → Prop}

/-- **Fact 1 (MWG Prop. 1.B.2).** A preference represented by a utility
function is rational. Intuition: `≤` on ℝ is complete and transitive, and
`u` pulls those properties back to `X`. -/
theorem rational (hu : Represents u R) : Rational R where
  complete x y := by
    -- On ℝ, either `u y ≤ u x` or `u x ≤ u y` (`le_total`).
    rcases le_total (u y) (u x) with h | h
    · exact Or.inl ((hu x y).2 h)
    · exact Or.inr ((hu y x).2 h)
  trans {x y z} hxy hyz := by
    -- Translate into ℝ, use transitivity of ≤ there, translate back.
    rw [hu] at hxy hyz ⊢
    exact le_trans hyz hxy

/-- Under a representation, strict preference is strict inequality. -/
theorem P_iff (hu : Represents u R) (x y : X) : P R x y ↔ u y < u x := by
  -- `P R x y` unfolds to `R x y ∧ ¬ R y x`, i.e. `u y ≤ u x ∧ ¬ u x ≤ u y`.
  simp only [P, hu x y, hu y x, not_le]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.le, h⟩

/-- **Fact 2: utility is ordinal.** If `u` represents `R` and `f` is strictly
increasing, then `f ∘ u` also represents `R`. So the *numbers* carry no
meaning beyond their ranking: "utils" are not measurable quantities. -/
theorem comp_strictMono (hu : Represents u R) {f : ℝ → ℝ} (hf : StrictMono f) :
    Represents (f ∘ u) R := by
  intro x y
  -- `StrictMono.le_iff_le : f a ≤ f b ↔ a ≤ b` does all the work.
  rw [Function.comp_apply, Function.comp_apply, hf.le_iff_le]
  exact hu x y

end Represents

/-- Any function `u : X → ℝ` *induces* a preference: x ≿ y iff u x ≥ u y.
It is represented by `u` by construction (proof: `Iff.rfl`, i.e. "true by
definition"). -/
def prefOf (u : X → ℝ) : X → X → Prop := fun x y => u y ≤ u x

theorem represents_prefOf (u : X → ℝ) : Represents u (prefOf u) :=
  fun _ _ => Iff.rfl

/-! ### Fact 3: existence of a utility function on a finite set

Construction: for each `x`, let `L x` be its *lower contour set*
`{y | x ≿ y}`, and set `u x := |L x|`, the number of alternatives `x` beats
or ties.

* If x ≿ y, then everything below `y` is below `x` (transitivity), so
  `L y ⊆ L x` and `u y ≤ u x`.
* If not x ≿ y, then y ≻ x (completeness), so `L x ⊊ L y`: `L x ⊆ L y`
  as before, and `y ∈ L y` (reflexivity) but `y ∉ L x`. Hence `u x < u y`.
-/

section Finite

-- `Fintype X`: X is finite and we can enumerate it (`Finset.univ`).
variable [Fintype X] {R : X → X → Prop}

open Classical in
/-- The lower contour set `{y | x ≿ y}`, as a finite set. (`open Classical`
lets us filter by a predicate without proving it is decidable.) -/
noncomputable def lowerContour (R : X → X → Prop) (x : X) : Finset X :=
  Finset.univ.filter (fun y => R x y)

theorem mem_lowerContour {x y : X} : y ∈ lowerContour R x ↔ R x y := by
  classical
  simp [lowerContour]

/-- The counting utility function. -/
noncomputable def countingUtility (R : X → X → Prop) (x : X) : ℝ :=
  ((lowerContour R x).card : ℝ)

/-- If x ≿ y then `L y ⊆ L x`. -/
theorem lowerContour_subset (h : Rational R) {x y : X} (hxy : R x y) :
    lowerContour R y ⊆ lowerContour R x := by
  intro z hz
  rw [mem_lowerContour] at hz ⊢
  exact h.trans hxy hz

/-- **Fact 3 (MWG Prop. 3.C.1, finite case).** Every rational preference on
a finite set has a utility representation. -/
theorem exists_utility_of_finite (h : Rational R) :
    ∃ u : X → ℝ, Represents u R := by
  refine ⟨countingUtility R, fun x y => ⟨fun hxy => ?_, fun hle => ?_⟩⟩
  · -- (→) x ≿ y ⟹ |L y| ≤ |L x|.
    unfold countingUtility
    exact_mod_cast Finset.card_le_card (lowerContour_subset h hxy)
  · -- (←) by contradiction: if ¬ x ≿ y then |L x| < |L y|.
    by_contra hxy
    have hyx : R y x := (h.complete x y).resolve_left hxy
    have hss : lowerContour R x ⊂ lowerContour R y := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨lowerContour_subset h hyx, ?_⟩
      intro heq
      -- `y ∈ L y` by reflexivity, so `y ∈ L x`, i.e. x ≿ y. Contradiction.
      have : y ∈ lowerContour R x := heq ▸ mem_lowerContour.2 (h.refl y)
      exact hxy (mem_lowerContour.1 this)
    have hlt := Finset.card_lt_card hss
    unfold countingUtility at hle
    have : ((lowerContour R y).card : ℝ) ≤ (lowerContour R x).card := hle
    exact absurd (by exact_mod_cast this) (not_le.2 hlt)

/-- Putting Facts 1 and 3 together: on a finite set, a preference is rational
**if and only if** it can be represented by a utility function. -/
theorem rational_iff_exists_utility :
    Rational R ↔ ∃ u : X → ℝ, Represents u R :=
  ⟨exists_utility_of_finite, fun ⟨_, hu⟩ => hu.rational⟩

end Finite

end Econ
