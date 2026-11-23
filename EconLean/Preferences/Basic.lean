/-
# Preference relations and rationality

This file covers the opening material of almost every graduate micro course
(Mas-Colell, Whinston & Green, *Microeconomic Theory*, §1.B; Kreps, *Microeconomic
Foundations I*, ch. 2).

**The economics.** A consumer faces a set of alternatives `X`. Their tastes are
described by a binary relation `R` on `X`, read

    `R x y`   ⟺   "x is at least as good as y"      (written x ≿ y on paper).

From `R` we derive
* strict preference `P x y`  ⟺  `R x y ∧ ¬ R y x`   (x ≻ y), and
* indifference      `I x y`  ⟺  `R x y ∧ R y x`     (x ∼ y).

`R` is called **rational** when it is
* **complete**: for all x, y, `R x y ∨ R y x`, and
* **transitive**: `R x y → R y z → R x z`.

**The Lean.** We model a preference as nothing more than a relation
`R : X → X → Prop`. This is deliberate: in Lean, a "property of a relation" is a
`Prop`-valued structure, so rationality is a *structure with two proof fields*.
Every result below is the formal version of MWG Proposition 1.B.1.
-/
module

public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Tactic.Tauto

@[expose] public section

namespace Econ

-- `X` is the set (in Lean: the *type*) of alternatives. `Type*` means
-- "a type in any universe"; you can safely read it as "a set".
variable {X : Type*}

/-- Strict preference derived from a weak preference `R`: x ≻ y. -/
def P (R : X → X → Prop) (x y : X) : Prop := R x y ∧ ¬ R y x

/-- Indifference derived from a weak preference `R`: x ∼ y. -/
def I (R : X → X → Prop) (x y : X) : Prop := R x y ∧ R y x

/-- A preference relation is **rational** if it is complete and transitive.

Lean note: a `structure` whose fields are proofs is how we bundle several
axioms into one hypothesis. Given `h : Rational R`, the field `h.complete`
is a proof of completeness, `h.trans` of transitivity. -/
structure Rational (R : X → X → Prop) : Prop where
  /-- Any two alternatives can be compared. -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Consistency of rankings: x ≿ y ≿ z ⟹ x ≿ z. -/
  trans : ∀ {x y z}, R x y → R y z → R x z

namespace Rational

variable {R : X → X → Prop} (h : Rational R)
include h

/-! ### Basic consequences of rationality (MWG Prop. 1.B.1) -/

/-- Completeness already forces reflexivity: take `x = y` in `complete`.
(This is why textbooks don't list reflexivity as a separate axiom.) -/
theorem refl (x : X) : R x x := by
  -- `complete x x : R x x ∨ R x x`; both cases give what we want.
  rcases h.complete x x with hx | hx <;> exact hx

/-- Under completeness, "not y ≿ x" is the same as "x ≻ y".
This little lemma is used constantly: failure of one weak ranking
produces a strict ranking the other way. -/
theorem P_iff_not (x y : X) : P R x y ↔ ¬ R y x := by
  constructor
  · -- (→) is just the second half of the definition of `P`.
    intro hxy
    exact hxy.2
  · -- (←) by completeness, either `R x y` or `R y x`; the latter is excluded.
    intro hyx
    rcases h.complete x y with hxy | hyx'
    · exact ⟨hxy, hyx⟩
    · exact absurd hyx' hyx

end Rational

/-! Strict preference has the expected properties. Note: some of these don't
even need rationality, and Lean makes us notice exactly which hypotheses are
used. That bookkeeping is one of the real payoffs of formalization. -/

/-- ≻ is irreflexive. (No hypotheses on `R` needed at all!) -/
theorem P_irrefl (R : X → X → Prop) (x : X) : ¬ P R x x := by
  intro hx
  -- `hx : R x x ∧ ¬ R x x`, a contradiction.
  exact hx.2 hx.1

/-- ≻ is transitive, given that ≿ is transitive. (Completeness not needed.) -/
theorem P_trans {R : X → X → Prop} (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {x y z : X} (hxy : P R x y) (hyz : P R y z) : P R x z := by
  refine ⟨htrans hxy.1 hyz.1, ?_⟩
  -- Suppose `R z x`. Then z ≿ x ≿ y gives z ≿ y, contradicting y ≻ z.
  intro hzx
  exact hyz.2 (htrans hzx hxy.1)

/-- Mixed transitivity: x ≻ y ≿ z ⟹ x ≻ z. -/
theorem P_of_P_of_R {R : X → X → Prop} (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {x y z : X} (hxy : P R x y) (hyz : R y z) : P R x z := by
  refine ⟨htrans hxy.1 hyz, ?_⟩
  -- If z ≿ x, then y ≿ z ≿ x so y ≿ x, contradicting x ≻ y.
  intro hzx
  exact hxy.2 (htrans hyz hzx)

/-- Mixed transitivity: x ≿ y ≻ z ⟹ x ≻ z. -/
theorem P_of_R_of_P {R : X → X → Prop} (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {x y z : X} (hxy : R x y) (hyz : P R y z) : P R x z := by
  refine ⟨htrans hxy hyz.1, ?_⟩
  intro hzx
  exact hyz.2 (htrans hzx hxy)

namespace Rational

variable {R : X → X → Prop} (h : Rational R)
include h

/-- Indifference ∼ is an equivalence relation (reflexive, symmetric,
transitive). We package this as Mathlib's `Equivalence`, so that all of
Mathlib's machinery for equivalence relations (quotients, setoids, ...)
becomes available, e.g. for talking about *indifference classes*. -/
theorem I_equivalence : Equivalence (I R) where
  refl x := ⟨h.refl x, h.refl x⟩
  symm hxy := ⟨hxy.2, hxy.1⟩
  trans hxy hyz := ⟨h.trans hxy.1 hyz.1, h.trans hyz.2 hxy.2⟩

/-- Bridge to Mathlib: a rational preference is in particular a *preorder*
in Mathlib's unbundled sense (`IsPreorder` = reflexive + transitive).
Connecting our definitions to Mathlib's is how we get its library for free. -/
theorem isPreorder : IsPreorder X R where
  refl := h.refl
  trans _ _ _ := h.trans

/-- Exactly one of x ≻ y, x ∼ y, y ≻ x holds. Here: at least one. -/
theorem trichotomy (x y : X) : P R x y ∨ I R x y ∨ P R y x := by
  -- `by_cases` splits on whether each weak ranking holds; Lean checks we
  -- covered every case.
  by_cases hxy : R x y <;> by_cases hyx : R y x
  · exact Or.inr (Or.inl ⟨hxy, hyx⟩)
  · exact Or.inl ⟨hxy, hyx⟩
  · exact Or.inr (Or.inr ⟨hyx, hxy⟩)
  · -- Neither ranking holds: impossible by completeness.
    exact absurd (h.complete x y) (by tauto)

end Rational

end Econ
