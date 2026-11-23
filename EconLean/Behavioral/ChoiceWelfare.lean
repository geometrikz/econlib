/-
# Choice-based welfare (Bernheim–Rangel 2009)

Reference. B. D. Bernheim and A. Rangel (2009), "Beyond Revealed Preference:
Choice-Theoretic Foundations for Behavioral Welfare Economics", *QJE*
124(1), §§III–IV.

A **generalized choice situation** `g` consists of a menu `menu g` and an
ancillary condition (a frame) that does not affect the feasible set but may
affect choice; the frames are the elements of the index type `G` itself. The
choice correspondence `C g ⊆ menu g` is nonempty on every situation.

The **unambiguous choice relation** `P*`: `x P* y` iff `x ≠ y` and `y` is
never chosen when `x` is available, in any situation.

**Results.** Assume the domain is rich: every nonempty finite menu appears in
some situation (`Rich`).
* `exists_weak_optimum` (BR Theorem 3): every nonempty menu contains a
  **weak welfare optimum**, an element not `P*`-dominated within the menu;
  hence `P*` has no cycles (`pstar_acyclic`, BR Theorem 1) and is asymmetric.
* `chosen_isWeakOptimum`: every choice, in any frame, is a weak welfare
  optimum: welfare analysis never overturns a choice.
* `pstar_iff_of_utility`: if choice is frame-independent and picks the
  maximizers of a utility `u`, then `x P* y ↔ u y < u x`: the framework
  coincides with standard revealed-preference welfare.
* `frame_ambiguity`: if a frame switches the choice between `a` and `b`,
  neither is unambiguously preferred: `P*` is incomplete exactly where
  choices conflict.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace Econ

namespace ChoiceWelfare

variable {X G : Type*} [DecidableEq X]

/-- A behavioral choice correspondence over generalized choice situations. -/
structure Data (X G : Type*) where
  menu : G → Finset X
  C : G → Set X
  sub : ∀ g, C g ⊆ menu g
  nonempty : ∀ g, (menu g).Nonempty → (C g).Nonempty

namespace Data

variable (D : Data X G)

/-- Bernheim–Rangel's unambiguous choice relation `P*`. -/
def Pstar (x y : X) : Prop := x ≠ y ∧ ∀ g, x ∈ D.menu g → y ∈ D.menu g → y ∉ D.C g

/-- Every nonempty finite menu is observed in some situation. -/
def Rich : Prop := ∀ S : Finset X, S.Nonempty → ∃ g, D.menu g = S

/-- A weak welfare optimum in `S`: no element of `S` is unambiguously better. -/
def IsWeakOptimum (S : Finset X) (x : X) : Prop := x ∈ S ∧ ∀ y ∈ S, ¬ D.Pstar y x

omit [DecidableEq X] in
/-- Every choice is a weak welfare optimum of its menu. -/
theorem chosen_isWeakOptimum {g : G} {x : X} (hx : x ∈ D.C g) :
    D.IsWeakOptimum (D.menu g) x :=
  ⟨D.sub g hx, fun _ hy h => h.2 g hy (D.sub g hx) hx⟩

omit [DecidableEq X] in
/-- **Weak welfare optima exist** in every nonempty menu (rich domain). -/
theorem exists_weak_optimum (hR : D.Rich) {S : Finset X} (hS : S.Nonempty) :
    ∃ x, D.IsWeakOptimum S x := by
  obtain ⟨g, hg⟩ := hR S hS
  obtain ⟨x, hx⟩ := D.nonempty g (hg ▸ hS)
  exact ⟨x, hg ▸ D.chosen_isWeakOptimum hx⟩

/-- **`P*` is acyclic** (rich domain): there is no list `x₀ P* x₁ P* ⋯ P* xₙ P* x₀`. -/
theorem pstar_acyclic (hR : D.Rich) (l : List X) (hl : l ≠ [])
    (hcyc : ∀ y ∈ l, ∃ z ∈ l, D.Pstar z y) : False := by
  obtain ⟨x, hxS, hx⟩ := D.exists_weak_optimum hR (S := l.toFinset)
    (List.toFinset_nonempty_iff l |>.2 hl)
  obtain ⟨z, hz, hzx⟩ := hcyc x (List.mem_toFinset.1 hxS)
  exact hx z (List.mem_toFinset.2 hz) hzx

/-- `P*` is asymmetric (rich domain). -/
theorem pstar_asymm (hR : D.Rich) {x y : X} (h : D.Pstar x y) : ¬ D.Pstar y x := fun h' =>
  D.pstar_acyclic hR [x, y] (by simp) fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨y, by simp, h'⟩
    · exact ⟨x, by simp, h⟩

/-- **Coincidence with standard welfare.** If choice ignores frames and picks
the `u`-maximizers of the menu, then `x P* y ↔ u y < u x` (ties are never
unambiguously ranked). -/
theorem pstar_iff_of_utility (hR : D.Rich) {u : X → ℝ}
    (hC : ∀ g, D.C g = {x | x ∈ D.menu g ∧ ∀ y ∈ D.menu g, u y ≤ u x}) (x y : X) :
    D.Pstar x y ↔ u y < u x := by
  constructor
  · rintro ⟨hne, h⟩
    obtain ⟨g, hg⟩ := hR {x, y} (by simp)
    have hx : x ∈ D.menu g := by simp [hg]
    have hy : y ∈ D.menu g := by simp [hg]
    have := h g hx hy
    rw [hC g] at this
    simp only [Set.mem_ofPred_eq, not_and, not_forall, not_le, exists_prop] at this
    obtain ⟨z, hz, hzy⟩ := this hy
    rw [hg] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hzy
    · exact absurd hzy (lt_irrefl _)
  · intro h
    refine ⟨fun hxy => by subst hxy; exact lt_irrefl _ h, fun g hx _ hyC => ?_⟩
    rw [hC g] at hyC
    exact absurd (hyC.2 x hx) (not_le.2 h)

omit [DecidableEq X] in
/-- **Frames create ambiguity.** If `a` is chosen over `b` in one situation and
`b` over `a` in another, neither is unambiguously preferred. -/
theorem frame_ambiguity {a b : X} {g₁ g₂ : G} (ha : a ∈ D.C g₁) (hb₁ : b ∈ D.menu g₁)
    (hb : b ∈ D.C g₂) (ha₂ : a ∈ D.menu g₂) : ¬ D.Pstar a b ∧ ¬ D.Pstar b a :=
  ⟨fun h => h.2 g₂ ha₂ (D.sub g₂ hb) hb, fun h => h.2 g₁ hb₁ (D.sub g₁ ha) ha⟩

end Data

end ChoiceWelfare

end Econ
