/-
# Temptation and self-control (Gul–Pesendorfer 2001)

Reference. F. Gul and W. Pesendorfer (2001), "Temptation and Self-Control",
*Econometrica* 69(6).

**The model.** The agent chooses a *menu* `A` (a nonempty finite set of
alternatives) today and an item from it tomorrow. Gul and Pesendorfer show
that preferences over menus satisfying completeness/transitivity, continuity,
independence and **set betweenness**

    A ≽ B  ⟹  A ≽ A ∪ B ≽ B

are exactly those represented by

    W(A) = max_{x ∈ A} (u(x) + v(x)) − max_{y ∈ A} v(y),

where `u` is commitment utility and `v` temptation utility. Tomorrow the agent
picks `x` maximizing `u + v` (the compromise between virtue and temptation);
`max v − v(x) ≥ 0` is the self-control cost.

**Deviation.** GP's menus are compact sets of *lotteries* with linear `u`,
`v`; here menus are finite sets of deterministic alternatives, which is all
the necessity results below need.

**What is formalized.** The representation as a definition, the *necessity*
of set betweenness (`setBetweenness`), preference for commitment
(`commitment_strict`), the self-control cost bound (`W_le_max_u`), and the
fact that adding an item that is never tempting cannot hurt
(`W_union_of_not_tempting`). The *sufficiency* half of the representation
theorem (axioms ⟹ representation) needs the mixture-space machinery on
lotteries over menus and is left for later.
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

namespace Temptation

variable {X : Type*}

/-- The Gul–Pesendorfer menu utility
`W(A) = max_{x∈A} (u x + v x) − max_{y∈A} v y`. -/
def W (u v : X → ℝ) (A : Finset X) (hA : A.Nonempty) : ℝ :=
  A.sup' hA (fun x => u x + v x) - A.sup' hA v

/-- `W` of a singleton menu is commitment utility: no temptation, no cost. -/
theorem W_singleton (u v : X → ℝ) (x : X) : W u v {x} (Finset.singleton_nonempty x) = u x := by
  simp [W]

/-- Choice tomorrow maximizes `u + v`; the menu is worth at most the best
commitment utility available (self-control is costly, never beneficial). -/
theorem W_le_max_u (u v : X → ℝ) (A : Finset X) (hA : A.Nonempty) :
    W u v A hA ≤ A.sup' hA u := by
  unfold W
  rw [sub_le_iff_le_add]
  apply Finset.sup'_le
  intro x hx
  have h1 := Finset.le_sup' u hx
  have h2 := Finset.le_sup' v hx
  linarith

/-- Two-element menus: the max over `{x, y}` is the larger of the two values. -/
theorem sup'_pair [DecidableEq X] (f : X → ℝ) (x y : X) :
    ({x, y} : Finset X).sup' (Finset.insert_nonempty x {y}) f = max (f x) (f y) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' f (by simp)) (Finset.le_sup' f (by simp))

/-- **Set betweenness** (necessity half of Gul–Pesendorfer's theorem): if
`A ≽ B` then `A ≽ A ∪ B ≽ B`. -/
theorem setBetweenness [DecidableEq X] (u v : X → ℝ) {A B : Finset X} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : W u v B hB ≤ W u v A hA) :
    W u v (A ∪ B) (hA.mono Finset.subset_union_left) ≤ W u v A hA ∧
      W u v B hB ≤ W u v (A ∪ B) (hA.mono Finset.subset_union_left) := by
  unfold W at *
  rw [Finset.sup'_union hA hB, Finset.sup'_union hA hB]
  set a := A.sup' hA (fun x => u x + v x)
  set b := B.sup' hB (fun x => u x + v x)
  set α := A.sup' hA v
  set β := B.sup' hB v
  -- Four cases on which menu attains each maximum.
  rcases le_total a b with hab | hab <;> rcases le_total α β with hαβ | hαβ <;>
    simp only [sup_of_le_left, sup_of_le_right, hab, hαβ] <;> constructor <;> linarith

/-- **Preference for commitment.** If `y` tempts more than `x` (`v y > v x`)
but the agent resists it (`u x + v x ≥ u y + v y`), then the agent strictly
prefers the commitment menu `{x}` to `{x, y}`: she pays the self-control
cost `v y − v x`. -/
theorem commitment_strict [DecidableEq X] (u v : X → ℝ) {x y : X} (htempt : v x < v y)
    (hresist : u y + v y ≤ u x + v x) :
    W u v {x, y} (Finset.insert_nonempty x {y}) < W u v {x} (Finset.singleton_nonempty x) := by
  rw [W_singleton]
  simp only [W, sup'_pair]
  rw [max_eq_left hresist, max_eq_right htempt.le]
  linarith

/-- If the agent would succumb to `y` (`u y + v y > u x + v x`) and `y` is
the more tempting item, then `{x, y}` is worth exactly `u y`: she consumes
`y` without any self-control cost (the "Strotz" case). -/
theorem W_pair_succumb [DecidableEq X] (u v : X → ℝ) {x y : X} (htempt : v x ≤ v y)
    (hsuccumb : u x + v x ≤ u y + v y) :
    W u v {x, y} (Finset.insert_nonempty x {y}) = u y := by
  simp only [W, sup'_pair]
  rw [max_eq_right hsuccumb, max_eq_right htempt]
  ring

/-- Adding alternatives that are no more tempting than what the menu already
offers cannot make the agent worse off. -/
theorem W_union_of_not_tempting [DecidableEq X] (u v : X → ℝ) {A B : Finset X} (hA : A.Nonempty)
    (hB : B.Nonempty) (hv : B.sup' hB v ≤ A.sup' hA v) :
    W u v A hA ≤ W u v (A ∪ B) (hA.mono Finset.subset_union_left) := by
  unfold W
  rw [Finset.sup'_union hA hB, Finset.sup'_union hA hB, sup_of_le_left hv]
  linarith [le_max_left (A.sup' hA (fun x => u x + v x)) (B.sup' hB (fun x => u x + v x))]

end Temptation

end Econ
