/-
# Gorman aggregation: when does aggregate demand depend only on aggregate wealth?

PLAN.md §7.2a (bridge B0), row "Gorman polar form". MWG §4.B, Prop. 4.B.1;
Gorman (1953, 1961).

**The economics.** Macro models routinely write aggregate demand as a function
of *aggregate* wealth, as if a single consumer held it all. When is that
legitimate? Fix prices. Aggregate demand `∑ₐ xₐ(wₐ)` depends only on total
wealth `∑ₐ wₐ`, *for every distribution of wealth*, if and only if every
consumer's demand is affine in wealth with the **same slope** for everybody:

    xₐ(w) = xₐ(0) + w · β        (β common to all consumers).

This is the demand-side content of the Gorman polar form: wealth expansion
paths are parallel straight lines. It is what a representative-agent macro
model silently assumes.

Results (at fixed prices, with at least two consumers):
* `aggregatesThroughWealth_of_gorman`: common-slope affine demands aggregate
  (MWG Prop. 4.B.1, "if").
* `gorman_of_aggregatesThroughWealth`: conversely, if aggregate demand depends
  only on aggregate wealth and each demand is continuous in wealth, then all
  demands are affine in wealth with a common slope (MWG Prop. 4.B.1, "only if").

**Deviation from MWG.** MWG assumes differentiable demand and proves it by
differentiating. We assume only continuity, and the proof is a Cauchy
functional equation argument: moving `h` units of wealth from `b` to `a`
must leave the total unchanged, so `xₐ(u + h) − xₐ(u)` cannot depend on `u`,
hence is additive in `h`, hence linear by continuity. We let wealth range over
all of `ℝ` (MWG: a neighbourhood of the given distribution); this is the
version for demand functions extended to a full domain.
-/
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.Module.BigOperators

@[expose] public section

namespace Econ

open Finset

variable {α ι : Type*} [Fintype α]

/-- Aggregate demand **depends only on aggregate wealth**: there is a function
`X` with `∑ₐ xₐ(wₐ) = X(∑ₐ wₐ)` for every wealth distribution `w`. (Prices
are held fixed and suppressed.) -/
def AggregatesThroughWealth (x : α → ℝ → ι → ℝ) : Prop :=
  ∃ X : ℝ → ι → ℝ, ∀ w : α → ℝ, ∑ a, x a (w a) = X (∑ a, w a)

/-- Demands have **Gorman form**: affine in wealth with a common slope `β`. -/
def GormanForm (x : α → ℝ → ι → ℝ) : Prop :=
  ∃ β : ι → ℝ, ∀ a w, x a w = x a 0 + w • β

/-- **Gorman ⇒ aggregation** (MWG Prop. 4.B.1, "if"). -/
theorem aggregatesThroughWealth_of_gorman {x : α → ℝ → ι → ℝ} (h : GormanForm x) :
    AggregatesThroughWealth x := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨fun W => ∑ a, x a 0 + W • β, fun w => ?_⟩
  rw [Finset.sum_congr rfl (fun a _ => hβ a (w a)), Finset.sum_add_distrib, ← Finset.sum_smul]

/-- Changing one consumer's wealth changes one term of the sum. -/
theorem sum_update_apply [DecidableEq α] {V : Type*} [AddCommGroup V] (f : α → ℝ → V)
    (w : α → ℝ) (a : α) (t : ℝ) :
    ∑ c, f c (Function.update w a t c) = ∑ c, f c (w c) - f a (w a) + f a t := by
  have hupd : ∀ c, f c (Function.update w a t c) =
      Function.update (fun c => f c (w c)) a (f a t) c := fun c => by
    by_cases hc : c = a
    · subst hc; simp
    · simp [Function.update_of_ne hc]
  simp only [hupd]
  rw [Finset.sum_update_of_mem (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have : Finset.univ \ {a} = Finset.univ.erase a := by ext b; simp [and_comm]
  rw [this]
  abel

/-- **Transfer invariance.** If aggregate demand depends only on aggregate
wealth, moving `h` units of wealth from `b` to `a` leaves aggregate demand
unchanged: `xₐ(u + h) + x_b(v − h) = xₐ(u) + x_b(v)`. -/
theorem AggregatesThroughWealth.transfer [DecidableEq α] {x : α → ℝ → ι → ℝ}
    (hagg : AggregatesThroughWealth x) {a b : α} (hab : a ≠ b) (u v h : ℝ) :
    x a (u + h) + x b (v - h) = x a u + x b v := by
  obtain ⟨X, hX⟩ := hagg
  set w₀ : α → ℝ := Function.update (Function.update 0 a u) b v
  set w₁ : α → ℝ := Function.update (Function.update w₀ a (u + h)) b (v - h)
  have hw₀a : w₀ a = u := by simp [w₀, Function.update_of_ne hab]
  have hw₀b : w₀ b = v := by simp [w₀]
  have hmid : Function.update w₀ a (u + h) b = v := by
    rw [Function.update_of_ne hab.symm]; exact hw₀b
  -- Same total wealth.
  have htot : ∑ c, w₁ c = ∑ c, w₀ c := by
    have h1 := sum_update_apply (fun _ (t : ℝ) => t) (Function.update w₀ a (u + h)) b (v - h)
    have h2 := sum_update_apply (fun _ (t : ℝ) => t) w₀ a (u + h)
    rw [h1, h2, hmid, hw₀a]
    ring
  -- Expand both aggregate demands.
  have hd := congrArg X htot
  rw [← hX, ← hX] at hd
  have e1 := sum_update_apply x (Function.update w₀ a (u + h)) b (v - h)
  have e2 := sum_update_apply x w₀ a (u + h)
  rw [e1, e2, hmid, hw₀a] at hd
  -- `hd : S - x a u + x a (u+h) - x b v + x b (v-h) = S`, where `S` is the base sum.
  rw [← sub_eq_zero] at hd ⊢
  rw [← hd]
  abel

/-- **Pairwise Gorman lemma.** For two distinct consumers, aggregation through
wealth plus continuity forces both demands to be affine in wealth with the
same slope. -/
theorem AggregatesThroughWealth.pair [DecidableEq α] {x : α → ℝ → ι → ℝ}
    (hagg : AggregatesThroughWealth x) (hc : ∀ a, Continuous (x a)) {a b : α}
    (hab : a ≠ b) :
    ∃ γ : ι → ℝ, ∀ u, x a u = x a 0 + u • γ ∧ x b u = x b 0 + u • γ := by
  -- With `v = h`: `xₐ(u + h) − xₐ(u) = x_b(h) − x_b(0) =: g(h)`.
  set g : ℝ → ι → ℝ := fun h => x b h - x b 0 with hg
  have hshift : ∀ u h, x a (u + h) = x a u + g h := by
    intro u h
    have := hagg.transfer hab u h h
    rw [sub_self] at this
    simp only [hg]
    rw [← sub_eq_zero] at this ⊢
    rw [← this]
    abel
  -- `g` is additive ...
  have hadd : ∀ h₁ h₂, g (h₁ + h₂) = g h₁ + g h₂ := by
    intro h₁ h₂
    have e1 := hshift 0 (h₁ + h₂)
    have e2 := hshift h₁ h₂
    have e3 := hshift 0 h₁
    simp only [zero_add] at e1 e3
    rw [e2, e3] at e1
    have : x a 0 + g h₁ + g h₂ = x a 0 + g (h₁ + h₂) := e1
    rw [add_assoc] at this
    exact (add_left_cancel this).symm
  -- ... and continuous, hence linear: `g h = h • g 1`.
  have hgc : Continuous g := (hc b).sub continuous_const
  let G : ℝ →+ (ι → ℝ) :=
    { toFun := g
      map_zero' := by simp [hg]
      map_add' := hadd }
  have hlin : ∀ h, g h = h • g 1 := fun h => by
    have := map_real_smul G hgc h 1
    simpa [G] using this
  refine ⟨g 1, fun u => ⟨?_, ?_⟩⟩
  · have := hshift 0 u
    rw [zero_add] at this
    rw [this, hlin u]
  · have : x b u = x b 0 + g u := by simp [hg]
    rw [this, hlin u]

/-- **Gorman's aggregation theorem** (MWG Prop. 4.B.1, "only if"; continuity
instead of differentiability). With at least two consumers, if aggregate
demand depends only on aggregate wealth and each consumer's demand is
continuous in wealth, then demands have Gorman form: affine in wealth with a
slope common to all consumers. -/
theorem gorman_of_aggregatesThroughWealth [Nontrivial α] {x : α → ℝ → ι → ℝ}
    (hagg : AggregatesThroughWealth x) (hc : ∀ a, Continuous (x a)) : GormanForm x := by
  classical
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  -- The common slope, read off consumer `a₀`.
  refine ⟨x a₀ 1 - x a₀ 0, fun a u => ?_⟩
  -- Any pair containing `a₀` has a common slope, which must be `x a₀ 1 - x a₀ 0`.
  have hslope : ∀ b, b ≠ a₀ → ∃ γ : ι → ℝ, γ = x a₀ 1 - x a₀ 0 ∧
      ∀ u, x a₀ u = x a₀ 0 + u • γ ∧ x b u = x b 0 + u • γ := by
    intro b hb
    obtain ⟨γ, hγ⟩ := hagg.pair hc (Ne.symm hb)
    refine ⟨γ, ?_, hγ⟩
    have := (hγ 1).1
    rw [one_smul] at this
    rw [this]; abel
  by_cases ha : a = a₀
  · subst ha
    obtain ⟨b, hb⟩ := exists_ne a
    obtain ⟨γ, hγeq, hγ⟩ := hslope b hb
    rw [← hγeq]; exact (hγ u).1
  · obtain ⟨γ, hγeq, hγ⟩ := hslope a ha
    rw [← hγeq]; exact (hγ u).2

/-! ### Nonnegative wealth: the economically relevant domain

Demand is only defined for `w ≥ 0` (the budget set is empty otherwise), so the
faithful version of MWG Prop. 4.B.1 quantifies over nonnegative wealth
distributions only. The proof is the same Cauchy argument on the half-line
`[0, ∞)`, extended to an additive map on `ℝ` by `G(h) = g(h⁺) − g(h⁻)`. -/

/-- Aggregate demand depends only on aggregate wealth, for every **nonnegative**
wealth distribution. -/
def AggregatesThroughWealthNonneg (x : α → ℝ → ι → ℝ) : Prop :=
  ∃ X : ℝ → ι → ℝ, ∀ w : α → ℝ, (∀ a, 0 ≤ w a) → ∑ a, x a (w a) = X (∑ a, w a)

/-- Transfer invariance on nonnegative wealth. -/
theorem AggregatesThroughWealthNonneg.transfer [DecidableEq α] {x : α → ℝ → ι → ℝ}
    (hagg : AggregatesThroughWealthNonneg x) {a b : α} (hab : a ≠ b) {u v h : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huh : 0 ≤ u + h) (hvh : 0 ≤ v - h) :
    x a (u + h) + x b (v - h) = x a u + x b v := by
  obtain ⟨X, hX⟩ := hagg
  set w₀ : α → ℝ := Function.update (Function.update 0 a u) b v
  set w₁ : α → ℝ := Function.update (Function.update w₀ a (u + h)) b (v - h)
  have hw₀a : w₀ a = u := by simp [w₀, Function.update_of_ne hab]
  have hw₀b : w₀ b = v := by simp [w₀]
  have hmid : Function.update w₀ a (u + h) b = v := by
    rw [Function.update_of_ne hab.symm]; exact hw₀b
  have hw₀ : ∀ c, 0 ≤ w₀ c := by
    intro c
    by_cases hcb : c = b
    · subst hcb; rw [hw₀b]; exact hv
    · by_cases hca : c = a
      · subst hca; rw [hw₀a]; exact hu
      · simp [w₀, Function.update_of_ne hcb, Function.update_of_ne hca]
  have hw₁ : ∀ c, 0 ≤ w₁ c := by
    intro c
    by_cases hcb : c = b
    · subst hcb; simp [w₁]; linarith
    · by_cases hca : c = a
      · subst hca; simp [w₁, Function.update_of_ne hcb]; linarith
      · simp only [w₁, Function.update_of_ne hcb, Function.update_of_ne hca]; exact hw₀ c
  have htot : ∑ c, w₁ c = ∑ c, w₀ c := by
    have h1 := sum_update_apply (fun _ (t : ℝ) => t) (Function.update w₀ a (u + h)) b (v - h)
    have h2 := sum_update_apply (fun _ (t : ℝ) => t) w₀ a (u + h)
    rw [h1, h2, hmid, hw₀a]
    ring
  have hd := congrArg X htot
  rw [← hX _ hw₁, ← hX _ hw₀] at hd
  have e1 := sum_update_apply x (Function.update w₀ a (u + h)) b (v - h)
  have e2 := sum_update_apply x w₀ a (u + h)
  rw [e1, e2, hmid, hw₀a] at hd
  rw [← sub_eq_zero] at hd ⊢
  rw [← hd]
  abel

/-- **Pairwise Gorman lemma on nonnegative wealth.** -/
theorem AggregatesThroughWealthNonneg.pair [DecidableEq α] {x : α → ℝ → ι → ℝ}
    (hagg : AggregatesThroughWealthNonneg x)
    (hc : ∀ a, ContinuousOn (x a) (Set.Ici 0)) {a b : α} (hab : a ≠ b) :
    ∃ γ : ι → ℝ, ∀ u, 0 ≤ u → x a u = x a 0 + u • γ ∧ x b u = x b 0 + u • γ := by
  -- `g(h) = x_b(h) − x_b(0)`; then `xₐ(u + h) = xₐ(u) + g(h)` for `u, h ≥ 0`.
  set g : ℝ → ι → ℝ := fun h => x b h - x b 0 with hg
  have hshift : ∀ u h, 0 ≤ u → 0 ≤ h → x a (u + h) = x a u + g h := by
    intro u h hu hh
    have := hagg.transfer hab hu hh (by linarith) (by simp)
    rw [sub_self] at this
    simp only [hg]
    rw [← sub_eq_zero] at this ⊢
    rw [← this]
    abel
  have hadd : ∀ h₁ h₂, 0 ≤ h₁ → 0 ≤ h₂ → g (h₁ + h₂) = g h₁ + g h₂ := by
    intro h₁ h₂ h₁0 h₂0
    have e1 := hshift 0 (h₁ + h₂) le_rfl (add_nonneg h₁0 h₂0)
    have e2 := hshift h₁ h₂ h₁0 h₂0
    have e3 := hshift 0 h₁ le_rfl h₁0
    simp only [zero_add] at e1 e3
    rw [e2, e3] at e1
    rw [add_assoc] at e1
    exact (add_left_cancel e1).symm
  -- Extend to `ℝ`: `G(h) = g(h⁺) − g(h⁻)`.
  set G : ℝ → ι → ℝ := fun h => g (max h 0) - g (max (-h) 0) with hG
  have hg0 : g 0 = 0 := by simp [hg]
  have hGadd : ∀ h₁ h₂, G (h₁ + h₂) = G h₁ + G h₂ := by
    intro h₁ h₂
    -- `(h₁+h₂)⁺ + h₁⁻ + h₂⁻ = (h₁+h₂)⁻ + h₁⁺ + h₂⁺`, all terms nonnegative.
    have key : max (h₁ + h₂) 0 + (max (-h₁) 0 + max (-h₂) 0)
        = max (-(h₁ + h₂)) 0 + (max h₁ 0 + max h₂ 0) := by
      have e := max_zero_sub_max_neg_zero_eq_self (h₁ + h₂)
      have e1 := max_zero_sub_max_neg_zero_eq_self h₁
      have e2 := max_zero_sub_max_neg_zero_eq_self h₂
      linarith
    have hk := congrArg g key
    have n := fun t : ℝ => le_max_right t 0
    rw [hadd _ _ (n _) (add_nonneg (n _) (n _)), hadd _ _ (n _) (n _),
      hadd _ _ (n _) (add_nonneg (n _) (n _)), hadd _ _ (n _) (n _)] at hk
    simp only [hG]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hk
    rw [← hk]
    abel
  have hgc : ContinuousOn g (Set.Ici 0) := (hc b).sub continuousOn_const
  have hGc : Continuous G := by
    have hpos : Continuous fun h : ℝ => g (max h 0) :=
      hgc.comp_continuous (continuous_id.max continuous_const) fun h => le_max_right h 0
    have hneg : Continuous fun h : ℝ => g (max (-h) 0) :=
      hgc.comp_continuous (continuous_neg.max continuous_const) fun h => le_max_right _ 0
    exact hpos.sub hneg
  let Gh : ℝ →+ (ι → ℝ) :=
    { toFun := G
      map_zero' := by simp [hG, hg0]
      map_add' := hGadd }
  have hlin : ∀ h, 0 ≤ h → g h = h • g 1 := fun h hh => by
    have := map_real_smul Gh hGc h 1
    have hG1 : G 1 = g 1 := by simp [hG, hg0]
    have hGh : G h = g h := by
      simp only [hG, max_eq_left hh, max_eq_right (neg_nonpos.2 hh), hg0, sub_zero]
    simp only [Gh, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul, mul_one] at this
    rw [← hGh, ← hG1]
    simpa using this
  refine ⟨g 1, fun u hu => ⟨?_, ?_⟩⟩
  · have := hshift 0 u le_rfl hu
    rw [zero_add] at this
    rw [this, hlin u hu]
  · have : x b u = x b 0 + g u := by simp [hg]
    rw [this, hlin u hu]

/-- **Gorman's aggregation theorem on nonnegative wealth** (MWG Prop. 4.B.1,
"only if"; continuity instead of differentiability). With at least two
consumers, if aggregate demand depends only on aggregate wealth for every
nonnegative wealth distribution and each demand is continuous in wealth on
`[0, ∞)`, then demands are affine in wealth on `[0, ∞)` with a common slope. -/
theorem gorman_of_aggregatesThroughWealthNonneg [Nontrivial α] {x : α → ℝ → ι → ℝ}
    (hagg : AggregatesThroughWealthNonneg x) (hc : ∀ a, ContinuousOn (x a) (Set.Ici 0)) :
    ∃ β : ι → ℝ, ∀ a, ∀ w, 0 ≤ w → x a w = x a 0 + w • β := by
  classical
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  refine ⟨x a₀ 1 - x a₀ 0, fun a u hu => ?_⟩
  have hslope : ∀ b, b ≠ a₀ → ∃ γ : ι → ℝ, γ = x a₀ 1 - x a₀ 0 ∧
      ∀ u, 0 ≤ u → x a₀ u = x a₀ 0 + u • γ ∧ x b u = x b 0 + u • γ := by
    intro b hb
    obtain ⟨γ, hγ⟩ := hagg.pair hc (Ne.symm hb)
    refine ⟨γ, ?_, hγ⟩
    have := (hγ 1 zero_le_one).1
    rw [one_smul] at this
    rw [this]; abel
  by_cases ha : a = a₀
  · subst ha
    obtain ⟨b, hb⟩ := exists_ne a
    obtain ⟨γ, hγeq, hγ⟩ := hslope b hb
    rw [← hγeq]; exact (hγ u hu).1
  · obtain ⟨γ, hγeq, hγ⟩ := hslope a ha
    rw [← hγeq]; exact (hγ u hu).2

end Econ
