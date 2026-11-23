/-
# Monotone policies and monotone convergence

Stokey–Lucas (SL) §4.2 and §6.1; Topkis (1978); Amir (1996).

**The economics.** In many dynamic programs a higher state today leads to a
higher optimal choice for tomorrow: more capital ⇒ more saving. The
textbook route is **increasing differences** (supermodularity): if the gain
from a higher `y` is larger at a higher state `x`, then optimal choices are
monotone in `x` (Topkis' theorem). With a monotone policy `g` on an interval,
the optimal state sequence `x_{t+1} = g(x_t)` is monotone, hence converges, and
(with `g` continuous) its limit is a steady state `g(k) = k`. This is the
engine behind monotone convergence of capital in the one-sector growth model
(SL Thm 6.1 / 6.2; see `Macro/Growth/Ramsey.lean`).

**Contents.**
* `DynProg.policy_monotone`: strictly increasing differences + ascending
  feasible sets ⇒ every optimal choice at `x` is below every optimal choice at
  any `x' > x` (an order argument, no differentiability).
* `orbit_monotone_or_antitone`, `orbit_tendsto_fixedPoint`: the orbit of a
  monotone continuous self-map of a closed interval is monotone and converges
  to a fixed point.
-/
module

public import EconLean.Macro.DP.Bellman
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace Econ

open Filter Topology Set

namespace DynProg

variable {X : Type*} [TopologicalSpace X] [LinearOrder X] (P : DynProg X)

/-- **Monotone policy (Topkis).** Suppose
* feasible sets are *ascending*: if `x < x'`, `y ∈ Γ(x)`, `y' ∈ Γ(x')` and
  `y' < y`, then also `y' ∈ Γ(x)` and `y ∈ Γ(x')`;
* `F` has **strictly increasing differences**: for `x < x'` and `y' < y`
  (all four pairs feasible), `F(x', y') - F(x, y') < F(x', y) - F(x, y)`.

Then if `y` is optimal at `x` and `y'` is optimal at `x' > x`, `y ≤ y'`. -/
theorem policy_monotone
    (hΓ : ∀ x x' y y', x < x' → y ∈ P.Γ x → y' ∈ P.Γ x' → y' < y → y' ∈ P.Γ x ∧ y ∈ P.Γ x')
    (hF : ∀ x x' y y', x < x' → y' < y → y ∈ P.Γ x → y' ∈ P.Γ x → y ∈ P.Γ x' → y' ∈ P.Γ x' →
      P.F x' y' - P.F x y' < P.F x' y - P.F x y)
    {x x' y y' : X} (hx : x < x') (hy : y ∈ P.policy x) (hy' : y' ∈ P.policy x') : y ≤ y' := by
  by_contra h'
  have h := not_le.1 h'
  obtain ⟨hyΓ, hye⟩ := P.mem_policy_iff.1 hy
  obtain ⟨hy'Γ, hy'e⟩ := P.mem_policy_iff.1 hy'
  obtain ⟨h1, h2⟩ := hΓ x x' y y' hx hyΓ hy'Γ h
  -- optimality at `x` against `y'`, and at `x'` against `y`
  have o1 := P.bellman_le h1
  have o2 := P.bellman_le h2
  have := hF x x' y y' hx h hyΓ h1 h2 hy'Γ
  linarith

end DynProg

/-! ### Orbits of monotone maps on an interval -/

/-- The orbit of a monotone self-map is monotone or antitone (depending on
whether the first step goes up or down). -/
theorem orbit_monotone_or_antitone {α : Type*} [LinearOrder α] {g : α → α} (hg : Monotone g)
    (x₀ : α) : Monotone (planOf g x₀) ∨ Antitone (planOf g x₀) := by
  by_cases h : x₀ ≤ g x₀
  · left
    refine monotone_nat_of_le_succ fun n => ?_
    induction n with
    | zero => simpa [planOf] using h
    | succ n ih =>
      calc planOf g x₀ (n + 1) = g (planOf g x₀ n) := planOf_succ g x₀ n
        _ ≤ g (planOf g x₀ (n + 1)) := hg ih
        _ = planOf g x₀ (n + 1 + 1) := (planOf_succ g x₀ (n + 1)).symm
  · right
    have h' : g x₀ ≤ x₀ := le_of_not_ge h
    exact antitone_nat_of_succ_le fun n => by
      induction n with
      | zero => simpa [planOf] using h'
      | succ n ih =>
        calc planOf g x₀ (n + 1 + 1) = g (planOf g x₀ (n + 1)) := planOf_succ g x₀ (n + 1)
          _ ≤ g (planOf g x₀ n) := hg ih
          _ = planOf g x₀ (n + 1) := (planOf_succ g x₀ n).symm

/-- **Monotone convergence.** A monotone continuous self-map `g` of a closed
interval `[a, b]` has convergent orbits, and every orbit converges to a fixed
point `g k = k` (a steady state). -/
theorem orbit_tendsto_fixedPoint {a b : ℝ} {g : Icc a b → Icc a b} (hg : Monotone g)
    (hc : Continuous g) (x₀ : Icc a b) :
    ∃ k : Icc a b, g k = k ∧ Tendsto (planOf g x₀) atTop (𝓝 k) := by
  set x := planOf g x₀
  have hbdd : ∀ n, (x n : ℝ) ∈ Icc a b := fun n => (x n).2
  -- the real sequence converges, monotonically
  have hconv : ∃ L, Tendsto (fun n => (x n : ℝ)) atTop (𝓝 L) := by
    rcases orbit_monotone_or_antitone hg x₀ with hm | hm
    · exact ⟨_, tendsto_atTop_ciSup (fun m n h => hm h)
        ⟨b, by rintro _ ⟨n, rfl⟩; exact (hbdd n).2⟩⟩
    · exact ⟨_, tendsto_atTop_ciInf (fun m n h => hm h)
        ⟨a, by rintro _ ⟨n, rfl⟩; exact (hbdd n).1⟩⟩
  obtain ⟨L, hL⟩ := hconv
  have hLmem : L ∈ Icc a b := isClosed_Icc.mem_of_tendsto hL (Eventually.of_forall hbdd)
  set k : Icc a b := ⟨L, hLmem⟩
  have hk : Tendsto x atTop (𝓝 k) := by
    rw [tendsto_subtype_rng]; exact hL
  refine ⟨k, ?_, hk⟩
  -- `x (n+1) = g (x n)` tends both to `g k` and to `k`
  have h1 : Tendsto (fun n => x (n + 1)) atTop (𝓝 (g k)) := by
    have := (hc.tendsto k).comp hk
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, x, planOf_succ]
  exact tendsto_nhds_unique h1 (hk.comp (tendsto_add_atTop_nat 1))

end Econ
