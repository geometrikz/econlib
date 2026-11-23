/-
# Stochastic DP: concave value function and a continuous policy function

Stokey–Lucas (SL) Thms 9.8–9.9 (concavity of `V(·, z)`, single-valued
continuous policy), in a variant that suits savings problems.

**Setup.** The endogenous state lives in a convex set `S` of a real normed
space, and there are finitely many shocks.

**Hypotheses** (for every shock `z`):
* *convex technology*: the graph of `Γ(·, z)` is convex;
* *concave return, strictly concave in the choice*: `F((x, z), y)` is
  jointly concave on the graph. It is strictly concave in `y` when the current
  state `x` is the same.

**Deviation from SL.** SL Assumption 9.7 asks for strict concavity whenever
the current *states* differ. That fails in the income fluctuation problem: there
`F = u(R a + y - a')` is constant along directions that keep cash-on-hand minus
savings fixed. Our hypothesis (strict in the choice, weak jointly) holds there,
and it is all that uniqueness of the optimal choice needs. In exchange we get
only weak concavity of `V(·, z)`.

**Results.** `V(·, z)` is concave for every `z` (`value_concave`). The optimal
choice is unique at every state, so the policy is a continuous function `g`
(`exists_continuous_policy`).
-/
module

public import EconLean.Macro.DP.StochasticPlan
public import EconLean.Macro.DP.Concavity

@[expose] public section

namespace Econ

open BoundedContinuousFunction Filter Topology Set Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- A return that is concave on the graph of `Γ` and strictly concave in the
choice at a fixed state. This **deviates from SL Assumption 9.7** (strict
concavity whenever the states differ); neither implies the other. It suits
savings problems, where 9.7 fails, and it gives a unique continuous policy.
The cost is that `V(·, z)` is only shown weakly concave. -/
def ConcaveReturnStrictInChoice (Γ : S → Set S) (F : S → S → ℝ) : Prop :=
  ∀ x y x' y' z w : S, y ∈ Γ x → y' ∈ Γ x' → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
    (z : E) = a • (x : E) + b • (x' : E) → (w : E) = a • (y : E) + b • (y' : E) →
    a * F x y + b * F x' y' ≤ F z w ∧ (x = x' → y ≠ y' → a * F x y + b * F x' y' < F z w)

namespace StochDynProg

variable {Z : Type*} [TopologicalSpace Z] [DiscreteTopology Z] [Fintype Z]
  (hS : Convex ℝ S) (P : StochDynProg S Z)

/-- Convex technology, shock by shock. -/
def ConvexTech : Prop := ∀ z, ConvexGraph fun x : S => P.Γ (x, z)

/-- Concave return, strictly concave in the choice, shock by shock. -/
def ConcaveRet : Prop :=
  ∀ z, ConcaveReturnStrictInChoice (fun x : S => P.Γ (x, z)) fun x y => P.F (x, z) y

/-- Expected continuation values of a function concave in the state are concave. -/
theorem concave_expect {f : S × Z →ᵇ ℝ} (hf : ∀ z, ConcaveFn fun x : S => f (x, z)) (z : Z) :
    ConcaveFn fun y : S => ∑ z', P.Q z z' * f (y, z') := by
  intro x x' w a b ha hb hab hw
  have e : a * ∑ z', P.Q z z' * f (x, z') + b * ∑ z', P.Q z z' * f (x', z') =
      ∑ z', P.Q z z' * (a * f (x, z') + b * f (x', z')) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  exact Finset.sum_le_sum fun z' _ =>
    mul_le_mul_of_nonneg_left (hf z' x x' w a b ha hb hab hw) (P.Q_nonneg _ _)

include hS in
/-- The Bellman operator preserves concavity in the state. -/
theorem concave_bellmanOp (hΓ : P.ConvexTech) (hF : P.ConcaveRet) {f : S × Z →ᵇ ℝ}
    (hf : ∀ z, ConcaveFn fun x : S => f (x, z)) (z : Z) :
    ConcaveFn fun x : S => P.bellmanOp f (x, z) := by
  intro x x' w a b ha hb hab hw
  obtain ⟨y, hy, he⟩ := (P.isGreatest_bellmanOp f (x, z)).1
  obtain ⟨y', hy', he'⟩ := (P.isGreatest_bellmanOp f (x', z)).1
  set v : S := ⟨a • (y : E) + b • (y' : E), hS y.2 y'.2 ha.le hb.le hab⟩
  have hv : v ∈ P.Γ (w, z) := hΓ z x y x' y' w v hy hy' a b ha hb hab hw rfl
  have hTw := (P.isGreatest_bellmanOp f (w, z)).2 ⟨v, hv, rfl⟩
  have hfv := P.concave_expect hf z y y' v a b ha hb hab rfl
  have hF1 := (hF z x y x' y' w v hy hy' a b ha hb hab hw rfl).1
  simp only at he he' hTw hF1 hfv ⊢
  rw [← he, ← he']
  have hβ := P.β_pos
  have key : a * (P.F (x, z) y + P.β * ∑ z', P.Q z z' * f (y, z')) +
      b * (P.F (x', z) y' + P.β * ∑ z', P.Q z z' * f (y', z')) =
      (a * P.F (x, z) y + b * P.F (x', z) y') +
        P.β * (a * ∑ z', P.Q z z' * f (y, z') + b * ∑ z', P.Q z z' * f (y', z')) := by ring
  rw [key]
  nlinarith

include hS in
/-- **SL Thm 9.8** (variant): `V(·, z)` is concave for every shock `z`. -/
theorem value_concave (hΓ : P.ConvexTech) (hF : P.ConcaveRet) (z : Z) :
    ConcaveFn fun x : S => P.value (x, z) := by
  have hiter : ∀ n z, ConcaveFn fun x : S => (P.bellmanOp^[n] 0) (x, z) := by
    intro n
    induction n with
    | zero => intro z x x' w a b _ _ _ _; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply']
      exact P.concave_bellmanOp hS hΓ hF ih z
  intro x x' w a b ha hb hab hw
  have hlim := (P.iterate_converges 0).1
  have hcont : Continuous fun f : S × Z →ᵇ ℝ => f (w, z) - (a * f (x, z) + b * f (x', z)) :=
    (lipschitz_eval_const (w, z)).continuous.sub
      ((continuous_const.mul (lipschitz_eval_const (x, z)).continuous).add
        (continuous_const.mul (lipschitz_eval_const (x', z)).continuous))
  have := ge_of_tendsto ((hcont.tendsto _).comp hlim)
    (Eventually.of_forall fun n => sub_nonneg.2 (hiter n z x x' w a b ha hb hab hw))
  simp only at this ⊢
  linarith

include hS in
/-- **SL Thm 9.9** (variant): the optimal choice is unique, so the policy is a
single-valued function `g`, and `g` is continuous in `(x, z)`. -/
theorem exists_continuous_policy (hΓ : P.ConvexTech) (hF : P.ConcaveRet) :
    ∃ g : S × Z → S, Continuous g ∧ ∀ s, P.policy s = {g s} := by
  have huniq : ∀ s, ∀ y ∈ P.policy s, ∀ y' ∈ P.policy s, y = y' := by
    rintro ⟨x, z⟩ y hy y' hy'
    by_contra hne
    have hye := P.value_eq_of_mem_policy hy
    have hy'e := P.value_eq_of_mem_policy hy'
    set w : S := ⟨(1 / 2 : ℝ) • (y : E) + (1 / 2 : ℝ) • (y' : E),
      hS y.2 y'.2 (by norm_num) (by norm_num) (by norm_num)⟩
    have hxx : (x : E) = (1 / 2 : ℝ) • (x : E) + (1 / 2 : ℝ) • (x : E) := by
      rw [← add_smul]; norm_num
    have hw : w ∈ P.Γ (x, z) := hΓ z x y x y' x w hy.1 hy'.1 _ _ (by norm_num) (by norm_num)
      (by norm_num) hxx rfl
    have h1 := (hF z x y x y' x w hy.1 hy'.1 _ _ (by norm_num) (by norm_num) (by norm_num) hxx
      rfl).2 rfl hne
    have h2 := P.concave_expect (P.value_concave hS hΓ hF) z y y' w _ _ (by norm_num)
      (by norm_num) (by norm_num) rfl
    have h3 := P.value_ge (x, z) hw
    simp only at h1 h2 h3 hye hy'e
    have hβ := P.β_pos
    nlinarith
  choose g hg using fun s => (P.policy_nonempty_compact_uhc.1 s).1
  have hsing : ∀ s, P.policy s = {g s} := fun s =>
    Set.eq_singleton_iff_unique_mem.2 ⟨hg s, fun y hy => huniq s y hy (g s) (hg s)⟩
  exact ⟨g, continuous_of_argmax_eq_singleton (P.continuous_objective _) P.Γ_continuous
    P.Γ_nonempty P.Γ_compact hsing, hsing⟩

end StochDynProg

end Econ
