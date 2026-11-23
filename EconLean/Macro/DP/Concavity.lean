/-
# Concavity of the value function and the Benveniste–Scheinkman theorem

Stokey–Lucas (SL), *Recursive Methods in Economic Dynamics*, §4.2,
Thms 4.8, 4.10, 4.11; Benveniste and Scheinkman (1979).

**The economics.** With a convex technology (the graph of `Γ` is convex) and a
strictly concave return `F`, the value function inherits strict concavity, so
each state has a *unique* optimal successor and the policy is a continuous
function (SL Thm 4.8). If moreover `F` is differentiable in the state, so is
`V`, with the **envelope formula** `V'(x) = F_x(x, g(x))`: the marginal value
of the state is its marginal return today, holding the optimal choice fixed
(Benveniste–Scheinkman, SL Thm 4.11). Combined with the first-order condition
this yields the Euler equation.

**Setup.** The state space is a convex set `S` in a real normed space `E`
(SL: a convex subset of `ℝ^l`); the dynamic program lives on the subtype `S`.
Convex combinations are written in `E`: "`z = a x + b x'`" means the ambient
vectors satisfy `(z : E) = a • x + b • x'`.

**Documented deviations from SL.**
* Benveniste–Scheinkman is proved for a one-dimensional state (`S ⊆ ℝ`); SL
  treat `ℝ^l`. The proof idea is the same.
* SL assume `g(x₀) ∈ int Γ(x₀)` and derive that `g(x₀) ∈ Γ(x)` for `x` near
  `x₀`; we assume the latter directly (it is the only use of the former), which
  makes the theorem more general.
* SL assume `F` continuously differentiable on the interior of the graph; we
  only need `F(·, g(x₀))` differentiable at `x₀`.
* Benveniste–Scheinkman only needs `V` concave, which follows from weakly
  concave `F`; we reuse SL 4.8's strict-concavity hypothesis (as SL do).
* Open: SL Thm 4.9 (convergence of approximate policies) and multi-dimensional
  Benveniste–Scheinkman.
-/
module

public import EconLean.Macro.DP.Bellman
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.Order.LeftRight

@[expose] public section

namespace Econ

open BoundedContinuousFunction Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- **SL Assumption 4.8** (convex technology): the graph of `Γ` is convex. If
`y ∈ Γ(x)`, `y' ∈ Γ(x')` and `0 < a, b`, `a + b = 1`, then
`a y + b y' ∈ Γ(a x + b x')`. -/
def ConvexGraph (Γ : S → Set S) : Prop :=
  ∀ x y x' y' z w : S, y ∈ Γ x → y' ∈ Γ x' → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
    (z : E) = a • (x : E) + b • (x' : E) → (w : E) = a • (y : E) + b • (y' : E) → w ∈ Γ z

/-- **SL Assumption 4.7** (strictly concave return): `F` is concave on the
graph of `Γ`, strictly so when the current states differ. -/
def StrictlyConcaveReturn (Γ : S → Set S) (F : S → S → ℝ) : Prop :=
  ∀ x y x' y' z w : S, y ∈ Γ x → y' ∈ Γ x' → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
    (z : E) = a • (x : E) + b • (x' : E) → (w : E) = a • (y : E) + b • (y' : E) →
    a * F x y + b * F x' y' ≤ F z w ∧ (x ≠ x' → a * F x y + b * F x' y' < F z w)

/-- A function on the state space is **concave** (strictly when `x ≠ x'`). -/
def StrictlyConcaveFn (f : S → ℝ) : Prop :=
  ∀ x x' z : S, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
    (z : E) = a • (x : E) + b • (x' : E) →
    a * f x + b * f x' ≤ f z ∧ (x ≠ x' → a * f x + b * f x' < f z)

/-- Weak concavity of a function on the state space. -/
def ConcaveFn (f : S → ℝ) : Prop :=
  ∀ x x' z : S, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
    (z : E) = a • (x : E) + b • (x' : E) → a * f x + b * f x' ≤ f z

open scoped Classical in
/-- Extend a function on `S` by `0` to all of `E` (used to state concavity
and derivatives with Mathlib's notions; the junk value `0` off `S` is never
used: everything is evaluated on `S` or near an interior point). -/
noncomputable def extendS (f : S → ℝ) : E → ℝ := fun r => if h : r ∈ S then f ⟨r, h⟩ else 0

/-- Our concavity agrees with Mathlib's `ConcaveOn` on `S`. -/
theorem ConcaveFn.concaveOn (hS : Convex ℝ S) {f : S → ℝ} (hf : ConcaveFn f) :
    ConcaveOn ℝ S (extendS f) := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := hS hx hy ha hb hab
  simp only [extendS, hx, hy, hz, dite_true, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | rfl
  · rcases hb.lt_or_eq with hb' | rfl
    · exact hf ⟨x, hx⟩ ⟨y, hy⟩ ⟨_, hz⟩ a b ha' hb' hab rfl
    · simp only [add_zero] at hab; subst hab; simp
  · simp only [zero_add] at hab; subst hab; simp

namespace DynProg

variable (hS : Convex ℝ S) (P : DynProg S)

include hS in
/-- One application of the Bellman operator turns a concave function into a
strictly concave one (SL Thm 4.8, key step). -/
theorem strictlyConcave_bellmanOp (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F)
    {f : S →ᵇ ℝ} (hf : ConcaveFn (f : S → ℝ)) : StrictlyConcaveFn (P.bellmanOp f : S → ℝ) := by
  intro x x' z a b ha hb hab hz
  obtain ⟨y, hy, he⟩ := (P.isGreatest_bellmanOp f x).1
  obtain ⟨y', hy', he'⟩ := (P.isGreatest_bellmanOp f x').1
  -- the convex combination of the two maximizers is feasible at `z`
  set w : S := ⟨a • (y : E) + b • (y' : E), hS y.2 y'.2 ha.le hb.le hab⟩
  have hw : w ∈ P.Γ z := hΓ x y x' y' z w hy hy' a b ha hb hab hz rfl
  have hTz := (P.isGreatest_bellmanOp f z).2 ⟨w, hw, rfl⟩
  have hfw := hf y y' w a b ha hb hab rfl
  obtain ⟨hF1, hF2⟩ := hF x y x' y' z w hy hy' a b ha hb hab hz rfl
  simp only at he he' hTz
  rw [← he, ← he']
  have hβ := P.β_pos
  have key : a * (P.F x y + P.β * f y) + b * (P.F x' y' + P.β * f y') =
      (a * P.F x y + b * P.F x' y') + P.β * (a * f y + b * f y') := by ring
  refine ⟨?_, fun hne => ?_⟩
  · rw [key]; nlinarith [hF1]
  · rw [key]; nlinarith [hF2 hne]

include hS in
/-- **SL Thm 4.8**: under convex technology and strictly concave returns, the
value function is strictly concave. -/
theorem value_strictlyConcave (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F) :
    StrictlyConcaveFn (P.value : S → ℝ) := by
  -- Iterates of `T` from `0` are concave; concavity survives the limit.
  have hiter : ∀ n, ConcaveFn (P.bellmanOp^[n] 0 : S → ℝ) := by
    intro n
    induction n with
    | zero => intro x x' z a b _ _ _ _; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      intro x x' z a b ha hb hab hz
      exact (P.strictlyConcave_bellmanOp hS hΓ hF ih x x' z a b ha hb hab hz).1
  have hV : ConcaveFn (P.value : S → ℝ) := by
    intro x x' z a b ha hb hab hz
    have hlim := (P.iterate_converges 0).1
    have hcont : Continuous fun f : S →ᵇ ℝ => f z - (a * f x + b * f x') :=
      (lipschitz_eval_const z).continuous.sub
        ((continuous_const.mul (lipschitz_eval_const x).continuous).add
          (continuous_const.mul (lipschitz_eval_const x').continuous))
    have := ge_of_tendsto ((hcont.tendsto _).comp hlim)
      (Eventually.of_forall fun n => sub_nonneg.2 (hiter n x x' z a b ha hb hab hz))
    linarith
  rw [← P.bellmanOp_value]
  exact P.strictlyConcave_bellmanOp hS hΓ hF hV

include hS in
/-- **SL Thm 4.8 (policy)**: the optimal choice is unique at every state, so
the policy correspondence is a single-valued function `g`, and `g` is
continuous. -/
theorem exists_continuous_policy (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F) :
    ∃ g : S → S, Continuous g ∧ ∀ x, P.policy x = {g x} := by
  have hV := P.value_strictlyConcave hS hΓ hF
  have huniq : ∀ x, ∀ y ∈ P.policy x, ∀ y' ∈ P.policy x, y = y' := by
    intro x y hy y' hy'
    by_contra hne
    obtain ⟨hyΓ, hye⟩ := P.mem_policy_iff.1 hy
    obtain ⟨hy'Γ, hy'e⟩ := P.mem_policy_iff.1 hy'
    -- the midpoint of two distinct optimal choices does strictly better
    set w : S := ⟨(1 / 2 : ℝ) • (y : E) + (1 / 2 : ℝ) • (y' : E),
      hS y.2 y'.2 (by norm_num) (by norm_num) (by norm_num)⟩
    have hxx : (x : E) = (1 / 2 : ℝ) • (x : E) + (1 / 2 : ℝ) • (x : E) := by
      rw [← add_smul]; norm_num
    have hw : w ∈ P.Γ x := hΓ x y x y' x w hyΓ hy'Γ _ _ (by norm_num) (by norm_num)
      (by norm_num) hxx rfl
    have h1 := (hF x y x y' x w hyΓ hy'Γ _ _ (by norm_num) (by norm_num) (by norm_num) hxx rfl).1
    have h2 := (hV y y' w _ _ (by norm_num) (by norm_num) (by norm_num) rfl).2 hne
    have h3 := P.bellman_le hw
    have hβ := P.β_pos
    nlinarith
  choose g hg using fun x => P.policy_nonempty x
  have hsing : ∀ x, P.policy x = {g x} := fun x =>
    Set.eq_singleton_iff_unique_mem.2 ⟨hg x, fun y hy => huniq x y hy (g x) (hg x)⟩
  exact ⟨g, P.continuous_policy_of_singleton hsing, hsing⟩

end DynProg

/-! ### Benveniste–Scheinkman -/

/-- **SL Thm 4.10** (one-dimensional). A concave function `V` with a
differentiable minorant `W` touching it at an interior point `x₀` is
differentiable at `x₀`, with `V'(x₀) = W'(x₀)`. (SL also assume `W` concave;
the proof does not need it.) -/
theorem hasDerivAt_of_concaveOn_of_le {D : Set ℝ} {V W : ℝ → ℝ} {x₀ w : ℝ}
    (hD : D ∈ 𝓝 x₀) (hV : ConcaveOn ℝ D V) (hW : HasDerivAt W w x₀)
    (hle : ∀ᶠ x in 𝓝 x₀, W x ≤ V x) (heq : W x₀ = V x₀) : HasDerivAt V w x₀ := by
  have hWs := hasDerivAt_iff_tendsto_slope.1 hW
  rw [slope_fun_def_field] at hWs
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]
  -- a symmetric interval around `x₀` inside `D` on which `W ≤ V`
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hD hle)
  have hin : ∀ x, |x - x₀| < δ → x ∈ D ∧ W x ≤ V x := fun x hx =>
    hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hx)
  have hx₀D : x₀ ∈ D := (hin x₀ (by simp [hδ])).1
  have hWl : Tendsto (fun x => (W x - W x₀) / (x - x₀)) (𝓝[<] x₀) (𝓝 w) :=
    hWs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
  have hWr : Tendsto (fun x => (W x - W x₀) / (x - x₀)) (𝓝[>] x₀) (𝓝 w) :=
    hWs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have near_l : ∀ᶠ x in 𝓝[<] x₀, x₀ - δ < x ∧ x < x₀ := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith : x₀ - δ < x₀)] with x hx using hx
  have near_r : ∀ᶠ x in 𝓝[>] x₀, x₀ < x ∧ x < x₀ + δ := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : x₀ < x₀ + δ)] with x hx using hx
  have mem : ∀ x, x₀ - δ < x → x < x₀ + δ → x ∈ D ∧ W x ≤ V x := fun x h1 h2 =>
    hin x (abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩)
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup]
  constructor
  · -- left: `w ≤ slope V ≤ slope W → w`
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hWl ?_ ?_
    · filter_upwards [near_l] with x ⟨hx1, hx2⟩
      refine le_of_tendsto hWr ?_
      filter_upwards [near_r] with x'' ⟨h1, h2⟩
      have hc := hV.slope_anti_adjacent (mem x hx1 (by linarith)).1
        (mem x'' (by linarith) h2).1 hx2 h1
      have hWV := (mem x'' (by linarith) h2).2
      have e1 : (W x'' - W x₀) / (x'' - x₀) ≤ (V x'' - V x₀) / (x'' - x₀) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e2 : (V x - V x₀) / (x - x₀) = (V x₀ - V x) / (x₀ - x) := by
        rw [← neg_sub (V x₀), ← neg_sub x₀, neg_div_neg_eq]
      rw [e2]; linarith
    · filter_upwards [near_l] with x ⟨hx1, hx2⟩
      have hWV := (mem x hx1 (by linarith)).2
      exact div_le_div_of_nonpos_of_le (by linarith) (by linarith)
  · -- right: `slope W ≤ slope V ≤ w`
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hWr tendsto_const_nhds ?_ ?_
    · filter_upwards [near_r] with x ⟨hx1, hx2⟩
      have hWV := (mem x (by linarith) hx2).2
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    · filter_upwards [near_r] with x ⟨hx1, hx2⟩
      refine ge_of_tendsto hWl ?_
      filter_upwards [near_l] with x' ⟨h1, h2⟩
      have hc := hV.slope_anti_adjacent (mem x' h1 (by linarith)).1
        (mem x (by linarith) hx2).1 h2 hx1
      have hWV := (mem x' h1 (by linarith)).2
      have e1 : (V x' - V x₀) / (x' - x₀) ≤ (W x' - W x₀) / (x' - x₀) :=
        div_le_div_of_nonpos_of_le (by linarith) (by linarith)
      have e2 : (V x₀ - V x') / (x₀ - x') = (V x' - V x₀) / (x' - x₀) := by
        rw [← neg_sub (V x'), ← neg_sub x', neg_div_neg_eq]
      rw [e2] at hc; linarith

/-- **Benveniste–Scheinkman** (SL Thm 4.11, one-dimensional state).
Let `S ⊆ ℝ` be convex, with convex technology and strictly concave returns.
Let `x₀` be interior to `S` and `y₀` optimal at `x₀`, and suppose `y₀` stays
feasible for states near `x₀`. If `F(·, y₀)` is differentiable at `x₀` with
derivative `F_x`, then `V` is differentiable at `x₀` and `V'(x₀) = F_x`:
the envelope formula. -/
theorem DynProg.hasDerivAt_value {S : Set ℝ} (hS : Convex ℝ S) (P : DynProg S)
    (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F)
    {x₀ y₀ : S} (hint : (x₀ : ℝ) ∈ interior S) (hy₀ : y₀ ∈ P.policy x₀)
    (hloc : ∀ᶠ r in 𝓝 (x₀ : ℝ), ∀ h : r ∈ S, y₀ ∈ P.Γ ⟨r, h⟩)
    {Fx : ℝ} (hFx : HasDerivAt (extendS fun x => P.F x y₀) Fx x₀) :
    HasDerivAt (extendS (P.value : S → ℝ)) Fx x₀ := by
  have hSn : S ∈ 𝓝 (x₀ : ℝ) := mem_interior_iff_mem_nhds.1 hint
  have hconc : ConcaveOn ℝ S (extendS (P.value : S → ℝ)) :=
    ConcaveFn.concaveOn hS fun x x' z a b ha hb hab hz =>
      (P.value_strictlyConcave hS hΓ hF x x' z a b ha hb hab hz).1
  -- minorant: keep the choice `y₀` fixed and vary today's state
  set W : ℝ → ℝ := fun r => extendS (fun x => P.F x y₀) r + P.β * P.value y₀
  have hW : HasDerivAt W Fx x₀ := by simpa [W] using hFx.add_const (P.β * P.value y₀)
  refine hasDerivAt_of_concaveOn_of_le hSn hconc hW ?_ ?_
  · filter_upwards [hloc, hSn] with r hr hrS
    simp only [W, extendS, hrS, dite_true]
    exact P.bellman_le (hr hrS)
  · simp only [W, extendS, x₀.2, dite_true]
    exact (P.mem_policy_iff.1 hy₀).2

end Econ
