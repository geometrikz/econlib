/-
# The Solow growth model (discrete time)

Acemoglu, *Introduction to Modern Economic Growth*, ch. 2 (§2.2–2.3:
Assumptions 1–2, Propositions 2.2–2.3 and 2.5); Barro and Sala-i-Martin ch. 1;
Romer, *Advanced Macroeconomics*, ch. 1.

**The economics.** Output is produced from capital and labour with a
constant-returns technology, so everything can be written *per worker*:
`k` is capital per worker and `f k` output per worker (the "intensive form").
A constant fraction `s` of output is saved and invested, capital depreciates
at rate `δ`, and the labour force grows at rate `n`. Capital per worker then
evolves by

    (1 + n) k_{t+1} = s f(k_t) + (1 − δ) k_t.

(With `n = 0` this is exactly Acemoglu's eq. (2.17).) A **steady state** is a
`k* > 0` with `k_{t+1} = k_t = k*`, which rearranges to the familiar
"investment = break-even investment" condition

    s f(k*) = (n + δ) k*.

Main results (all proved, no `sorry`):
* `Economy.existsUnique_steadyState`: there is exactly one steady state with
  `k* > 0` (Acemoglu Prop. 2.2).
* `Economy.tendsto_path`: from **any** initial `k₀ > 0` capital per worker
  converges to `k*` (global stability, Acemoglu Prop. 2.5).
* `Economy.path_monotone_of_le`, `Economy.path_antitone_of_ge`: the convergence
  is monotone; below `k*` capital rises, above it capital falls.
* `Economy.path_strictMono_of_lt`, `Economy.path_strictAnti_of_gt`: strict
  versions (Acemoglu Prop. 2.5): `k_t` never reaches or crosses `k*`.
* `Economy.fixedPoint_iff`: on `[0, ∞)` the only fixed points are `0` and `k*`.
* `Economy.steadyState_strictMono_s`, `steadyState_strictAnti_n`,
  `steadyState_strictAnti_δ`: comparative statics (Acemoglu Prop. 2.3).
* `Economy.tendsto_output`: output per worker converges to `f(k*)`.
* `Economy.growthRate_strictAntiOn`: conditional convergence, poorer
  economies grow faster.
* `cobbDouglas_steadyState`: for `f k = k^α` the steady state is
  `(s / (n + δ))^{1/(1−α)}`, the textbook closed form (a "unit test" pinning
  the definitions to the formula every student knows).

**The assumptions on `f`.** Acemoglu assumes `f` is twice differentiable,
increasing and strictly concave with `f 0 = 0` (Assumption 1), plus the Inada
conditions `f'(k) → ∞` as `k → 0` and `f'(k) → 0` as `k → ∞` (Assumption 2).
The proofs only ever use the *average product* `f k / k`, so the structure
`NeoclassicalProduction` states the Inada conditions in average-product form:
`f k / k → ∞` as `k ↓ 0` and `f k / k → 0` as `k → ∞`. The theorem
`NeoclassicalProduction.of_deriv` shows that Acemoglu's derivative version
implies ours, so nothing is lost; our hypotheses are strictly weaker (they do
not need differentiability at all).

**Deviations from the textbook (reviewed, all generalizations).**
* No differentiability: Inada conditions are on the average product (equivalent
  to Acemoglu's for differentiable concave `f`; `of_deriv` proves the direction
  we need). Continuity at `k = 0` is assumed explicitly because a concave
  function may jump at the boundary of its domain.
* Wider parameter ranges: `s ∈ (0,1]`, `δ ∈ [0,1]`, `n > −1`, `n + δ > 0`.
  Acemoglu's §2.2 model is the special case `n = 0`, `s, δ ∈ (0,1)`.
* We work with the intensive form `f(k) = F(k, 1)` directly rather than deriving
  it from a constant-returns `F(K, L)`.
* Comparative statics are stated as strict monotonicity of `k*` in `s`, `n`,
  `δ`, which needs no derivatives.

Not yet covered (follow-ups): comparative statics in technology `A f`, the
golden rule, labour-augmenting technical progress, speed of convergence, and
the continuous-time model.

**The Lean.** The law of motion is a function `next : ℝ → ℝ`, and the path
from `k₀` is its `t`-fold iterate `next^[t] k₀` (`Nat.iterate`). Convergence
is `Filter.Tendsto (path k₀) atTop (𝓝 k*)`: Mathlib's way of writing
`lim_{t→∞} k_t = k*`.
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

noncomputable section

namespace Econ
namespace Solow

open Set Filter Topology

/-! ## The production function -/

/-- A **neoclassical production function** in intensive form (Acemoglu
Assumptions 1–2), with the Inada conditions stated for the average product
`f k / k`. See `NeoclassicalProduction.of_deriv` for the derivative version.

Only nonnegative capital is economically meaningful, so every condition is
stated on `[0, ∞)` (`Set.Ici 0`); what `f` does on negative numbers is
irrelevant. -/
structure NeoclassicalProduction (f : ℝ → ℝ) : Prop where
  /-- No capital, no output. -/
  map_zero : f 0 = 0
  /-- Output is continuous at `k = 0` (from the right): a little capital
  produces a little output. Continuity on `(0, ∞)` is automatic from
  concavity (`NeoclassicalProduction.continuousOn`), but a concave function may
  jump at the boundary of its domain, so this is assumed. -/
  continuousWithinAt_zero : ContinuousWithinAt f (Ici 0) 0
  /-- More capital never lowers output. -/
  monotoneOn : MonotoneOn f (Ici 0)
  /-- Diminishing returns to capital. -/
  strictConcaveOn : StrictConcaveOn ℝ (Ici 0) f
  /-- Inada at zero: the average product `f k / k` blows up as `k ↓ 0`.
  (`𝓝[>] 0` is the filter "k tends to 0 from the right".) -/
  inada_zero : Tendsto (fun k => f k / k) (𝓝[>] 0) atTop
  /-- Inada at infinity: the average product vanishes as `k → ∞`. -/
  inada_atTop : Tendsto (fun k => f k / k) atTop (𝓝 0)

namespace NeoclassicalProduction

variable {f : ℝ → ℝ}

/-- `f` is continuous on `(0, ∞)`. This is not an extra assumption: a concave
function is automatically continuous on the interior of its domain. -/
theorem continuousOn (hf : NeoclassicalProduction f) : ContinuousOn f (Ioi 0) := by
  have := hf.strictConcaveOn.concaveOn.continuousOn_interior
  rwa [interior_Ici] at this

/-- **Diminishing average product.** With `f 0 = 0` and strict concavity,
`f k / k` is strictly decreasing in `k > 0`. Geometrically: the chord from the
origin to the graph gets flatter as `k` grows. This single fact drives both
uniqueness and stability of the steady state.

Proof: for `0 < a < b`, write `a` as the mix `(a/b)·b + (1 − a/b)·0`; strict
concavity gives `f a > (a/b) f b + (1 − a/b) f 0 = (a/b) f b`. -/
theorem avg_strictAntiOn (hf : NeoclassicalProduction f) :
    StrictAntiOn (fun k => f k / k) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  obtain ⟨-, hsc⟩ := hf.strictConcaveOn
  have key := hsc (mem_Ici.2 hb.le) (mem_Ici.2 (le_refl (0 : ℝ)))
    hb.ne' (div_pos ha hb)
    (by rw [sub_pos, div_lt_one hb]; exact hab) (add_sub_cancel (a / b) 1)
  simp only [smul_eq_mul, mul_zero, add_zero, hf.map_zero] at key
  rw [div_mul_cancel₀ a hb.ne'] at key
  -- `key : a / b * f b < f a`; now clear denominators.
  show f b / b < f a / a
  rw [div_lt_div_iff₀ hb ha]
  calc f b * a = a / b * f b * b := by field_simp
    _ < f a * b := mul_lt_mul_of_pos_right key hb

/-- The average product is strictly positive (it decreases strictly towards
its limit `0`), hence so is output at any `k > 0`. -/
theorem avg_pos (hf : NeoclassicalProduction f) {k : ℝ} (hk : 0 < k) : 0 < f k / k := by
  -- `f k / k > f (2k) / (2k) ≥ lim = 0`.
  have h2k : (0 : ℝ) < 2 * k := by positivity
  have hlt : f (2 * k) / (2 * k) < f k / k :=
    hf.avg_strictAntiOn hk h2k (by linarith)
  have hge : 0 ≤ f (2 * k) / (2 * k) := by
    refine le_of_tendsto hf.inada_atTop ?_
    filter_upwards [eventually_gt_atTop (2 * k)] with x hx
    exact (hf.avg_strictAntiOn h2k (h2k.trans hx) hx).le
  linarith

theorem pos (hf : NeoclassicalProduction f) {k : ℝ} (hk : 0 < k) : 0 < f k := by
  have := hf.avg_pos hk
  rwa [div_pos_iff_of_pos_right hk] at this

/-- `f` is in fact *strictly* increasing on `[0, ∞)`: a flat stretch
`f a = f b` would put the midpoint's value strictly above the chord (strict
concavity) yet at most `f b` (monotonicity). -/
theorem strictMonoOn (hf : NeoclassicalProduction f) : StrictMonoOn f (Ici 0) := by
  intro a ha b hb hab
  refine lt_of_le_of_ne (hf.monotoneOn ha hb hab.le) fun heq => ?_
  obtain ⟨-, hsc⟩ := hf.strictConcaveOn
  have hmid := hsc ha hb hab.ne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hm : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ Ici (0 : ℝ) := by
    simp only [smul_eq_mul, mem_Ici] at ha hb ⊢; linarith
  have hle := hf.monotoneOn hm hb (by simp only [smul_eq_mul]; linarith)
  simp only [smul_eq_mul] at hmid hle
  rw [← heq] at hle
  linarith

/-- **Acemoglu's assumptions imply ours.** Suppose `f 0 = 0`, `f` is strictly
concave on `[0, ∞)`, differentiable at every `k > 0` with derivative
`f' k > 0`, and satisfies the derivative Inada conditions
`f' k → ∞` as `k ↓ 0` and `f' k → 0` as `k → ∞` (Acemoglu Assumptions 1–2;
twice-differentiability is not needed, and `hpos` could be derived from
the other assumptions but is kept to match the textbook). Then `f` is a
`NeoclassicalProduction`.

The bridge is the tangent-line property of concave functions: the chord from
`0` to `k` is steeper than the tangent at `k`, so `f k / k ≥ f' k`; and the
graph lies below its tangent at any `K`, so `f k ≤ f K + f' K (k − K)`. -/
theorem of_deriv {f' : ℝ → ℝ} (h0 : f 0 = 0) (hcont0 : ContinuousWithinAt f (Ici 0) 0)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hderiv : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hpos : ∀ k, 0 < k → 0 < f' k)
    (hinada0 : Tendsto f' (𝓝[>] 0) atTop) (hinadaTop : Tendsto f' atTop (𝓝 0)) :
    NeoclassicalProduction f := by
  -- Chord from the origin vs tangent at `k`: `f' k ≤ f k / k`.
  have chord : ∀ k, 0 < k → f' k ≤ f k / k := by
    intro k hk
    have := hconc.concaveOn.le_slope_of_hasDerivAt (x := 0) (y := k) (mem_Ici.2 le_rfl)
      (mem_Ici.2 hk.le) hk (hderiv k hk)
    simpa [slope_def_field, h0] using this
  -- Tangent at `K` lies above the graph: `f k ≤ f K + f' K * (k - K)` for `k > K`.
  have tangent : ∀ K k, 0 < K → K < k → f k ≤ f K + f' K * (k - K) := by
    intro K k hK hKk
    have := hconc.concaveOn.slope_le_of_hasDerivAt (x := K) (y := k) (mem_Ici.2 hK.le)
      (mem_Ici.2 (hK.trans hKk).le) hKk (hderiv K hK)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hKk)] at this
    linarith
  -- `f` is monotone on `[0, ∞)`: strictly increasing on `(0, ∞)` since `f' > 0`,
  -- and `f k ≥ k f' k > 0 = f 0` handles the endpoint.
  have fpos : ∀ k, 0 < k → 0 < f k := fun k hk => by
    have := (hpos k hk).trans_le (chord k hk)
    rwa [div_pos_iff_of_pos_right hk] at this
  have hmonoIoi : MonotoneOn f (Ioi 0) := by
    refine (strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_).monotoneOn
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(hderiv x hx).deriv]
      exact hpos x hx
  refine ⟨h0, hcont0, ?_, hconc, ?_, ?_⟩
  · intro a ha b hb hab
    rcases (mem_Ici.1 ha).eq_or_lt with h | h
    · subst h
      rcases (mem_Ici.1 hb).eq_or_lt with h' | h'
      · rw [← h']
      · rw [h0]; exact (fpos b h').le
    · exact hmonoIoi h (h.trans_le hab) hab
  · -- `f k / k ≥ f' k → ∞`.
    refine tendsto_atTop_mono' _ ?_ hinada0
    filter_upwards [self_mem_nhdsWithin] with k hk using chord k hk
  · -- `0 < f k / k ≤ f K / k + f' K`, and both terms can be made small.
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [eventually_gt_atTop 0] with k hk
      exact ha.trans ((hpos k hk).trans_le (chord k hk))
    · -- choose `K > 0` with `f' K < a / 2`
      obtain ⟨K, hK, hK0⟩ :=
        ((hinadaTop.eventually (gt_mem_nhds (half_pos ha))).and
          (eventually_gt_atTop (0 : ℝ))).exists
      have hlim : Tendsto (fun k : ℝ => f K / k) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      filter_upwards [hlim.eventually (gt_mem_nhds (half_pos ha)), eventually_gt_atTop K]
        with k hk1 hk2
      have hk0 : 0 < k := hK0.trans hk2
      have ht := tangent K k hK0 hk2
      have hfK : 0 ≤ f' K := (hpos K hK0).le
      rw [div_lt_iff₀ hk0]
      rw [div_lt_iff₀ hk0] at hk1
      nlinarith

end NeoclassicalProduction

/-! ## The economy -/

/-- A Solow economy: a production function and the three behavioural /
demographic parameters. Parameter ranges are the widest under which the
model makes sense: saving rate `s ∈ (0, 1]`, depreciation `δ ∈ [0, 1]`,
population growth `n > −1` (the population may shrink), and effective
depreciation `n + δ > 0` (otherwise capital per worker never wears out and
there is no steady state). Acemoglu's `s ∈ (0,1)`, `δ ∈ (0,1)`, `n ≥ 0` is a
special case. -/
structure Economy where
  /-- Output per worker as a function of capital per worker. -/
  f : ℝ → ℝ
  /-- Saving (= investment) rate. -/
  s : ℝ
  /-- Depreciation rate. -/
  δ : ℝ
  /-- Population growth rate. -/
  n : ℝ
  hf : NeoclassicalProduction f
  hs_pos : 0 < s
  hs_le_one : s ≤ 1
  hδ_nonneg : 0 ≤ δ
  hδ_le_one : δ ≤ 1
  hn : -1 < n
  hnδ : 0 < n + δ

namespace Economy

variable (E : Economy)

/-- The law of motion: `k_{t+1} = (s f(k_t) + (1 − δ) k_t) / (1 + n)`. -/
def next (k : ℝ) : ℝ := (E.s * E.f k + (1 - E.δ) * k) / (1 + E.n)

/-- The path of capital per worker from initial capital `k₀`:
`path k₀ t = k_t`, the `t`-fold iterate of `next`. -/
def path (k₀ : ℝ) (t : ℕ) : ℝ := E.next^[t] k₀

@[simp] theorem path_zero (k₀ : ℝ) : E.path k₀ 0 = k₀ := rfl

/-- `k_{t+1} = next k_t`. -/
theorem path_succ (k₀ : ℝ) (t : ℕ) : E.path k₀ (t + 1) = E.next (E.path k₀ t) :=
  Function.iterate_succ_apply' _ _ _

/-- A steady state is a strictly positive fixed point of the law of motion.
(`k = 0` is always a trivial fixed point; Acemoglu's Prop. 2.2 is about the
unique *positive* one.) -/
def IsSteadyState (k : ℝ) : Prop := 0 < k ∧ E.next k = k

/-- `1 + n > 0`, so dividing by it is harmless. -/
theorem one_add_n_pos : 0 < 1 + E.n := by linarith [E.hn]

/-- `k = 0` is the trivial steady state: no capital, no output, no saving. -/
theorem next_zero : E.next 0 = 0 := by simp [next, E.hf.map_zero]

/-- `k_{t+1} − k_t = k_t (s · f(k_t)/k_t − (n + δ)) / (1 + n)`: capital per
worker grows exactly when saving per unit of capital exceeds break-even
investment `n + δ`. -/
theorem next_sub_self {k : ℝ} (hk : 0 < k) :
    E.next k - k = k * (E.s * (E.f k / k) - (E.n + E.δ)) / (1 + E.n) := by
  have h1 := E.one_add_n_pos
  unfold next
  field_simp
  ring

theorem next_eq_self_iff {k : ℝ} (hk : 0 < k) :
    E.next k = k ↔ E.s * (E.f k / k) = E.n + E.δ := by
  rw [← sub_eq_zero, E.next_sub_self hk, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
  have := E.one_add_n_pos
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hk.ne'
    · exact h
    · exact absurd h this.ne'
  · exact fun h => Or.inl (Or.inr h)

/-- **Steady state ⟺ investment equals break-even investment:**
`k* > 0` is a steady state iff `s f(k*) = (n + δ) k*`. -/
theorem isSteadyState_iff {k : ℝ} :
    E.IsSteadyState k ↔ 0 < k ∧ E.s * E.f k = (E.n + E.δ) * k := by
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have := (E.next_eq_self_iff hk).1 h
    field_simp at this
    linarith
  · rintro ⟨hk, h⟩
    refine ⟨hk, (E.next_eq_self_iff hk).2 ?_⟩
    field_simp
    linarith

theorem le_next_iff {k : ℝ} (hk : 0 < k) : k ≤ E.next k ↔ E.n + E.δ ≤ E.s * (E.f k / k) := by
  rw [← sub_nonneg, E.next_sub_self hk, div_nonneg_iff]
  have h1 := E.one_add_n_pos
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · by_contra hc
      have := mul_neg_of_pos_of_neg hk (sub_neg.2 (not_le.1 hc))
      linarith
    · linarith
  · intro h
    exact Or.inl ⟨mul_nonneg hk.le (by linarith), h1.le⟩

theorem next_le_iff {k : ℝ} (hk : 0 < k) : E.next k ≤ k ↔ E.s * (E.f k / k) ≤ E.n + E.δ := by
  rw [← sub_nonpos, E.next_sub_self hk, div_nonpos_iff]
  have h1 := E.one_add_n_pos
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · by_contra hc
      have := mul_pos hk (sub_pos.2 (not_le.1 hc))
      linarith
  · intro h
    exact Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith), h1.le⟩

/-- The law of motion is increasing in `k` (on `k ≥ 0`): more capital today
means more capital tomorrow. This uses `δ ≤ 1`. -/
theorem next_monotoneOn : MonotoneOn E.next (Ici 0) := by
  intro a ha b hb hab
  unfold next
  have h1 := E.one_add_n_pos
  gcongr
  · exact E.hs_pos.le
  · exact E.hf.monotoneOn ha hb hab
  · linarith [E.hδ_le_one]

/-- The law of motion is *strictly* increasing on `k ≥ 0`. -/
theorem next_strictMonoOn : StrictMonoOn E.next (Ici 0) := by
  intro a ha b hb hab
  unfold next
  have h1 := E.one_add_n_pos
  have hf := mul_lt_mul_of_pos_left (E.hf.strictMonoOn ha hb hab) E.hs_pos
  have hl := mul_le_mul_of_nonneg_left hab.le (by linarith [E.hδ_le_one] : 0 ≤ 1 - E.δ)
  exact div_lt_div_of_pos_right (by linarith) h1

theorem next_pos {k : ℝ} (hk : 0 < k) : 0 < E.next k := by
  unfold next
  have h1 := E.one_add_n_pos
  have := E.hf.pos hk
  have : 0 ≤ (1 - E.δ) * k := mul_nonneg (by linarith [E.hδ_le_one]) hk.le
  have := E.hs_pos
  positivity

theorem path_pos {k₀ : ℝ} (hk₀ : 0 < k₀) (t : ℕ) : 0 < E.path k₀ t := by
  induction t with
  | zero => exact hk₀
  | succ t ih => rw [path_succ]; exact E.next_pos ih

theorem continuousOn_next : ContinuousOn E.next (Ioi 0) := by
  unfold next
  exact ((continuousOn_const.mul E.hf.continuousOn).add
    (continuousOn_const.mul continuousOn_id)).div_const _

/-! ## Existence and uniqueness of the steady state -/

/-- **Existence and uniqueness of the steady state** (Acemoglu Prop. 2.2).
There is exactly one `k* > 0` with `next k* = k*`.

Proof idea: steady states are the solutions of `s · f(k)/k = n + δ`. The left
side is continuous, strictly decreasing (diminishing average product), goes to
`∞` as `k ↓ 0` and to `0 < n + δ` as `k → ∞` (Inada). The intermediate value
theorem gives a solution, and strict monotonicity makes it unique. -/
theorem existsUnique_steadyState : ∃! k, E.IsSteadyState k := by
  set c := E.n + E.δ with hc
  have hc0 : 0 < c := E.hnδ
  -- φ(k) = s · f(k)/k
  set φ : ℝ → ℝ := fun k => E.s * (E.f k / k) with hφ
  have hφanti : StrictAntiOn φ (Ioi 0) := fun a ha b hb hab =>
    mul_lt_mul_of_pos_left (E.hf.avg_strictAntiOn ha hb hab) E.hs_pos
  -- a point with φ a > c, near zero
  have h0 : Tendsto φ (𝓝[>] 0) atTop := E.hf.inada_zero.const_mul_atTop E.hs_pos
  obtain ⟨a, ha, ha0⟩ :=
    ((h0.eventually_gt_atTop c).and self_mem_nhdsWithin).exists
  -- a point `b > a` with φ b < c, far out
  have hTop : Tendsto φ atTop (𝓝 0) := by
    simpa using E.hf.inada_atTop.const_mul E.s
  obtain ⟨b, hb, hab⟩ :=
    ((hTop.eventually (gt_mem_nhds hc0)).and (eventually_gt_atTop a)).exists
  have ha0' : (0 : ℝ) < a := ha0
  have hcont : ContinuousOn φ (Icc a b) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine (E.hf.continuousOn.mono ?_).div continuousOn_id ?_
    · intro x hx; exact ha0'.trans_le hx.1
    · intro x hx; exact (ha0'.trans_le hx.1).ne'
  obtain ⟨k, hk, hφk⟩ := intermediate_value_Icc' hab.le hcont ⟨hb.le, ha.le⟩
  have hk0 : 0 < k := ha0'.trans_le hk.1
  refine ⟨k, ⟨hk0, (E.next_eq_self_iff hk0).2 hφk⟩, ?_⟩
  rintro k' ⟨hk'0, hk'⟩
  have hφk' := (E.next_eq_self_iff hk'0).1 hk'
  exact hφanti.injOn hk'0 hk0 (hφk'.trans hφk.symm)

/-- Uniqueness, in the form "any two steady states coincide". -/
theorem IsSteadyState.unique {k₁ k₂ : ℝ} (h₁ : E.IsSteadyState k₁) (h₂ : E.IsSteadyState k₂) :
    k₁ = k₂ :=
  E.existsUnique_steadyState.unique h₁ h₂

/-! ## Global stability -/

/-- Below the steady state, capital grows: `k ≤ k*` implies `k ≤ next k`.
(Average product is higher at smaller `k`, so saving exceeds break-even.) -/
theorem le_next_of_le {kstar k : ℝ} (hs : E.IsSteadyState kstar) (hk : 0 < k)
    (hle : k ≤ kstar) : k ≤ E.next k := by
  rw [E.le_next_iff hk, ← (E.next_eq_self_iff hs.1).1 hs.2]
  exact mul_le_mul_of_nonneg_left (E.hf.avg_strictAntiOn.antitoneOn hk hs.1 hle) E.hs_pos.le

/-- Above the steady state, capital falls. -/
theorem next_le_of_ge {kstar k : ℝ} (hs : E.IsSteadyState kstar) (hk : 0 < k)
    (hge : kstar ≤ k) : E.next k ≤ k := by
  rw [E.next_le_iff hk, ← (E.next_eq_self_iff hs.1).1 hs.2]
  exact mul_le_mul_of_nonneg_left (E.hf.avg_strictAntiOn.antitoneOn hs.1 hk hge) E.hs_pos.le

/-- If the path converges to some `L > 0`, then `L` is a fixed point
(by continuity of the law of motion). -/
theorem next_eq_of_tendsto {k₀ L : ℝ} (hL : 0 < L)
    (h : Tendsto (E.path k₀) atTop (𝓝 L)) : E.next L = L := by
  have h1 : Tendsto (fun t => E.path k₀ (t + 1)) atTop (𝓝 L) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => E.path k₀ (t + 1)) atTop (𝓝 (E.next L)) := by
    simp only [path_succ]
    exact ((E.continuousOn_next L hL).continuousAt (Ioi_mem_nhds hL)).tendsto.comp h
  exact tendsto_nhds_unique h2 h1

/-- Starting below the steady state, the path stays in `(0, k*]`. -/
theorem path_le_of_le {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀)
    (hle : k₀ ≤ kstar) (t : ℕ) : E.path k₀ t ≤ kstar := by
  induction t with
  | zero => exact hle
  | succ t ih =>
    rw [path_succ, ← hs.2]
    exact E.next_monotoneOn (mem_Ici.2 (E.path_pos hk₀ t).le) (mem_Ici.2 hs.1.le) ih

/-- Starting above the steady state, the path stays in `[k*, ∞)`. -/
theorem le_path_of_ge {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar)
    (hge : kstar ≤ k₀) (t : ℕ) : kstar ≤ E.path k₀ t := by
  induction t with
  | zero => exact hge
  | succ t ih =>
    rw [path_succ]
    conv_lhs => rw [← hs.2]
    exact E.next_monotoneOn (mem_Ici.2 hs.1.le) (mem_Ici.2 (hs.1.le.trans ih)) ih

/-- **Monotone convergence from below:** if `0 < k₀ ≤ k*`, capital per worker
rises every period. -/
theorem path_monotone_of_le {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀)
    (hle : k₀ ≤ kstar) : Monotone (E.path k₀) := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [path_succ]
  exact E.le_next_of_le hs (E.path_pos hk₀ t) (E.path_le_of_le hs hk₀ hle t)

/-- **Monotone convergence from above:** if `k₀ ≥ k*`, capital per worker
falls every period. -/
theorem path_antitone_of_ge {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar)
    (hge : kstar ≤ k₀) : Antitone (E.path k₀) := by
  refine antitone_nat_of_succ_le fun t => ?_
  rw [path_succ]
  have := E.le_path_of_ge hs hge t
  exact E.next_le_of_ge hs (hs.1.trans_le this) this

/-- Strictly below the steady state, capital grows strictly and stays strictly
below `k*`. -/
theorem lt_next_of_lt {kstar k : ℝ} (hs : E.IsSteadyState kstar) (hk : 0 < k)
    (hlt : k < kstar) : k < E.next k := by
  have h := mul_lt_mul_of_pos_left (E.hf.avg_strictAntiOn hk hs.1 hlt) E.hs_pos
  rw [(E.next_eq_self_iff hs.1).1 hs.2] at h
  have := E.next_sub_self hk
  have h1 := E.one_add_n_pos
  have : 0 < E.next k - k := by
    rw [this]; exact div_pos (mul_pos hk (by linarith)) h1
  linarith

theorem next_lt_of_gt {kstar k : ℝ} (hs : E.IsSteadyState kstar) (hk : kstar < k) :
    E.next k < k := by
  have hk0 : 0 < k := hs.1.trans hk
  have h := mul_lt_mul_of_pos_left (E.hf.avg_strictAntiOn hs.1 hk0 hk) E.hs_pos
  rw [(E.next_eq_self_iff hs.1).1 hs.2] at h
  have := E.next_sub_self hk0
  have h1 := E.one_add_n_pos
  have : E.next k - k < 0 := by
    rw [this]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hk0 (by linarith)) h1
  linarith

theorem path_lt_of_lt {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀)
    (hlt : k₀ < kstar) (t : ℕ) : E.path k₀ t < kstar := by
  induction t with
  | zero => exact hlt
  | succ t ih =>
    rw [path_succ, ← hs.2]
    exact E.next_strictMonoOn (mem_Ici.2 (E.path_pos hk₀ t).le) (mem_Ici.2 hs.1.le) ih

theorem lt_path_of_gt {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar)
    (hgt : kstar < k₀) (t : ℕ) : kstar < E.path k₀ t := by
  induction t with
  | zero => exact hgt
  | succ t ih =>
    rw [path_succ]
    conv_lhs => rw [← hs.2]
    exact E.next_strictMonoOn (mem_Ici.2 hs.1.le) (mem_Ici.2 (hs.1.le.trans ih.le)) ih

/-- **Strict version (Acemoglu Prop. 2.5):** if `0 < k₀ < k*`, then `k_t` is
strictly increasing and `k_t < k*` for all `t`. -/
theorem path_strictMono_of_lt {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀)
    (hlt : k₀ < kstar) : StrictMono (E.path k₀) ∧ ∀ t, E.path k₀ t < kstar := by
  refine ⟨strictMono_nat_of_lt_succ fun t => ?_, E.path_lt_of_lt hs hk₀ hlt⟩
  rw [path_succ]
  exact E.lt_next_of_lt hs (E.path_pos hk₀ t) (E.path_lt_of_lt hs hk₀ hlt t)

/-- If `k₀ > k*`, then `k_t` is strictly decreasing and `k_t > k*` for all `t`. -/
theorem path_strictAnti_of_gt {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar)
    (hgt : kstar < k₀) : StrictAnti (E.path k₀) ∧ ∀ t, kstar < E.path k₀ t := by
  refine ⟨strictAnti_nat_of_succ_lt fun t => ?_, E.lt_path_of_gt hs hgt⟩
  rw [path_succ]
  exact E.next_lt_of_gt hs (E.lt_path_of_gt hs hgt t)

/-- **Global stability of the steady state** (Acemoglu Prop. 2.5, discrete
time). From every initial capital stock `k₀ > 0`, capital per worker converges
to the steady state `k*`.

Proof: if `k₀ ≤ k*` the path is increasing and bounded above by `k*`, so it
converges (monotone convergence theorem) to some `L ∈ [k₀, k*]`; if `k₀ ≥ k*`
it is decreasing and bounded below by `k*`, converging to some `L ≥ k*`. In
both cases `L > 0`, continuity makes `L` a fixed point, and uniqueness of the
steady state forces `L = k*`. -/
theorem tendsto_path {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀) :
    Tendsto (E.path k₀) atTop (𝓝 kstar) := by
  rcases le_total k₀ kstar with hle | hge
  · have hmono := E.path_monotone_of_le hs hk₀ hle
    have hbdd : BddAbove (range (E.path k₀)) :=
      ⟨kstar, by rintro _ ⟨t, rfl⟩; exact E.path_le_of_le hs hk₀ hle t⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    set L := ⨆ t, E.path k₀ t
    have hL : 0 < L := hk₀.trans_le (le_ciSup hbdd 0)
    have : L = kstar := (IsSteadyState.unique E ⟨hL, E.next_eq_of_tendsto hL hlim⟩ hs)
    rwa [this] at hlim
  · have hanti := E.path_antitone_of_ge hs hge
    have hbdd : BddBelow (range (E.path k₀)) :=
      ⟨kstar, by rintro _ ⟨t, rfl⟩; exact E.le_path_of_ge hs hge t⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    set L := ⨅ t, E.path k₀ t
    have hL : 0 < L := hs.1.trans_le (le_ciInf fun t => E.le_path_of_ge hs hge t)
    have : L = kstar := (IsSteadyState.unique E ⟨hL, E.next_eq_of_tendsto hL hlim⟩ hs)
    rwa [this] at hlim

/-- The headline result in one statement: a unique steady state exists, and
every path starting from positive capital converges to it. -/
theorem exists_globally_stable_steadyState :
    ∃ kstar, E.IsSteadyState kstar ∧ (∀ k, E.IsSteadyState k → k = kstar) ∧
      ∀ k₀, 0 < k₀ → Tendsto (E.path k₀) atTop (𝓝 kstar) := by
  obtain ⟨kstar, hs, huniq⟩ := E.existsUnique_steadyState
  exact ⟨kstar, hs, huniq, fun _ hk₀ => E.tendsto_path hs hk₀⟩

/-- **Output per worker converges too:** `y_t = f(k_t) → f(k*) = y*`. -/
theorem tendsto_output {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀) :
    Tendsto (fun t => E.f (E.path k₀ t)) atTop (𝓝 (E.f kstar)) :=
  ((E.hf.continuousOn kstar hs.1).continuousAt (Ioi_mem_nhds hs.1)).tendsto.comp
    (E.tendsto_path hs hk₀)

/-- The growth rate of capital per worker, `(k_{t+1} − k_t) / k_t`, as a
function of the current `k`. -/
def growthRate (k : ℝ) : ℝ := (E.next k - k) / k

theorem growthRate_eq {k : ℝ} (hk : 0 < k) :
    E.growthRate k = (E.s * (E.f k / k) - (E.n + E.δ)) / (1 + E.n) := by
  unfold growthRate
  rw [E.next_sub_self hk]
  field_simp

/-- **Conditional convergence:** the growth rate of capital per worker is
strictly decreasing in `k`. Among economies with the same parameters,
poorer ones grow faster (Barro and Sala-i-Martin §1.2.9). -/
theorem growthRate_strictAntiOn : StrictAntiOn E.growthRate (Ioi 0) := by
  intro a ha b hb hab
  rw [E.growthRate_eq ha, E.growthRate_eq hb]
  have := mul_lt_mul_of_pos_left (E.hf.avg_strictAntiOn ha hb hab) E.hs_pos
  exact div_lt_div_of_pos_right (by linarith) E.one_add_n_pos

/-- **All fixed points on `[0, ∞)`:** the law of motion has exactly two
nonnegative fixed points, the trivial one `0` and the steady state `k*`. -/
theorem fixedPoint_iff {kstar k : ℝ} (hs : E.IsSteadyState kstar) (hk : 0 ≤ k) :
    E.next k = k ↔ k = 0 ∨ k = kstar := by
  constructor
  · intro h
    rcases hk.eq_or_lt with h0 | h0
    · exact Or.inl h0.symm
    · exact Or.inr (IsSteadyState.unique E ⟨h0, h⟩ hs)
  · rintro (rfl | rfl)
    · exact E.next_zero
    · exact hs.2

/-! ## Comparative statics (Acemoglu Prop. 2.3) -/

/-- At a steady state, the average product equals `(n + δ) / s`. -/
theorem avg_eq_of_isSteadyState {k : ℝ} (hs : E.IsSteadyState k) :
    E.f k / k = (E.n + E.δ) / E.s := by
  rw [eq_div_iff E.hs_pos.ne', mul_comm]
  exact (E.next_eq_self_iff hs.1).1 hs.2

/-- Two economies with the same technology: the one with the lower effective
break-even ratio `(n + δ) / s` has the higher steady-state capital. -/
theorem steadyState_lt_of_ratio_lt {E₁ E₂ : Economy} (hf : E₁.f = E₂.f) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂)
    (h : (E₂.n + E₂.δ) / E₂.s < (E₁.n + E₁.δ) / E₁.s) : k₁ < k₂ := by
  by_contra hle
  push Not at hle
  have := E₁.hf.avg_strictAntiOn.antitoneOn h₂.1 h₁.1 hle
  rw [E₁.avg_eq_of_isSteadyState h₁, hf, E₂.avg_eq_of_isSteadyState h₂] at this
  linarith

/-- **A higher saving rate raises steady-state capital** (Acemoglu Prop. 2.3). -/
theorem steadyState_strictMono_s {E₁ E₂ : Economy} (hf : E₁.f = E₂.f) (hn : E₁.n = E₂.n)
    (hδ : E₁.δ = E₂.δ) (hs : E₁.s < E₂.s) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂) : k₁ < k₂ := by
  refine steadyState_lt_of_ratio_lt hf h₁ h₂ ?_
  rw [hn, hδ]
  exact div_lt_div_of_pos_left E₂.hnδ E₁.hs_pos hs

/-- **Faster population growth lowers steady-state capital.** -/
theorem steadyState_strictAnti_n {E₁ E₂ : Economy} (hf : E₁.f = E₂.f) (hs : E₁.s = E₂.s)
    (hδ : E₁.δ = E₂.δ) (hn : E₁.n < E₂.n) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂) : k₂ < k₁ := by
  refine steadyState_lt_of_ratio_lt hf.symm h₂ h₁ ?_
  rw [hs, hδ]
  exact div_lt_div_of_pos_right (by linarith) E₂.hs_pos

/-- **Faster depreciation lowers steady-state capital.** -/
theorem steadyState_strictAnti_δ {E₁ E₂ : Economy} (hf : E₁.f = E₂.f) (hs : E₁.s = E₂.s)
    (hn : E₁.n = E₂.n) (hδ : E₁.δ < E₂.δ) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂) : k₂ < k₁ := by
  refine steadyState_lt_of_ratio_lt hf.symm h₂ h₁ ?_
  rw [hs, hn]
  exact div_lt_div_of_pos_right (by linarith) E₂.hs_pos

end Economy

/-! ## Cobb–Douglas: non-vacuity witness and closed form -/

/-- Cobb–Douglas in intensive form, `f k = k^α`, is neoclassical for
`0 < α < 1`. This shows the hypotheses of `NeoclassicalProduction` can be met
(they are not vacuous). -/
theorem cobbDouglas_neoclassical {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    NeoclassicalProduction (fun k => k ^ α) := by
  -- On `k > 0`, the average product is `k^(α - 1)`.
  have avg : ∀ k : ℝ, 0 < k → k ^ α / k = k ^ (α - 1) := fun k hk =>
    (Real.rpow_sub_one hk.ne' α).symm
  refine ⟨Real.zero_rpow hα₀.ne',
    (Real.continuousAt_rpow_const 0 α (Or.inr hα₀.le)).continuousWithinAt, ?_,
    Real.strictConcaveOn_rpow hα₀ hα₁, ?_, ?_⟩
  · intro a ha b _ hab
    exact Real.rpow_le_rpow (mem_Ici.1 ha) hab hα₀.le
  · refine (tendsto_rpow_neg_nhdsGT_zero (by linarith : α - 1 < 0)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with k hk using (avg k hk).symm
  · have := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)
    rw [neg_sub] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk using (avg k hk).symm

/-- A Cobb–Douglas Solow economy with share `α` and parameters `s, δ, n`. -/
def cobbDouglas (α s δ n : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hn : -1 < n) (hnδ : 0 < n + δ) : Economy where
  f := fun k => k ^ α
  s := s
  δ := δ
  n := n
  hf := cobbDouglas_neoclassical hα₀ hα₁
  hs_pos := hs₀
  hs_le_one := hs₁
  hδ_nonneg := hδ₀
  hδ_le_one := hδ₁
  hn := hn
  hnδ := hnδ

/-- **Unit test: the Cobb–Douglas steady state has the textbook closed form**
`k* = (s / (n + δ))^{1/(1−α)}`. Stated for *any* Solow economy whose
production function is `k ↦ k^α`. -/
theorem cobbDouglas_steadyState (E : Economy) {α : ℝ} (hα₁ : α < 1)
    (hf : E.f = fun k => k ^ α) :
    E.IsSteadyState ((E.s / (E.n + E.δ)) ^ (1 / (1 - α))) := by
  have hx : 0 < E.s / (E.n + E.δ) := div_pos E.hs_pos E.hnδ
  have hk : 0 < (E.s / (E.n + E.δ)) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hx _
  refine ⟨hk, (E.next_eq_self_iff hk).2 ?_⟩
  rw [hf]
  dsimp only
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [← Real.rpow_sub_one hk.ne', ← Real.rpow_mul hx.le,
    show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring, Real.rpow_neg_one, inv_div]
  have := E.hnδ.ne'
  have := E.hs_pos.ne'
  field_simp

/-- And so, in a Cobb–Douglas economy, every path from `k₀ > 0` converges to
`(s / (n + δ))^{1/(1−α)}`. -/
theorem cobbDouglas_tendsto (E : Economy) {α : ℝ} (hα₁ : α < 1)
    (hf : E.f = fun k => k ^ α) {k₀ : ℝ} (hk₀ : 0 < k₀) :
    Tendsto (E.path k₀) atTop (𝓝 ((E.s / (E.n + E.δ)) ^ (1 / (1 - α)))) :=
  E.tendsto_path (cobbDouglas_steadyState E hα₁ hf) hk₀

/-- A concrete calibrated economy (`α = 1/3`, `s = 1/5`, `δ = 1/10`, `n = 1/100`)
satisfies every hypothesis, and its steady state is `(20/11)^{3/2}`. -/
example : (cobbDouglas (1 / 3) (1 / 5) (1 / 10) (1 / 100) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).IsSteadyState ((20 / 11) ^ (3 / 2 : ℝ)) := by
  have := cobbDouglas_steadyState (cobbDouglas (1 / 3) (1 / 5) (1 / 10) (1 / 100) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)) (α := 1 / 3) (by norm_num) rfl
  convert this using 2 <;> simp [cobbDouglas] <;> norm_num

end Solow
end Econ

end
