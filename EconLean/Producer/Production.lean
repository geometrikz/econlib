/-
# Production sets, profit maximization and supply

MWG §5.B–5.C (Props. 5.B.1–5.B.2, 5.C.1, Hotelling's lemma).

**The economics.** A firm is described by its *production set*
`Y ⊆ ℝᴸ` of feasible *net output* vectors: `yᵢ > 0` means good `i` is
produced, `yᵢ < 0` that it is used as an input. Facing prices `p`, the firm
chooses `y ∈ Y` to maximize profit `p · y`. This gives
* the **profit function** `π(p) = sup { p · y | y ∈ Y }`, and
* the **supply correspondence** `y(p) = argmax { p · y | y ∈ Y }`.

The main results here (MWG Prop. 5.C.1):
* `y(·)` is homogeneous of degree zero and `π` of degree one;
* `π` is convex in `p`;
* `y(p)` is convex when `Y` is;
* the **law of supply** `(p - p') · (y - y') ≥ 0`;
* **Hotelling's lemma** `∇π(p) = y(p)`, with uniqueness of supply as a
  corollary when `π` is differentiable;
* for compact `Y`, Berge's maximum theorem gives continuity of `π` and upper
  hemicontinuity of supply.

**Shared abstractions (PLAN §7.1).** Profit maximization is *literally* an
instance of the generic optimization problem of `Foundations/Maximum.lean`:
`profit Y = maxValue (fun p y => p · y) (fun _ => Y)` and
`supply Y = argmax …`. So Berge's theorem applies with no extra work, and
later general-equilibrium code can treat firms and consumers alike as
"agents with a choice correspondence".

**The Lean.** `cost p y = ∑ᵢ pᵢ yᵢ` (from `Consumer/Budget.lean`) is the
value of the net-output vector `y` at prices `p`; for a firm this *is* its
profit. Like the consumer's `expenditure`, `profit` is a real `sSup`, so it is
a junk value (0) when profits are unbounded. Theorems that need a genuine
supremum assume either that the maximum is attained (`y ∈ supply Y p`) or
that profits are bounded above (`BddAbove`), exactly as MWG implicitly does.
MWG's `π(p) = +∞` for unbounded profits becomes `0` here, so
`profit_smul` (true unconditionally) is only `0 = α · 0` off `profitDomain`.
-/
module

public import EconLean.Consumer.Envelope
public import EconLean.Foundations.Maximum
public import Mathlib.Basic.Real.Pointwise

@[expose] public section

namespace Econ

open Filter Topology Set

variable {ι : Type*}

/-! ### Properties of production sets (MWG §5.B) -/

/-- **Possibility of inaction**: the firm may shut down, `0 ∈ Y`. -/
def PossibilityOfInaction (Y : Set (ι → ℝ)) : Prop := (0 : ι → ℝ) ∈ Y

/-- **Free disposal**: if `y` is feasible, so is anything that uses at least
as much of every input and produces no more of every output. -/
def FreeDisposal (Y : Set (ι → ℝ)) : Prop := ∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y

/-- **No free lunch**: nothing can be produced from nothing, `Y ∩ ℝᴸ₊ ⊆ {0}`. -/
def NoFreeLunch (Y : Set (ι → ℝ)) : Prop := ∀ y ∈ Y, 0 ≤ y → y = 0

/-- **Irreversibility**: `y ∈ Y` and `y ≠ 0` imply `-y ∉ Y`. -/
def Irreversible (Y : Set (ι → ℝ)) : Prop := ∀ y ∈ Y, -y ∈ Y → y = 0

/-- **Nonincreasing returns to scale**: feasible plans can be scaled down. -/
def NonincreasingReturns (Y : Set (ι → ℝ)) : Prop :=
  ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α ≤ 1 → α • y ∈ Y

/-- **Nondecreasing returns to scale**: feasible plans can be scaled up. -/
def NondecreasingReturns (Y : Set (ι → ℝ)) : Prop :=
  ∀ y ∈ Y, ∀ α : ℝ, 1 ≤ α → α • y ∈ Y

/-- **Constant returns to scale**: `Y` is a cone. -/
def ConstantReturns (Y : Set (ι → ℝ)) : Prop := ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y

/-- **Additivity** (free entry): `y, y' ∈ Y ⟹ y + y' ∈ Y`. -/
def Additive (Y : Set (ι → ℝ)) : Prop := ∀ y ∈ Y, ∀ y' ∈ Y, y + y' ∈ Y

/-- A convex production set containing `0` has nonincreasing returns: `α y`
is the convex combination `α y + (1 - α) 0`. (MWG §5.B, property (vii)). -/
theorem NonincreasingReturns.of_convex {Y : Set (ι → ℝ)} (hY : Convex ℝ Y)
    (h0 : PossibilityOfInaction Y) : NonincreasingReturns Y := by
  intro y hy α hα0 hα1
  have := hY hy h0 hα0 (sub_nonneg.2 hα1) (by ring)
  simpa using this

/-- CRS is nonincreasing and nondecreasing returns together. -/
theorem constantReturns_iff (Y : Set (ι → ℝ)) :
    ConstantReturns Y ↔ NonincreasingReturns Y ∧ NondecreasingReturns Y := by
  refine ⟨fun h => ⟨fun y hy α hα _ => h y hy α hα,
    fun y hy α hα => h y hy α (zero_le_one.trans hα)⟩, fun ⟨hn, hd⟩ y hy α hα => ?_⟩
  rcases le_total α 1 with h | h
  · exact hn y hy α hα h
  · exact hd y hy α h

/-- Repeated addition stays in an additive set. -/
theorem Additive.nsmul_mem {Y : Set (ι → ℝ)} (hA : Additive Y) {y : ι → ℝ} (hy : y ∈ Y) :
    ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) • y ∈ Y
  | 0 => by simpa using hy
  | n + 1 => by
    have h := hA _ (hA.nsmul_mem hy n) y hy
    convert h using 1
    push_cast
    rw [add_smul, one_smul]

/-- **Additivity + nonincreasing returns ⟹ constant returns and convexity**
(MWG Exercise 5.B.4 / the remark after property (viii)). A production set
that allows free entry and scaling down is a convex cone. -/
theorem Additive.constantReturns_and_convex {Y : Set (ι → ℝ)} (hA : Additive Y)
    (hN : NonincreasingReturns Y) : ConstantReturns Y ∧ Convex ℝ Y := by
  have hcrs : ConstantReturns Y := by
    intro y hy α hα
    -- Write `α = (n+1) β` with `β ∈ [0, 1]` and `n + 1 = ⌈α⌉₊ + 1`.
    set n := ⌈α⌉₊
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hβ0 : 0 ≤ α / ((n + 1 : ℕ) : ℝ) := div_nonneg hα hn.le
    have hβ1 : α / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      push_cast
      linarith [Nat.le_ceil α]
    have h := hA.nsmul_mem (hN y hy _ hβ0 hβ1) n
    rwa [smul_smul, mul_div_cancel₀ _ hn.ne'] at h
  refine ⟨hcrs, ?_⟩
  intro y hy y' hy' a b ha hb _
  exact hA _ (hcrs y hy a ha) _ (hcrs y' hy' b hb)

variable [Fintype ι]

/-! ### Profit and supply as an instance of the generic maximization problem -/

/-- The **profit function** `π(p) = sup { p · y | y ∈ Y }` (MWG Def. 5.C.1).
It is the value function of the generic problem in `Foundations/Maximum.lean`
with objective `(p, y) ↦ p · y` and constant feasible set `Y`. -/
noncomputable def profit (Y : Set (ι → ℝ)) (p : ι → ℝ) : ℝ :=
  maxValue (fun p y => cost p y) (fun _ => Y) p

/-- The **supply correspondence** `y(p)`: the profit-maximizing plans. -/
def supply (Y : Set (ι → ℝ)) (p : ι → ℝ) : Set (ι → ℝ) :=
  argmax (fun p y => cost p y) (fun _ => Y) p

variable {Y : Set (ι → ℝ)}

theorem mem_supply {p y : ι → ℝ} :
    y ∈ supply Y p ↔ y ∈ Y ∧ ∀ y' ∈ Y, cost p y' ≤ cost p y := Iff.rfl

theorem profit_def (p : ι → ℝ) : profit Y p = sSup ((fun y => cost p y) '' Y) := rfl

/-- At a supplied plan, profit equals its value: `π(p) = p · y`. -/
theorem profit_eq {p y : ι → ℝ} (hy : y ∈ supply Y p) : profit Y p = cost p y :=
  IsGreatest.csSup_eq ⟨mem_image_of_mem _ hy.1, by rintro _ ⟨y', hy', rfl⟩; exact hy.2 y' hy'⟩

/-- When profits are bounded above, every feasible plan earns at most `π(p)`. -/
theorem cost_le_profit {p y : ι → ℝ} (hb : BddAbove ((fun y => cost p y) '' Y))
    (hy : y ∈ Y) : cost p y ≤ profit Y p :=
  le_csSup hb (mem_image_of_mem _ hy)

/-- With the possibility of inaction and bounded profits, `π(p) ≥ 0`. -/
theorem profit_nonneg {p : ι → ℝ} (h0 : PossibilityOfInaction Y)
    (hb : BddAbove ((fun y => cost p y) '' Y)) : 0 ≤ profit Y p := by
  have := cost_le_profit hb h0
  simpa [cost] using this

/-- **Supply is homogeneous of degree zero** (MWG Prop. 5.C.1 (ii)). -/
theorem supply_smul {α : ℝ} (hα : 0 < α) (p : ι → ℝ) : supply Y (α • p) = supply Y p := by
  ext y
  simp only [mem_supply, cost_smul_left, mul_le_mul_iff_right₀ hα]

/-- **Profit is homogeneous of degree one** (MWG Prop. 5.C.1 (i)). This holds
with no boundedness assumption: both sides are junk-consistent. -/
theorem profit_smul {α : ℝ} (hα : 0 ≤ α) (p : ι → ℝ) :
    profit Y (α • p) = α * profit Y p := by
  rw [profit_def, profit_def, ← smul_eq_mul, ← Real.sSup_smul_of_nonneg hα, ← image_smul,
    image_image]
  simp only [cost_smul_left, smul_eq_mul]

/-- Prices at which profits are bounded above (where `π` is finite). -/
def profitDomain (Y : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {p | BddAbove ((fun y => cost p y) '' Y)}

/-- **Profit is convex in prices** (MWG Prop. 5.C.1 (iii)), on the set of
prices where it is finite (itself convex). The intuition: at a mixed price
the firm can do no better than mixing what it earned at each price. -/
theorem convexOn_profit (hY : Y.Nonempty) : ConvexOn ℝ (profitDomain Y) (profit Y) := by
  -- Key bound: at `a p + b q`, any plan earns at most `a π(p) + b π(q)`.
  have key : ∀ {p q : ι → ℝ}, p ∈ profitDomain Y → q ∈ profitDomain Y → ∀ {a b : ℝ},
      0 ≤ a → 0 ≤ b → ∀ y ∈ Y, cost (a • p + b • q) y ≤ a * profit Y p + b * profit Y q := by
    intro p q hp hq a b ha hb y hy
    rw [cost_add_left, cost_smul_left, cost_smul_left]
    exact add_le_add (mul_le_mul_of_nonneg_left (cost_le_profit hp hy) ha)
      (mul_le_mul_of_nonneg_left (cost_le_profit hq hy) hb)
  refine ⟨fun p hp q hq a b ha hb _ => ?_, fun p hp q hq a b ha hb _ => ?_⟩
  · exact ⟨_, by rintro _ ⟨y, hy, rfl⟩; exact key hp hq ha hb y hy⟩
  · rw [smul_eq_mul, smul_eq_mul, profit_def]
    exact csSup_le (hY.image _) (by rintro _ ⟨y, hy, rfl⟩; exact key hp hq ha hb y hy)

/-- **Supply is convex when `Y` is** (MWG Prop. 5.C.1 (iv)). -/
theorem convex_supply (hY : Convex ℝ Y) (p : ι → ℝ) : Convex ℝ (supply Y p) := by
  intro y hy y' hy' a b ha hb hab
  refine ⟨hY hy.1 hy'.1 ha hb hab, fun z hz => ?_⟩
  show cost p z ≤ cost p (a • y + b • y')
  rw [cost_add_right, cost_smul_right, cost_smul_right]
  have h1 : cost p z ≤ cost p y := hy.2 z hz
  have h2 : cost p z ≤ cost p y' := hy'.2 z hz
  have hz' : cost p z = a * cost p z + b * cost p z := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Law of supply** (MWG Prop. 5.C.1 (vi), discrete form):
`(p - p') · (y - y') ≥ 0` for `y ∈ y(p)`, `y' ∈ y(p')`. Supply responds
in the direction of the price change, with no income effects. -/
theorem law_of_supply {p p' y y' : ι → ℝ} (hy : y ∈ supply Y p) (hy' : y' ∈ supply Y p') :
    0 ≤ cost (p - p') (y - y') := by
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  rw [cost_sub_left, cost_sub_right, cost_sub_right]
  linarith

/-! ### Hotelling's lemma (MWG Prop. 5.C.1 (vi)) -/

/-- **Hotelling's lemma.** Let `y ∈ y(p)` and suppose profits are bounded
above for all prices near `p`. If `π` is differentiable at `p` with
derivative `Π'`, then `Π' δ = δ · y` for every direction `δ`: the price
gradient of profit is the supply vector.

Proof: `q ↦ π(q) - q · y` is `≥ 0` near `p` and `= 0` at `p`, so it has a
local minimum there and its derivative vanishes (Fermat). -/
theorem hotelling {p y : ι → ℝ} (hy : y ∈ supply Y p)
    (hb : ∀ᶠ q in 𝓝 p, q ∈ profitDomain Y) {P' : (ι → ℝ) →L[ℝ] ℝ}
    (hP : HasFDerivAt (profit Y) P' p) : ∀ δ, P' δ = cost δ y := by
  have hmin : IsLocalMin (fun q => profit Y q - cost q y) p := by
    filter_upwards [hb] with q hq
    rw [profit_eq hy, sub_self, sub_nonneg]
    exact cost_le_profit hq hy.1
  have hc : HasFDerivAt (fun q => cost q y) (costCLM y) p :=
    (costCLM y).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun q => (costCLM_apply y q).symm)
  have hzero := hmin.hasFDerivAt_eq_zero (hP.sub hc)
  intro δ
  have := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L δ) hzero
  simp at this
  linarith

/-- Hotelling's lemma, coordinate form: `∂π/∂pⱼ (p) = yⱼ(p)`. -/
theorem hotelling_partial [DecidableEq ι] {p y : ι → ℝ} (hy : y ∈ supply Y p)
    (hb : ∀ᶠ q in 𝓝 p, q ∈ profitDomain Y) {P' : (ι → ℝ) →L[ℝ] ℝ}
    (hP : HasFDerivAt (profit Y) P' p) (j : ι) : P' (Pi.single j 1) = y j := by
  rw [hotelling hy hb hP, cost_single]

/-- If `π` is differentiable at `p`, supply at `p` is a single plan. -/
theorem supply_subsingleton [DecidableEq ι] {p : ι → ℝ}
    (hb : ∀ᶠ q in 𝓝 p, q ∈ profitDomain Y) {P' : (ι → ℝ) →L[ℝ] ℝ}
    (hP : HasFDerivAt (profit Y) P' p) : (supply Y p).Subsingleton := by
  intro y hy y' hy'
  funext j
  rw [← hotelling_partial hy hb hP j, hotelling_partial hy' hb hP j]

/-! ### Continuity from Berge's maximum theorem -/

/-- The objective `(p, y) ↦ p · y` is jointly continuous. -/
theorem continuous_profitObjective :
    Continuous (Function.uncurry fun (p y : ι → ℝ) => cost p y) := by
  unfold cost
  fun_prop

/-- **Berge for the firm.** If `Y` is nonempty and compact, then `π` is
continuous, supply is nonempty and compact-valued, and supply is upper
hemicontinuous in prices. -/
theorem berge_supply (hne : Y.Nonempty) (hK : IsCompact Y) :
    Continuous (profit Y) ∧ (∀ p, (supply Y p).Nonempty ∧ IsCompact (supply Y p)) ∧
      UpperHemicontinuous (supply Y) := by
  have h := berge_maximum_theorem (Φ := fun _ : ι → ℝ => Y) continuous_profitObjective
    ⟨UpperHemicontinuous.const, LowerHemicontinuous.const⟩ (fun _ => hne) (fun _ => hK)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-! ### Non-vacuity -/

/-- **Witness for Hotelling's hypotheses.** The free-disposal technology
`Y = {y | y ≤ ȳ}` (anything weakly below a fixed plan `ȳ`) at strictly
positive prices: `ȳ` is supplied, profits are bounded near `p`, and `π` is
differentiable (it equals `q ↦ q · ȳ` near `p`). Hotelling then gives the
expected answer `∇π(p) = ȳ`. -/
example [DecidableEq ι] (ybar p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    ybar ∈ supply (Iic ybar) p ∧ (∀ᶠ q in 𝓝 p, q ∈ profitDomain (Iic ybar)) ∧
      HasFDerivAt (profit (Iic ybar)) (costCLM ybar) p ∧
      ∀ j, costCLM ybar (Pi.single j 1) = ybar j := by
  -- For `q ≥ 0`, `ȳ` maximizes `q · y` over `y ≤ ȳ`.
  have hsup : ∀ q : ι → ℝ, (∀ i, 0 < q i) → ybar ∈ supply (Iic ybar) q := by
    intro q hq
    refine ⟨Set.mem_Iic.2 le_rfl, fun y hy => ?_⟩
    show cost q y ≤ cost q ybar
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hq i).le
  have hdom : ∀ᶠ q in 𝓝 p, q ∈ profitDomain (Iic ybar) := by
    filter_upwards [eventually_pos hp] with q hq
    exact ⟨cost q ybar, by rintro _ ⟨y, hy, rfl⟩; exact (hsup q hq).2 y hy⟩
  have hderiv : HasFDerivAt (profit (Iic ybar)) (costCLM ybar) p := by
    refine (costCLM ybar).hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [eventually_pos hp] with q hq
    rw [profit_eq (hsup q hq), costCLM_apply]
  refine ⟨hsup p hp, hdom, hderiv, fun j => ?_⟩
  rw [costCLM_apply, cost_single]

end Econ
