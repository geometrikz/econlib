/-
# Exchange economies, Pareto optimality, Walrasian equilibrium, the core,
# and the First Welfare Theorem

MWG ch. 15 (§15.B), §16.B–16.C, §18.B. Blueprint: Parsert & Kaliszyk,
*Microeconomics and the First Welfare Theorem* (Isabelle AFP, 2017).

**The economics.** A *pure exchange economy* has finitely many consumers
`a : α` and finitely many goods `i : ι`. Consumer `a` has a preference `≿ₐ` on
bundles in `ℝ^ι₊` and an endowment `ωₐ ≥ 0`. Nothing is produced: goods are
only reallocated.

* An **allocation** assigns a bundle `xₐ` to every consumer. It is
  **feasible** if every bundle is nonnegative and the bundles add up to the
  total endowment, `∑ₐ xₐ = ω̄` (MWG Def. 15.B.1 and 16.B.1 with no firms).
* `y` **Pareto dominates** `x` if everybody weakly prefers `y` and somebody
  strictly prefers it. A feasible allocation is **Pareto optimal** if no
  feasible allocation Pareto dominates it (MWG Def. 16.B.2).
* `(p, x)` is a **Walrasian equilibrium** if every consumer's bundle is a
  best bundle in their budget set at prices `p` and wealth `p · ωₐ`, and
  markets clear, `∑ₐ xₐ = ω̄` (MWG Def. 15.B.1, 16.B.3).
* A nonempty coalition `S` **blocks** `x` if its members, trading only their
  own endowments, can make *every* member strictly better off. The **core** is
  the set of feasible allocations no coalition blocks (MWG Def. 18.B.1–18.B.2).

Results:
1. **First Welfare Theorem** (MWG Prop. 16.C.1): with rational, locally
   nonsatiated preferences, every Walrasian equilibrium allocation is Pareto
   optimal.
2. **Walrasian equilibria are in the core** (MWG Prop. 18.B.2). This needs *no*
   assumption on preferences, because blocking asks for strict improvement for
   every member.
3. Core allocations are **individually rational** and **weakly Pareto
   optimal** (the singleton and grand coalitions cannot block).

**The Lean.** We reuse `cost`, `budgetSet`, `demand` and `LocallyNonsatiated`
from the consumer files, so a consumer in an economy is literally the consumer
of `Consumer/Demand.lean` with wealth `p · ωₐ`. Agents are indexed by an
arbitrary finite type `α`, and aggregates are `Finset` sums. When the library's
`Core` layer (PLAN §7.1) arrives, these sums become integrals against a
counting measure, which is what lets the same definitions later describe
continuum economies.
-/
module

public import EconLean.Consumer.Demand

@[expose] public section

namespace Econ

open Finset

variable {α ι : Type*}

/-- A **pure exchange economy** with consumers `α` and goods `ι`: each consumer
`a` has a preference `pref a` on bundles and a nonnegative endowment `endow a`.
-/
structure ExchangeEconomy (α ι : Type*) where
  /-- Consumer `a`'s weak preference: `pref a x y` reads "a finds x at least as
  good as y". -/
  pref : α → (ι → ℝ) → (ι → ℝ) → Prop
  /-- Consumer `a`'s endowment `ωₐ`. -/
  endow : α → ι → ℝ
  /-- Endowments lie in the consumption set `ℝ^ι₊`. -/
  endow_nonneg : ∀ a, 0 ≤ endow a

/-- An allocation gives each consumer a bundle. (Just a function; feasibility
is a separate predicate.) -/
abbrev Allocation (α ι : Type*) := α → ι → ℝ

/-! ### Cost of a sum of bundles

`cost p` is linear, so the value of a sum of bundles is the sum of the values.
This is the one piece of algebra that both welfare theorems rest on. -/

section CostSum

variable [Fintype ι]

/-- `p · (∑ₐ xₐ) = ∑ₐ p · xₐ`. -/
theorem cost_sum (p : ι → ℝ) (s : Finset α) (x : α → ι → ℝ) :
    cost p (∑ a ∈ s, x a) = ∑ a ∈ s, cost p (x a) := by
  -- Unfold `cost`, evaluate the sum of functions pointwise, then swap the two
  -- finite sums (`Finset.sum_comm`).
  simp only [cost, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

end CostSum

namespace ExchangeEconomy

variable [Fintype α] [Fintype ι] (E : ExchangeEconomy α ι)

/-- The aggregate endowment `ω̄ = ∑ₐ ωₐ`. -/
def totalEndowment : ι → ℝ := ∑ a, E.endow a

/-- Consumer `a`'s wealth at prices `p`: the market value of their endowment. -/
def wealth (p : ι → ℝ) (a : α) : ℝ := cost p (E.endow a)

/-- A **feasible allocation**: nonnegative bundles that exactly exhaust the
aggregate endowment (MWG Def. 15.B.1). -/
def Feasible (x : Allocation α ι) : Prop :=
  (∀ a, 0 ≤ x a) ∧ ∑ a, x a = E.totalEndowment

/-- `y` **Pareto dominates** `x`: everybody weakly prefers `y`, somebody
strictly. -/
def ParetoDominates (y x : Allocation α ι) : Prop :=
  (∀ a, E.pref a (y a) (x a)) ∧ ∃ a, P (E.pref a) (y a) (x a)

/-- A **Pareto optimal** allocation is feasible and not Pareto dominated by any
feasible allocation (MWG Def. 16.B.2). -/
def ParetoOptimal (x : Allocation α ι) : Prop :=
  E.Feasible x ∧ ∀ y, E.Feasible y → ¬ E.ParetoDominates y x

/-- A **weakly Pareto optimal** allocation is feasible and no feasible
allocation makes *everybody* strictly better off. -/
def WeaklyParetoOptimal (x : Allocation α ι) : Prop :=
  E.Feasible x ∧ ∀ y, E.Feasible y → ¬ ∀ a, P (E.pref a) (y a) (x a)

/-- `(p, x)` is a **Walrasian equilibrium** (MWG Def. 15.B.1, 16.B.3):
(i) each consumer's bundle is in their Walrasian demand at prices `p` and
wealth `p · ωₐ`; (ii) markets clear. -/
def IsWalrasianEquilibrium (p : ι → ℝ) (x : Allocation α ι) : Prop :=
  (∀ a, x a ∈ demand (E.pref a) p (E.wealth p a)) ∧ ∑ a, x a = E.totalEndowment

/-- Coalition `S` **blocks** `x` (MWG Def. 18.B.1): `S` is nonempty and there
are bundles `yₐ ≥ 0` for its members, using only their own endowments
(`∑_{a∈S} yₐ = ∑_{a∈S} ωₐ`), that every member strictly prefers to `xₐ`. -/
def Blocks (S : Finset α) (x : Allocation α ι) : Prop :=
  S.Nonempty ∧ ∃ y : Allocation α ι, (∀ a ∈ S, 0 ≤ y a) ∧
    ∑ a ∈ S, y a = ∑ a ∈ S, E.endow a ∧ ∀ a ∈ S, P (E.pref a) (y a) (x a)

/-- The **core** (MWG Def. 18.B.2): feasible allocations that no coalition
blocks. -/
def InCore (x : Allocation α ι) : Prop :=
  E.Feasible x ∧ ∀ S, ¬ E.Blocks S x

/-- An allocation is **individually rational** if nobody prefers their own
endowment to it. -/
def IndividuallyRational (x : Allocation α ι) : Prop :=
  ∀ a, E.pref a (x a) (E.endow a)

variable {E}

/-! ### Basic facts -/

omit [Fintype ι] in
/-- The endowment allocation itself is feasible. -/
theorem feasible_endow : E.Feasible E.endow :=
  ⟨E.endow_nonneg, rfl⟩

/-- A Walrasian equilibrium allocation is feasible (demanded bundles are
nonnegative because they lie in a budget set). -/
theorem IsWalrasianEquilibrium.feasible {p : ι → ℝ} {x : Allocation α ι}
    (h : E.IsWalrasianEquilibrium p x) : E.Feasible x :=
  ⟨fun a => (h.1 a).1.1, h.2⟩

/-- In a feasible allocation, the total value of the bundles equals the total
value of the endowments: `∑ₐ p · xₐ = ∑ₐ p · ωₐ`. -/
theorem Feasible.sum_cost {x : Allocation α ι} (hx : E.Feasible x) (p : ι → ℝ) :
    ∑ a, cost p (x a) = ∑ a, E.wealth p a := by
  -- Both sides are `p · ω̄` by linearity of `cost`.
  rw [← cost_sum, hx.2, totalEndowment, cost_sum]
  rfl

omit [Fintype ι] in
/-- Pareto optimality implies weak Pareto optimality (when there is at least
one consumer). -/
theorem ParetoOptimal.weaklyParetoOptimal [Nonempty α] {x : Allocation α ι}
    (hx : E.ParetoOptimal x) : E.WeaklyParetoOptimal x := by
  refine ⟨hx.1, fun y hy hall => hx.2 y hy ⟨fun a => (hall a).1, ?_⟩⟩
  obtain ⟨a⟩ := ‹Nonempty α›
  exact ⟨a, hall a⟩

/-! ### Two consumer-level facts behind both welfare theorems

If `x` is demanded at `(p, w)`, then
* any bundle strictly better than `x` costs more than `w` (no assumptions), and
* under local nonsatiation, any bundle at least as good as `x` costs at least
  `w` (MWG Lemma 16.C.1). -/

/-- A bundle strictly preferred to a demanded bundle is unaffordable. -/
theorem cost_gt_of_mem_demand {R : (ι → ℝ) → (ι → ℝ) → Prop} {p : ι → ℝ} {w : ℝ}
    {x y : ι → ℝ} (hx : x ∈ demand R p w) (hy : 0 ≤ y) (hyx : P R y x) :
    w < cost p y := by
  -- If `y` were affordable, optimality of `x` would give `x ≿ y`, contradicting `y ≻ x`.
  by_contra hle
  exact hyx.2 (hx.2 y ⟨hy, not_lt.1 hle⟩)

/-- **MWG Lemma 16.C.1.** Under local nonsatiation, a bundle at least as good
as a demanded bundle costs at least the consumer's wealth. -/
theorem cost_ge_of_mem_demand {R : (ι → ℝ) → (ι → ℝ) → Prop} (hR : Rational R)
    (hlns : LocallyNonsatiated R) {p : ι → ℝ} {w : ℝ} {x y : ι → ℝ}
    (hx : x ∈ demand R p w) (hy : 0 ≤ y) (hyx : R y x) : w ≤ cost p y := by
  by_contra hlt
  -- If `y` were strictly cheaper than `w`, local nonsatiation would give an
  -- affordable `z ≻ y ≿ x`, so `z ≻ x`, contradicting optimality of `x`.
  obtain ⟨z, hzB, hzy⟩ := exists_better_affordable hlns hy (not_le.1 hlt)
  have hzx : P R z x := P_of_P_of_R (R := R) (fun h₁ h₂ => hR.trans h₁ h₂) hzy hyx
  exact hzx.2 (hx.2 z hzB)

/-! ### 1. The First Welfare Theorem (MWG Prop. 16.C.1) -/

/-- **First Fundamental Theorem of Welfare Economics** (MWG Prop. 16.C.1).
If preferences are rational and locally nonsatiated, any Walrasian equilibrium
allocation is Pareto optimal.

Proof: suppose a feasible `y` Pareto dominates `x`. Each `yₐ` is at least as
good as `xₐ`, so costs at least `p · ωₐ` (Lemma 16.C.1); the strictly better
`y_b` costs strictly more. Summing, `p · ∑ yₐ > p · ω̄`, but feasibility says
`∑ yₐ = ω̄`. -/
theorem first_welfare_theorem (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {x : Allocation α ι}
    (heq : E.IsWalrasianEquilibrium p x) : E.ParetoOptimal x := by
  refine ⟨heq.feasible, fun y hy ⟨hweak, b, hb⟩ => ?_⟩
  -- Strict inequality of the sums: every term `≤`, the term for `b` is `<`.
  have hlt : ∑ a, E.wealth p a < ∑ a, cost p (y a) :=
    Finset.sum_lt_sum
      (fun a _ => cost_ge_of_mem_demand (hR a) (hlns a) (heq.1 a) (hy.1 a) (hweak a))
      ⟨b, Finset.mem_univ b, cost_gt_of_mem_demand (heq.1 b) (hy.1 b) hb⟩
  -- But feasibility of `y` makes the two sums equal.
  rw [hy.sum_cost p] at hlt
  exact lt_irrefl _ hlt

/-! ### 2. The core (MWG §18.B) -/

/-- **Walrasian equilibrium allocations are in the core** (MWG Prop. 18.B.2).
No assumption on preferences is needed.

Proof: if `S` blocks with `y`, every `yₐ` (`a ∈ S`) is strictly preferred to
`xₐ`, hence costs more than `p · ωₐ`. Summing over `S`,
`p · ∑_S yₐ > p · ∑_S ωₐ`, contradicting `∑_S yₐ = ∑_S ωₐ`. -/
theorem IsWalrasianEquilibrium.inCore {p : ι → ℝ} {x : Allocation α ι}
    (heq : E.IsWalrasianEquilibrium p x) : E.InCore x := by
  refine ⟨heq.feasible, fun S ⟨hS, y, hy0, hysum, hybetter⟩ => ?_⟩
  have hlt : ∑ a ∈ S, E.wealth p a < ∑ a ∈ S, cost p (y a) :=
    Finset.sum_lt_sum_of_nonempty hS
      (fun a ha => cost_gt_of_mem_demand (heq.1 a) (hy0 a ha) (hybetter a ha))
  -- `∑_S p · yₐ = p · ∑_S yₐ = p · ∑_S ωₐ = ∑_S p · ωₐ`.
  rw [← cost_sum, hysum, cost_sum] at hlt
  exact lt_irrefl _ hlt

omit [Fintype ι] in
/-- **Core allocations are individually rational.** Otherwise consumer `a`
alone (the singleton coalition) blocks by consuming their endowment. Needs
completeness to turn "not ωₐ ≻ xₐ" into "xₐ ≿ ωₐ". -/
theorem InCore.individuallyRational (hR : ∀ a, Rational (E.pref a))
    {x : Allocation α ι} (hx : E.InCore x) : E.IndividuallyRational x := by
  intro a
  by_contra hnot
  -- `ωₐ ≻ xₐ`, because `¬ (xₐ ≿ ωₐ)` and preferences are complete.
  have hstrict : P (E.pref a) (E.endow a) (x a) := ((hR a).P_iff_not _ _).2 hnot
  classical
  refine hx.2 {a} ⟨singleton_nonempty a, E.endow, fun b _ => E.endow_nonneg b, rfl, ?_⟩
  intro b hb
  rw [Finset.mem_singleton.1 hb]
  exact hstrict

omit [Fintype ι] in
/-- **Core allocations are weakly Pareto optimal.** Otherwise the grand
coalition blocks. -/
theorem InCore.weaklyParetoOptimal [Nonempty α] {x : Allocation α ι}
    (hx : E.InCore x) : E.WeaklyParetoOptimal x := by
  refine ⟨hx.1, fun y hy hall => hx.2 Finset.univ
    ⟨Finset.univ_nonempty, y, fun a _ => hy.1 a, ?_, fun a _ => hall a⟩⟩
  -- The grand coalition's resources are the whole endowment.
  rw [hy.2]
  rfl

/-- **Walrasian equilibrium allocations are individually rational**: each
consumer's endowment is affordable at their own wealth `p · ωₐ`, so the
demanded bundle is at least as good. (No assumption on preferences.) -/
theorem IsWalrasianEquilibrium.individuallyRational {p : ι → ℝ} {x : Allocation α ι}
    (heq : E.IsWalrasianEquilibrium p x) : E.IndividuallyRational x :=
  fun a => (heq.1 a).2 (E.endow a) ⟨E.endow_nonneg a, le_rfl⟩

end ExchangeEconomy

end Econ
