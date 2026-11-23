/-
# Price equilibria with transfers and the Second Welfare Theorem

MWG §16.B (Def. 16.B.4), §16.C (Prop. 16.C.1 in its "with transfers" form),
§16.D (Def. 16.D.1, Prop. 16.D.1, Prop. 16.D.2).

**The economics.** The Second Welfare Theorem is the converse of the First:
*any* Pareto optimal allocation can be reached as a competitive outcome,
provided the planner can first redistribute wealth by lump-sum transfers.
Formally, with wealth levels `wₐ` summing to the value of the aggregate
endowment:

* `(p, w, x)` is a **price equilibrium with transfers** (MWG Def. 16.B.4) if
  `x` is feasible, `∑ₐ wₐ = p · ω̄`, and any bundle a consumer strictly prefers
  to `xₐ` costs more than `wₐ`;
* it is a **price quasi-equilibrium with transfers** (MWG Def. 16.D.1) if
  instead such a bundle costs *at least* `wₐ`.

Results:
1. **First Welfare Theorem with transfers** (MWG Prop. 16.C.1, the version MWG
   actually states): under local nonsatiation a price equilibrium with
   transfers is Pareto optimal. Walrasian equilibrium is the special case
   `wₐ = p · ωₐ`.
2. **Second Welfare Theorem** (MWG Prop. 16.D.1): with rational, convex and
   locally nonsatiated preferences, every Pareto optimal allocation `x` is
   supported by nonzero prices `p` as a price quasi-equilibrium with transfers
   `wₐ = p · xₐ`. The prices come from the supporting hyperplane theorem
   applied to the set of aggregate bundles that would make everyone better off.
3. **Quasi-equilibrium ⇒ equilibrium** (MWG Prop. 16.D.2): if preferences are
   continuous and the consumer has a *cheaper point* (a bundle costing less
   than `wₐ`), then "costs at least" upgrades to "costs more".
4. **Textbook Second Welfare Theorem**: with strongly monotone, continuous,
   convex preferences and an interior Pareto optimum `x ≫ 0`, there are
   nonnegative, nonzero prices at which every `xₐ` is the consumer's Walrasian
   demand with wealth `p · xₐ`.
-/
module

public import EconLean.GE.Exchange
public import EconLean.Foundations.SupportingHyperplane

@[expose] public section

namespace Econ

open Finset

variable {α ι : Type*}

/-! ### Preference continuity (MWG Def. 3.C.1) -/

/-- `R` is **continuous** on the consumption set `ℝ^ι₊`: for every `x ≥ 0`, the
upper contour set `{y ≥ 0 | y ≿ x}` and lower contour set `{y ≥ 0 | x ≿ y}`
are closed. (For rational preferences this is equivalent to MWG's sequential
Def. 3.C.1; since `ℝ^ι₊` is closed, "closed in `ℝ^ι₊`" equals "closed".) -/
def ContinuousPref [Fintype ι] (R : (ι → ℝ) → (ι → ℝ) → Prop) : Prop :=
  ∀ x, 0 ≤ x → IsClosed {y : ι → ℝ | 0 ≤ y ∧ R y x} ∧ IsClosed {y : ι → ℝ | 0 ≤ y ∧ R x y}

/-- Preferences represented by a continuous utility function are continuous. -/
theorem continuousPref_prefOf [Fintype ι] {u : (ι → ℝ) → ℝ} (hu : Continuous u) :
    ContinuousPref (prefOf u) := fun _ _ =>
  ⟨(isClosed_le continuous_const continuous_id).inter (isClosed_le continuous_const hu),
   (isClosed_le continuous_const continuous_id).inter (isClosed_le hu continuous_const)⟩

/-- With rational and convex preferences, the **strict** upper contour set
`{y ≥ 0 | y ≻ x}` is convex. (Convexity of preferences is about *weak* upper
contour sets; completeness lets us transfer it.) -/
theorem convex_strictUpper [Fintype ι] {R : (ι → ℝ) → (ι → ℝ) → Prop} (hR : Rational R)
    (hconv : ConvexPref R) (x : ι → ℝ) : Convex ℝ {y | 0 ≤ y ∧ P R y x} := by
  intro y₁ h₁ y₂ h₂ s t hs ht hst
  refine ⟨add_nonneg (smul_nonneg hs h₁.1) (smul_nonneg ht h₂.1), ?_⟩
  -- Compare `y₁` and `y₂`; the mix is at least as good as the worse one,
  -- which is strictly better than `x`.
  rcases hR.complete y₁ y₂ with h12 | h21
  · have hmix : R (s • y₁ + t • y₂) y₂ :=
      (hconv y₂ h₂.1 ⟨h₁.1, h12⟩ ⟨h₂.1, hR.refl y₂⟩ hs ht hst).2
    exact P_of_R_of_P (R := R) (fun h h' => hR.trans h h') hmix h₂.2
  · have hmix : R (s • y₁ + t • y₂) y₁ :=
      (hconv y₁ h₁.1 ⟨h₁.1, hR.refl y₁⟩ ⟨h₂.1, h21⟩ hs ht hst).2
    exact P_of_R_of_P (R := R) (fun h h' => hR.trans h h') hmix h₁.2

/-- Under local nonsatiation, every `x ≥ 0` is a limit of strictly better
bundles. -/
theorem mem_closure_strictUpper [Fintype ι] {R : (ι → ℝ) → (ι → ℝ) → Prop}
    (hlns : LocallyNonsatiated R) {x : ι → ℝ} (hx : 0 ≤ x) :
    x ∈ closure {y | 0 ≤ y ∧ P R y x} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hy0, hyd, hyx⟩ := hlns x hx ε hε
  exact ⟨y, ⟨hy0, hyx⟩, by rwa [dist_comm]⟩

namespace ExchangeEconomy

variable [Fintype α] [Fintype ι] (E : ExchangeEconomy α ι)

/-- **Price equilibrium with transfers** (MWG Def. 16.B.4, exchange case):
`x` is feasible, wealth levels add up to the value of the aggregate endowment,
and anything a consumer strictly prefers to `xₐ` costs more than `wₐ`.

Documented deviation: MWG's condition (ii) also asks `xₐ` to be affordable,
`p · xₐ ≤ wₐ`. We follow the "strictly preferred ⇒ costs more" form that MWG
uses in its proofs; under rational, locally nonsatiated preferences the two
agree, because then `p · xₐ = wₐ` for every `a` (`IsPriceEquilibriumWithTransfers.cost_eq`). -/
def IsPriceEquilibriumWithTransfers (p : ι → ℝ) (w : α → ℝ) (x : Allocation α ι) :
    Prop :=
  E.Feasible x ∧ ∑ a, w a = cost p E.totalEndowment ∧
    ∀ a y, 0 ≤ y → P (E.pref a) y (x a) → w a < cost p y

/-- **Price quasi-equilibrium with transfers** (MWG Def. 16.D.1, exchange
case): as above, but strictly preferred bundles only cost *at least* `wₐ`. -/
def IsPriceQuasiEquilibriumWithTransfers (p : ι → ℝ) (w : α → ℝ)
    (x : Allocation α ι) : Prop :=
  E.Feasible x ∧ ∑ a, w a = cost p E.totalEndowment ∧
    ∀ a y, 0 ≤ y → P (E.pref a) y (x a) → w a ≤ cost p y

variable {E}

/-- A Walrasian equilibrium is a price equilibrium with transfers in which
each consumer's wealth is the value of their own endowment. -/
theorem IsWalrasianEquilibrium.isPriceEquilibriumWithTransfers {p : ι → ℝ}
    {x : Allocation α ι} (heq : E.IsWalrasianEquilibrium p x) :
    E.IsPriceEquilibriumWithTransfers p (E.wealth p) x := by
  refine ⟨heq.feasible, ?_, fun a y hy hyx => cost_gt_of_mem_demand (heq.1 a) hy hyx⟩
  simp only [wealth, totalEndowment, cost_sum]

/-- Every price equilibrium with transfers is a quasi-equilibrium. -/
theorem IsPriceEquilibriumWithTransfers.quasi {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceEquilibriumWithTransfers p w x) :
    E.IsPriceQuasiEquilibriumWithTransfers p w x :=
  ⟨h.1, h.2.1, fun a y hy hyx => (h.2.2 a y hy hyx).le⟩

/-! ### 1. First Welfare Theorem, with transfers (MWG Prop. 16.C.1) -/

/-- In a price equilibrium with transfers and locally nonsatiated, rational
preferences, any bundle at least as good as `xₐ` costs at least `wₐ`
(MWG Lemma 16.C.1). -/
theorem IsPriceEquilibriumWithTransfers.cost_ge (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceEquilibriumWithTransfers p w x) (a : α)
    {y : ι → ℝ} (hy : 0 ≤ y) (hyx : E.pref a y (x a)) : w a ≤ cost p y := by
  by_contra hlt
  -- A cheaper `y` can be improved within the cost bound by local
  -- nonsatiation, giving an affordable `z ≻ xₐ`.
  obtain ⟨z, ⟨hz0, hzc⟩, hzy⟩ := exists_better_affordable (hlns a) hy (not_le.1 hlt)
  have := h.2.2 a z hz0 (P_of_P_of_R (R := E.pref a) (fun h h' => (hR a).trans h h') hzy hyx)
  linarith

/-- **First Welfare Theorem** (MWG Prop. 16.C.1): with rational, locally
nonsatiated preferences, every price equilibrium with transfers is Pareto
optimal. -/
theorem IsPriceEquilibriumWithTransfers.paretoOptimal (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceEquilibriumWithTransfers p w x) :
    E.ParetoOptimal x := by
  refine ⟨h.1, fun y hy ⟨hweak, b, hb⟩ => ?_⟩
  have hlt : ∑ a, w a < ∑ a, cost p (y a) :=
    Finset.sum_lt_sum (fun a _ => h.cost_ge hR hlns a (hy.1 a) (hweak a))
      ⟨b, Finset.mem_univ b, h.2.2 b (y b) (hy.1 b) hb⟩
  -- Both sums equal `p · ω̄`.
  rw [h.2.1, ← cost_sum, hy.2] at hlt
  exact lt_irrefl _ hlt

/-- Under rational, locally nonsatiated preferences, every consumer spends
exactly their wealth in a price equilibrium with transfers: `p · xₐ = wₐ`. So our
definition agrees with MWG Def. 16.B.4, which also requires `p · xₐ ≤ wₐ`. -/
theorem IsPriceEquilibriumWithTransfers.cost_eq (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {w : α → ℝ}
    {x : Allocation α ι} (h : E.IsPriceEquilibriumWithTransfers p w x) (a : α) :
    cost p (x a) = w a := by
  classical
  -- Each `p · x_b ≥ w_b` (take `y = x_b` in Lemma 16.C.1), and the totals agree.
  have hge : ∀ b, w b ≤ cost p (x b) := fun b =>
    h.cost_ge hR hlns b (h.1.1 b) ((hR b).refl (x b))
  have htot : ∑ b, cost p (x b) = ∑ b, w b := by
    rw [h.2.1, ← cost_sum, h.1.2]
  have hsum0 : ∑ b, (cost p (x b) - w b) = 0 := by
    rw [Finset.sum_sub_distrib, htot, sub_self]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sub_nonneg.2 (hge b))).1 hsum0 a
    (Finset.mem_univ a)
  linarith

/-! ### 2. The Second Welfare Theorem (MWG Prop. 16.D.1) -/

/-- **Second Fundamental Theorem of Welfare Economics** (MWG Prop. 16.D.1).
If preferences are rational, convex and locally nonsatiated, then for every
Pareto optimal allocation `x` there is a nonzero price vector `p` such that
`(p, w, x)` with `wₐ = p · xₐ` is a price quasi-equilibrium with transfers.

Proof (MWG): let `Vₐ = {y ≥ 0 | y ≻ₐ xₐ}` and `V = ∑ₐ Vₐ`, the aggregate
bundles that could make everyone strictly better off. `V` is convex, and
`ω̄ ∉ V` by Pareto optimality. The supporting hyperplane theorem gives `p ≠ 0`
with `p · ω̄ ≤ p · v` on `V`. If `y ≻ₐ xₐ`, combine `y` with bundles
`y_b ≻_b x_b` arbitrarily close to `x_b` (local nonsatiation) for `b ≠ a`;
passing to the limit gives `p · ω̄ ≤ p · y + ∑_{b≠a} p · x_b`, i.e.
`p · xₐ ≤ p · y`. -/
theorem second_welfare_theorem [Nonempty ι] (hR : ∀ a, Rational (E.pref a))
    (hconv : ∀ a, ConvexPref (E.pref a)) (hlns : ∀ a, LocallyNonsatiated (E.pref a))
    {x : Allocation α ι} (hx : E.ParetoOptimal x) :
    ∃ p : ι → ℝ, p ≠ 0 ∧
      E.IsPriceQuasiEquilibriumWithTransfers p (fun a => cost p (x a)) x := by
  classical
  -- Wealth levels `p · xₐ` always add up to `p · ω̄` for feasible `x`.
  have hsum : ∀ p : ι → ℝ, ∑ a, cost p (x a) = cost p E.totalEndowment := fun p => by
    rw [← cost_sum, hx.1.2]
  rcases isEmpty_or_nonempty α with hα | hα
  · -- No consumers: any nonzero price vector works vacuously.
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨fun _ => 1, fun h => by simpa using congrFun h i, hx.1, hsum _, ?_⟩
    exact fun a => (IsEmpty.false a).elim
  obtain ⟨a₀⟩ := hα
  -- The sets `Vₐ` of strictly better bundles, and their sum `V`.
  set Vb : α → Set (ι → ℝ) := fun a => {y | 0 ≤ y ∧ P (E.pref a) y (x a)} with hVb
  set V : Set (ι → ℝ) := {z | ∃ y : Allocation α ι, (∀ a, y a ∈ Vb a) ∧ z = ∑ a, y a}
    with hV
  -- `V` is convex: a mix of sums is the sum of the mixes.
  have hVconv : Convex ℝ V := by
    rintro _ ⟨y₁, h₁, rfl⟩ _ ⟨y₂, h₂, rfl⟩ s t hs ht hst
    refine ⟨fun a => s • y₁ a + t • y₂ a,
      fun a => convex_strictUpper (hR a) (hconv a) (x a) (h₁ a) (h₂ a) hs ht hst, ?_⟩
    simp [Finset.sum_add_distrib, Finset.smul_sum]
  -- `ω̄ ∉ V`: otherwise the corresponding allocation is a feasible Pareto
  -- improvement on `x`.
  have hωV : E.totalEndowment ∉ V := by
    rintro ⟨y, hy, hsumy⟩
    exact hx.2 y ⟨fun a => (hy a).1, hsumy.symm⟩ ⟨fun a => (hy a).2.1, a₀, (hy a₀).2⟩
  -- Supporting prices.
  obtain ⟨p, hp0, hp⟩ := exists_price_support hVconv (fun h => hωV (interior_subset h))
  refine ⟨p, hp0, hx.1, hsum p, fun a y hy0 hyx => ?_⟩
  -- The total value `g(y') = ∑_b p · y'_b` is continuous in the allocation `y'`.
  set g : Allocation α ι → ℝ := fun y' => ∑ b, cost p (y' b) with hg
  have hgc : Continuous g :=
    continuous_finsetSum _ fun b _ => (continuous_cost p).comp (continuous_apply b)
  -- Allocations giving `a` exactly `y` and everybody else something strictly
  -- better than `x_b`.
  set T : Set (Allocation α ι) :=
    Set.pi Set.univ (fun b => if b = a then {y} else Vb b) with hT
  have hTK : T ⊆ {y' | cost p E.totalEndowment ≤ g y'} := by
    intro y' hy'
    have hmem : ∀ b, y' b ∈ Vb b := by
      intro b
      have := hy' b (Set.mem_univ b)
      by_cases hb : b = a
      · subst hb
        simp only [↓reduceIte, Set.mem_singleton_iff] at this
        rw [this]
        exact ⟨hy0, hyx⟩
      · simpa [hb] using this
    have := hp (∑ b, y' b) ⟨y', hmem, rfl⟩
    simpa [hg, cost_sum] using this
  -- `x` with `a`'s bundle replaced by `y` lies in the closure of `T`.
  have hcl : Function.update x a y ∈ closure T := by
    rw [hT, closure_pi_set]
    intro b _
    by_cases hb : b = a
    · subst hb
      simp only [↓reduceIte, Function.update_self, closure_singleton,
        Set.mem_singleton_iff]
    · simp only [hb, ↓reduceIte, Function.update_of_ne hb]
      exact mem_closure_strictUpper (hlns b) (hx.1.1 b)
  -- Pass to the limit: the inequality `p · ω̄ ≤ g` is closed.
  have hlim : cost p E.totalEndowment ≤ g (Function.update x a y) :=
    closure_minimal hTK (isClosed_le continuous_const hgc) hcl
  -- Unpack: `∑_b p · x_b ≤ p · y + ∑_{b ≠ a} p · x_b`.
  rw [← hsum p] at hlim
  simp only [hg] at hlim
  have hupd : ∀ b, cost p (Function.update x a y b)
      = Function.update (fun b => cost p (x b)) a (cost p y) b := fun b => by
    by_cases hb : b = a
    · subst hb; simp
    · simp [Function.update_of_ne hb]
  simp only [hupd] at hlim
  rw [Finset.sum_update_of_mem (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hlim
  have : Finset.univ \ {a} = Finset.univ.erase a := by
    ext b; simp [and_comm]
  rw [this] at hlim
  linarith

/-! ### 3. From quasi-equilibrium to equilibrium (MWG Prop. 16.D.2) -/

/-- **Cheaper-point lemma** (MWG Prop. 16.D.2, one consumer). Suppose `R` is
rational and continuous, and some affordable bundle `z ≥ 0` costs strictly less
than `w`. If every bundle strictly preferred to `x` costs at least `w`, then
every such bundle actually costs *more* than `w`.

Proof: if `y ≻ x` with `p · y ≤ w`, move slightly from `y` toward `z`. The
mix still costs less than `w`, and by continuity is still strictly better
than `x`, which contradicts the hypothesis. -/
theorem cost_gt_of_cheaper_point {R : (ι → ℝ) → (ι → ℝ) → Prop} (hR : Rational R)
    (hcont : ContinuousPref R) {p x z : ι → ℝ} {w : ℝ} (hx0 : 0 ≤ x) (hz0 : 0 ≤ z)
    (hzw : cost p z < w) (hquasi : ∀ y, 0 ≤ y → P R y x → w ≤ cost p y)
    {y : ι → ℝ} (hy0 : 0 ≤ y) (hyx : P R y x) : w < cost p y := by
  by_contra hle
  push Not at hle
  -- The path `t ↦ y + t (z - y)` starts at `y`, outside the closed set
  -- `{v ≥ 0 | x ≿ v}`; so it stays outside for small `t`.
  set L : Set (ι → ℝ) := {v | 0 ≤ v ∧ R x v}
  have hLc : IsClosed L := (hcont x hx0).2
  have hyL : y ∉ L := fun h => hyx.2 h.2
  have hpath : Continuous fun t : ℝ => y + t • (z - y) := by fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), y + t • (z - y) ∈ Lᶜ :=
    hpath.continuousAt.eventually_mem (by simpa using hLc.isOpen_compl.mem_nhds hyL)
  -- Pick `t ∈ (0, 1]` with the mix outside `L`.
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set v := y + t • (z - y) with hv
  have hvL : v ∉ L := hball htε
  -- `v = (1 - t) y + t z ≥ 0`.
  have hv' : v = (1 - t) • y + t • z := by
    rw [hv, smul_sub, sub_smul, one_smul]; abel
  have hv0 : 0 ≤ v := by
    rw [hv']
    exact add_nonneg (smul_nonneg (by linarith) hy0) (smul_nonneg ht0.le hz0)
  -- So `v ≻ x` (completeness), hence `w ≤ p · v` ...
  have hvx : P R v x := (hR.P_iff_not v x).2 fun h => hvL ⟨hv0, h⟩
  have hwv := hquasi v hv0 hvx
  -- ... but `p · v = (1 - t) p · y + t p · z < w`.
  have hcv : cost p v = (1 - t) * cost p y + t * cost p z := by
    rw [hv', cost_add_right, cost_smul_right, cost_smul_right]
  have : cost p v < w := by
    rw [hcv]
    nlinarith
  linarith

/-- **Quasi-equilibrium ⇒ equilibrium** (MWG Prop. 16.D.2): if preferences are
rational and continuous and every consumer has a cheaper point, a price
quasi-equilibrium with transfers is a price equilibrium with transfers. -/
theorem IsPriceQuasiEquilibriumWithTransfers.isPriceEquilibriumWithTransfers
    (hR : ∀ a, Rational (E.pref a)) (hcont : ∀ a, ContinuousPref (E.pref a))
    {p : ι → ℝ} {w : α → ℝ} {x : Allocation α ι}
    (h : E.IsPriceQuasiEquilibriumWithTransfers p w x)
    (hcheap : ∀ a, ∃ z, 0 ≤ z ∧ cost p z < w a) :
    E.IsPriceEquilibriumWithTransfers p w x := by
  refine ⟨h.1, h.2.1, fun a y hy hyx => ?_⟩
  obtain ⟨z, hz0, hzw⟩ := hcheap a
  exact cost_gt_of_cheaper_point (hR a) (hcont a) (h.1.1 a) hz0 hzw (fun y hy hyx => h.2.2 a y hy hyx)
    hy hyx

/-- In a price equilibrium with transfers where `wₐ = p · xₐ` and preferences
are complete, each `xₐ` is the consumer's Walrasian demand at `(p, wₐ)`. -/
theorem IsPriceEquilibriumWithTransfers.mem_demand (hR : ∀ a, Rational (E.pref a))
    {p : ι → ℝ} {x : Allocation α ι}
    (h : E.IsPriceEquilibriumWithTransfers p (fun a => cost p (x a)) x) (a : α) :
    x a ∈ demand (E.pref a) p (cost p (x a)) := by
  refine ⟨⟨h.1.1 a, le_rfl⟩, fun y hy => ?_⟩
  -- If `y ≻ xₐ` it would cost more than `p · xₐ`, but it is in the budget.
  by_contra hnot
  have hyx : P (E.pref a) y (x a) := ((hR a).P_iff_not y (x a)).2 hnot
  have := h.2.2 a y hy.1 hyx
  linarith [hy.2]

/-! ### 4. The textbook Second Welfare Theorem -/

/-- With strongly monotone preferences, supporting prices of a
quasi-equilibrium are nonnegative: if `pᵢ < 0`, adding good `i` to `xₐ` would
be strictly better and strictly cheaper. -/
theorem IsPriceQuasiEquilibriumWithTransfers.price_nonneg [Nonempty α]
    (hmono : ∀ a, StronglyMonotone (E.pref a)) {p : ι → ℝ} {x : Allocation α ι}
    (h : E.IsPriceQuasiEquilibriumWithTransfers p (fun a => cost p (x a)) x) :
    0 ≤ p := by
  classical
  intro i
  by_contra hneg
  push Not at hneg
  simp only [Pi.zero_apply] at hneg
  obtain ⟨a⟩ := ‹Nonempty α›
  set y := x a + Pi.single i 1 with hy
  have hxy : x a ≤ y := by
    intro j
    simp only [hy, Pi.add_apply]
    have : (0 : ℝ) ≤ (Pi.single i 1 : ι → ℝ) j := by
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    linarith
  have hne : x a ≠ y := by
    intro heq
    have := congrFun heq i
    simp [hy] at this
  have hbetter := hmono a (x a) y (h.1.1 a) hxy hne
  have hge : cost p (x a) ≤ cost p y := h.2.2 a y ((h.1.1 a).trans hxy) hbetter
  -- `p · y = p · xₐ + pᵢ < p · xₐ`.
  have hcy : cost p y = cost p (x a) + p i := by
    rw [hy, cost_add_right]
    congr 1
    simp [cost, Pi.single_apply]
  linarith

/-- **Second Welfare Theorem, textbook form** (MWG Prop. 16.D.1 + 16.D.2).
If preferences are rational, strongly monotone, continuous and convex, and `x`
is a Pareto optimal allocation with every bundle strictly positive (`xₐ ≫ 0`),
then there are nonzero, nonnegative prices `p` at which `x`, together with
the transfers `wₐ = p · xₐ`, is a price equilibrium with transfers, and each
`xₐ` is consumer `a`'s Walrasian demand at `(p, p · xₐ)`. -/
theorem second_welfare_theorem_demand [Nonempty ι] [Nonempty α]
    (hR : ∀ a, Rational (E.pref a)) (hmono : ∀ a, StronglyMonotone (E.pref a))
    (hcont : ∀ a, ContinuousPref (E.pref a)) (hconv : ∀ a, ConvexPref (E.pref a))
    {x : Allocation α ι} (hx : E.ParetoOptimal x) (hpos : ∀ a i, 0 < x a i) :
    ∃ p : ι → ℝ, p ≠ 0 ∧ 0 ≤ p ∧
      E.IsPriceEquilibriumWithTransfers p (fun a => cost p (x a)) x ∧
      ∀ a, x a ∈ demand (E.pref a) p (cost p (x a)) := by
  obtain ⟨p, hp0, hq⟩ := second_welfare_theorem hR hconv
    (fun a => (hmono a).locallyNonsatiated) hx
  have hpnn : 0 ≤ p := hq.price_nonneg hmono
  -- Cheaper point: the zero bundle, which costs `0 < p · xₐ` since `p ≥ 0`,
  -- `p ≠ 0` and `xₐ ≫ 0`.
  have hcheap : ∀ a, ∃ z, 0 ≤ z ∧ cost p z < cost p (x a) := by
    intro a
    refine ⟨0, le_rfl, ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hp0 (funext hall)
    have hpi : 0 < p i := lt_of_le_of_ne (hpnn i) (Ne.symm hi)
    have : 0 < cost p (x a) :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hpnn j) (hpos a j).le)
        ⟨i, Finset.mem_univ i, mul_pos hpi (hpos a i)⟩
    simpa [cost] using this
  have heq := hq.isPriceEquilibriumWithTransfers hR hcont hcheap
  exact ⟨p, hp0, hpnn, heq, heq.mem_demand hR⟩

end ExchangeEconomy

end Econ
