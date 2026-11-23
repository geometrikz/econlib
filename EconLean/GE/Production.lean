/-
# Production economies: First and Second Welfare Theorems with firms

MWG §16.B (Defs. 16.B.1–16.B.4, private ownership economy), §16.C
(Prop. 16.C.1), §16.D (Def. 16.D.1, Prop. 16.D.1).

**The economics.** A *private ownership economy* adds firms `j : β` to an
exchange economy. Firm `j` chooses a net output vector `y_j` from its
production set `Y_j ⊆ ℝ^ι` (negative entries are inputs). Consumer `a` owns
share `θ_{aj} ≥ 0` of firm `j`'s profits, with `∑ₐ θ_{aj} = 1`.

* `(x, y)` is **feasible** if bundles are nonnegative, each `y_j ∈ Y_j`, and
  `∑ₐ xₐ = ω̄ + ∑ⱼ y_j` (MWG Def. 16.B.1).
* `(p, x, y)` is a **Walrasian equilibrium** (MWG Def. 16.B.3) if every firm
  maximizes profit `p · y_j` on `Y_j`, every consumer's bundle is demanded at
  wealth `p · ωₐ + ∑ⱼ θ_{aj} p · y_j`, and markets clear.

Results:
1. **First Welfare Theorem** (MWG Prop. 16.C.1): with rational, locally
   nonsatiated preferences, a Walrasian equilibrium allocation is Pareto
   optimal. No assumption on production sets is needed.
2. **Second Welfare Theorem** (MWG Prop. 16.D.1): with rational, convex,
   locally nonsatiated preferences and *convex* production sets, every Pareto
   optimal allocation is supported by nonzero prices as a price
   quasi-equilibrium with transfers, in which every firm maximizes profit.
   The proof separates the convex set of aggregate bundles that would make
   everyone better off from the convex set of aggregate supplies `ω̄ + ∑ⱼ Y_j`.
3. **Quasi-equilibrium ⇒ equilibrium** under continuity and a cheaper point
   (MWG Prop. 16.D.2), reusing the exchange-economy lemma.

**The Lean.** `ProductionEconomy` *extends* `ExchangeEconomy`, so preferences,
endowments and Pareto dominance are literally shared with the exchange case.
-/
module

public import EconLean.GE.SecondWelfare

@[expose] public section

namespace Econ

open Finset Pointwise

variable {α β ι : Type*}

/-- A **private ownership production economy** (MWG Def. 16.B.1 / §17.B):
an exchange economy plus firms `β` with production sets and ownership shares. -/
structure ProductionEconomy (α β ι : Type*) [Fintype α] extends ExchangeEconomy α ι where
  /-- Firm `j`'s production set `Y_j` (net outputs). -/
  prod : β → Set (ι → ℝ)
  /-- Consumer `a`'s share `θ_{aj}` of firm `j`'s profits. -/
  share : α → β → ℝ
  share_nonneg : ∀ a j, 0 ≤ share a j
  /-- Each firm is wholly owned by the consumers. -/
  share_sum : ∀ j, ∑ a, share a j = 1

namespace ProductionEconomy

variable [Fintype α] [Fintype β] [Fintype ι] (E : ProductionEconomy α β ι)

/-- `y` **maximizes profit** at prices `p` on the production set `Y`. -/
def ProfitMax (p : ι → ℝ) (Y : Set (ι → ℝ)) (y : ι → ℝ) : Prop :=
  y ∈ Y ∧ ∀ y' ∈ Y, cost p y' ≤ cost p y

/-- Consumer `a`'s wealth: endowment value plus profit shares,
`p · ωₐ + ∑ⱼ θ_{aj} p · y_j`. -/
def wealth (p : ι → ℝ) (y : β → ι → ℝ) (a : α) : ℝ :=
  cost p (E.endow a) + ∑ j, E.share a j * cost p (y j)

/-- **Feasible allocation** `(x, y)` (MWG Def. 16.B.1). -/
def Feasible (x : Allocation α ι) (y : β → ι → ℝ) : Prop :=
  (∀ a, 0 ≤ x a) ∧ (∀ j, y j ∈ E.prod j) ∧ ∑ a, x a = E.totalEndowment + ∑ j, y j

/-- **Pareto optimality** (MWG Def. 16.B.2): feasible, and no feasible
allocation Pareto dominates it. -/
def ParetoOptimal (x : Allocation α ι) (y : β → ι → ℝ) : Prop :=
  E.Feasible x y ∧ ∀ x' y', E.Feasible x' y' → ¬ E.ParetoDominates x' x

/-- **Walrasian equilibrium** of a private ownership economy (MWG Def. 16.B.3,
17.B.1). -/
def IsWalrasianEquilibrium (p : ι → ℝ) (x : Allocation α ι) (y : β → ι → ℝ) : Prop :=
  (∀ j, ProfitMax p (E.prod j) (y j)) ∧
    (∀ a, x a ∈ demand (E.pref a) p (E.wealth p y a)) ∧
    ∑ a, x a = E.totalEndowment + ∑ j, y j

/-- **Price quasi-equilibrium with transfers** (MWG Def. 16.D.1). -/
def IsPriceQuasiEquilibriumWithTransfers (p : ι → ℝ) (w : α → ℝ)
    (x : Allocation α ι) (y : β → ι → ℝ) : Prop :=
  E.Feasible x y ∧ (∀ j, ProfitMax p (E.prod j) (y j)) ∧
    ∑ a, w a = cost p (E.totalEndowment + ∑ j, y j) ∧
    ∀ a z, 0 ≤ z → P (E.pref a) z (x a) → w a ≤ cost p z

/-- **Price equilibrium with transfers** (MWG Def. 16.B.4, in the
"strictly preferred ⇒ costs more" form; see the exchange file for the
equivalence with MWG's affordability form under local nonsatiation). -/
def IsPriceEquilibriumWithTransfers (p : ι → ℝ) (w : α → ℝ)
    (x : Allocation α ι) (y : β → ι → ℝ) : Prop :=
  E.Feasible x y ∧ (∀ j, ProfitMax p (E.prod j) (y j)) ∧
    ∑ a, w a = cost p (E.totalEndowment + ∑ j, y j) ∧
    ∀ a z, 0 ≤ z → P (E.pref a) z (x a) → w a < cost p z

variable {E}

/-- Total wealth is the value of the aggregate endowment plus total profits
(shares add up to one). -/
theorem sum_wealth (p : ι → ℝ) (y : β → ι → ℝ) :
    ∑ a, E.wealth p y a = cost p (E.totalEndowment + ∑ j, y j) := by
  simp only [wealth, Finset.sum_add_distrib, cost_add_right, cost_sum]
  rw [ExchangeEconomy.totalEndowment, cost_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, E.share_sum j, one_mul]

/-- An equilibrium allocation is feasible. -/
theorem IsWalrasianEquilibrium.feasible {p : ι → ℝ} {x : Allocation α ι}
    {y : β → ι → ℝ} (h : E.IsWalrasianEquilibrium p x y) : E.Feasible x y :=
  ⟨fun a => (h.2.1 a).1.1, fun j => (h.1 j).1, h.2.2⟩

/-! ### 1. First Welfare Theorem with production (MWG Prop. 16.C.1) -/

/-- **First Fundamental Theorem of Welfare Economics, production economy**
(MWG Prop. 16.C.1). With rational, locally nonsatiated preferences, every
Walrasian equilibrium allocation `(x, y)` is Pareto optimal.

Proof: a feasible Pareto improvement `(x', y')` costs strictly more than total
wealth, `∑ p · x'ₐ > p · ω̄ + ∑ⱼ p · y_j`, while profit maximization gives
`p · y_j ≥ p · y'_j`, so `∑ p · x'ₐ > p · (ω̄ + ∑ y'_j) = p · ∑ x'ₐ`. -/
theorem first_welfare_theorem (hR : ∀ a, Rational (E.pref a))
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {p : ι → ℝ} {x : Allocation α ι}
    {y : β → ι → ℝ} (heq : E.IsWalrasianEquilibrium p x y) : E.ParetoOptimal x y := by
  refine ⟨heq.feasible, fun x' y' hfeas ⟨hweak, b, hb⟩ => ?_⟩
  have hlt : ∑ a, E.wealth p y a < ∑ a, cost p (x' a) :=
    Finset.sum_lt_sum
      (fun a _ => ExchangeEconomy.cost_ge_of_mem_demand (hR a) (hlns a) (heq.2.1 a)
        (hfeas.1 a) (hweak a))
      ⟨b, Finset.mem_univ b,
        ExchangeEconomy.cost_gt_of_mem_demand (heq.2.1 b) (hfeas.1 b) hb⟩
  rw [sum_wealth, ← cost_sum, hfeas.2.2] at hlt
  -- Profit maximization: `p · y'_j ≤ p · y_j` for every firm.
  have hprofit : ∑ j, cost p (y' j) ≤ ∑ j, cost p (y j) :=
    Finset.sum_le_sum fun j _ => (heq.1 j).2 (y' j) (hfeas.2.1 j)
  rw [cost_add_right, cost_add_right, cost_sum, cost_sum] at hlt
  linarith

/-! ### 2. Second Welfare Theorem with production (MWG Prop. 16.D.1) -/

/-- **Limit lemma.** If `c₀ ≤ ∑ₐ p · y'ₐ` for every profile with `y'ₐ ∈ sₐ`,
then also for every profile in the closures. -/
theorem le_sum_cost_of_mem_closure {s : α → Set (ι → ℝ)} {c₀ : ℝ} {p : ι → ℝ}
    (h : ∀ y' : Allocation α ι, (∀ a, y' a ∈ s a) → c₀ ≤ ∑ a, cost p (y' a))
    {z : Allocation α ι} (hz : ∀ a, z a ∈ closure (s a)) : c₀ ≤ ∑ a, cost p (z a) := by
  have hgc : Continuous fun y' : Allocation α ι => ∑ a, cost p (y' a) :=
    continuous_finsetSum _ fun b _ => (continuous_cost p).comp (continuous_apply b)
  have hsub : Set.pi Set.univ s ⊆ {y' | c₀ ≤ ∑ a, cost p (y' a)} :=
    fun y' hy' => h y' fun a => hy' a (Set.mem_univ a)
  have hzc : z ∈ closure (Set.pi Set.univ s) := by
    rw [closure_pi_set]
    exact fun a _ => hz a
  exact closure_minimal hsub (isClosed_le continuous_const hgc) hzc

omit [Fintype ι] in
/-- `∑_b f (update x a v b) = ∑_b f (x b) - f (x a) + f v`. -/
theorem sum_update_eq {γ : Type*} [Fintype γ] [DecidableEq γ] (f : (ι → ℝ) → ℝ)
    (x : γ → ι → ℝ) (a : γ) (v : ι → ℝ) :
    ∑ b, f (Function.update x a v b) = ∑ b, f (x b) - f (x a) + f v := by
  have hupd : ∀ b, f (Function.update x a v b) = Function.update (fun b => f (x b)) a (f v) b :=
    fun b => by
      by_cases hb : b = a
      · subst hb; simp
      · simp [Function.update_of_ne hb]
  simp only [hupd]
  rw [Finset.sum_update_of_mem (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have : Finset.univ \ {a} = Finset.univ.erase a := by ext b; simp [and_comm]
  rw [this]
  ring

/-- **Second Fundamental Theorem of Welfare Economics, production economy**
(MWG Prop. 16.D.1). If preferences are rational, convex and locally
nonsatiated and every production set is convex, then for every Pareto optimal
allocation `(x, y)` there are nonzero prices `p` such that, with transfers
`wₐ = p · xₐ`, `(p, w, x, y)` is a price quasi-equilibrium with transfers:
every firm maximizes profit, and anything a consumer strictly prefers costs
at least `wₐ`. -/
theorem second_welfare_theorem [Nonempty ι] [Nonempty α] (hR : ∀ a, Rational (E.pref a))
    (hconv : ∀ a, ConvexPref (E.pref a)) (hlns : ∀ a, LocallyNonsatiated (E.pref a))
    (hY : ∀ j, Convex ℝ (E.prod j)) {x : Allocation α ι} {y : β → ι → ℝ}
    (hxy : E.ParetoOptimal x y) :
    ∃ p : ι → ℝ, p ≠ 0 ∧
      E.IsPriceQuasiEquilibriumWithTransfers p (fun a => cost p (x a)) x y := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hfeas := hxy.1
  -- Strictly-better sets `Vₐ` and their sum `V`; aggregate supplies `Z`.
  set Vb : α → Set (ι → ℝ) := fun a => {z | 0 ≤ z ∧ P (E.pref a) z (x a)} with hVb
  set V : Set (ι → ℝ) := {v | ∃ x' : Allocation α ι, (∀ a, x' a ∈ Vb a) ∧ v = ∑ a, x' a}
  set Z : Set (ι → ℝ) :=
    {z | ∃ y' : β → ι → ℝ, (∀ j, y' j ∈ E.prod j) ∧ z = E.totalEndowment + ∑ j, y' j}
  have hVconv : Convex ℝ V := by
    rintro _ ⟨y₁, h₁, rfl⟩ _ ⟨y₂, h₂, rfl⟩ s t hs ht hst
    refine ⟨fun a => s • y₁ a + t • y₂ a,
      fun a => convex_strictUpper (hR a) (hconv a) (x a) (h₁ a) (h₂ a) hs ht hst, ?_⟩
    simp [Finset.sum_add_distrib, Finset.smul_sum]
  have hZconv : Convex ℝ Z := by
    rintro _ ⟨y₁, h₁, rfl⟩ _ ⟨y₂, h₂, rfl⟩ s t hs ht hst
    refine ⟨fun j => s • y₁ j + t • y₂ j, fun j => hY j (h₁ j) (h₂ j) hs ht hst, ?_⟩
    simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
    calc _ = (s + t) • E.totalEndowment + (∑ j, s • y₁ j + ∑ j, t • y₂ j) := by
            rw [add_smul]; abel
      _ = _ := by rw [hst, one_smul]
  -- `0 ∉ V - Z`: otherwise some feasible allocation makes everyone better off.
  have h0 : (0 : ι → ℝ) ∉ V - Z := by
    rintro ⟨v, ⟨x', hx', rfl⟩, z, ⟨y', hy', rfl⟩, hvz⟩
    refine hxy.2 x' y' ⟨fun a => (hx' a).1, hy', sub_eq_zero.1 hvz⟩
      ⟨fun a => (hx' a).2.1, a₀, (hx' a₀).2⟩
  obtain ⟨p, hp0, hp⟩ := exists_price_support (hVconv.sub hZconv)
    (fun h => h0 (interior_subset h))
  -- Unpack: `p · z ≤ p · v` for all `v ∈ V`, `z ∈ Z`.
  have hpVZ : ∀ v ∈ V, ∀ z ∈ Z, cost p z ≤ cost p v := by
    intro v hv z hz
    have := hp (v - z) ⟨v, hv, z, hz, rfl⟩
    simp only [cost_sub_right] at this
    simpa [cost] using this
  -- The value of `x` is `p · (ω̄ + ∑ y)`.
  have hxval : ∑ a, cost p (x a) = cost p (E.totalEndowment + ∑ j, y j) := by
    rw [← cost_sum, hfeas.2.2]
  refine ⟨p, hp0, hfeas, fun j => ⟨hfeas.2.1 j, fun y' hy' => ?_⟩, hxval, ?_⟩
  · -- Firms: compare `ω̄ + ∑ y` with `j`'s plan replaced by `y'`, against `x ∈ cl V`.
    have hz : E.totalEndowment + ∑ k, Function.update y j y' k ∈ Z := by
      refine ⟨Function.update y j y', fun k => ?_, rfl⟩
      by_cases hk : k = j
      · subst hk; simpa using hy'
      · simpa [Function.update_of_ne hk] using hfeas.2.1 k
    have hle := le_sum_cost_of_mem_closure (s := Vb)
      (fun x' hx' => by
        rw [← cost_sum]; exact hpVZ _ ⟨x', hx', rfl⟩ _ hz)
      (fun a => mem_closure_strictUpper (hlns a) (hfeas.1 a))
    rw [hxval, cost_add_right, cost_add_right, cost_sum, cost_sum,
      sum_update_eq (cost p) y j y'] at hle
    linarith
  · -- Consumers: as in the exchange case, with `ω̄ + ∑ y ∈ Z` as the benchmark.
    intro a z hz0 hzx
    have hZ : E.totalEndowment + ∑ k, y k ∈ Z := ⟨y, hfeas.2.1, rfl⟩
    set s : α → Set (ι → ℝ) := fun b => if b = a then {z} else Vb b
    have hle := le_sum_cost_of_mem_closure (s := s) (z := Function.update x a z)
      (fun x' hx' => by
        have hmem : ∀ b, x' b ∈ Vb b := by
          intro b
          have := hx' b
          by_cases hb : b = a
          · subst hb
            simp only [s, ↓reduceIte, Set.mem_singleton_iff] at this
            rw [this]; exact ⟨hz0, hzx⟩
          · simpa [s, hb] using this
        rw [← cost_sum]; exact hpVZ _ ⟨x', hmem, rfl⟩ _ hZ)
      (fun b => by
        by_cases hb : b = a
        · subst hb; simp [s]
        · simp only [s, hb, ↓reduceIte, Function.update_of_ne hb]
          exact mem_closure_strictUpper (hlns b) (hfeas.1 b))
    rw [← hxval, sum_update_eq (cost p) x a z] at hle
    linarith

/-! ### 3. Quasi-equilibrium ⇒ equilibrium (MWG Prop. 16.D.2) -/

/-- With continuous rational preferences and a cheaper point for each
consumer, a price quasi-equilibrium with transfers is a price equilibrium with
transfers. -/
theorem IsPriceQuasiEquilibriumWithTransfers.isPriceEquilibriumWithTransfers
    (hR : ∀ a, Rational (E.pref a)) (hcont : ∀ a, ContinuousPref (E.pref a))
    {p : ι → ℝ} {w : α → ℝ} {x : Allocation α ι} {y : β → ι → ℝ}
    (h : E.IsPriceQuasiEquilibriumWithTransfers p w x y)
    (hcheap : ∀ a, ∃ z, 0 ≤ z ∧ cost p z < w a) :
    E.IsPriceEquilibriumWithTransfers p w x y := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun a z hz hzx => ?_⟩
  obtain ⟨c, hc0, hcw⟩ := hcheap a
  exact ExchangeEconomy.cost_gt_of_cheaper_point (hR a) (hcont a) (h.1.1 a) hc0 hcw
    (fun z hz hzx => h.2.2.2 a z hz hzx) hz hzx

end ProductionEconomy

end Econ
