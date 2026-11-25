/-
# The Second Welfare Theorem in infinite-dimensional commodity spaces

Debreu (1954), "Valuation equilibrium and Pareto optimum"; Bewley (1972),
"Existence of equilibria in economies with infinitely many commodities";
Mas-Colell & Zame (1991, Handbook of Math. Econ. IV, ch. 34).

**The economics.** In MWG §16.D the Second Welfare Theorem is proved in `ℝ^L`
with the supporting hyperplane theorem. Debreu (1954) observed that the
argument needs no coordinates at all: the commodity space can be any real
topological vector space `X`, and prices become continuous linear functionals
`p : X →L[ℝ] ℝ` ("valuations"). The one hypothesis that does not come for free
in infinite dimensions is that the set of aggregate bundles that would make
everyone better off has an **interior point**; without it the separating
functional may fail to exist. This is why Bewley (1972) works in `ℓ^∞`, where
the positive cone has nonempty interior (unlike `ℓ^p` for `p < ∞`). Caveat: in
`ℓ^∞` the supporting valuation lies in the full norm dual and may be purely
finitely additive rather than a summable price sequence; obtaining `ℓ^1` prices
(Bewley's contribution, via Mackey continuity) is not formalized here.

**Setup.** Finitely many agents `a : α` with consumption sets `C a ⊆ X` and
preference relations `R a`. An allocation is feasible if `x a ∈ C a` and
`∑ₐ xₐ = ω̄` (exact market clearing). `better (C a) (R a) (x a)` is the set of
bundles in `C a` strictly preferred to `x a`.

**Results.**
* `second_welfare_theorem_tvs` (Debreu 1954, Thm 2): if `x` is weakly Pareto
  optimal, each strictly-better set is convex, each `x a` is a limit of strictly
  better bundles (local nonsatiation at `x`), and the aggregate better set has an
  interior point, then there is a nonzero continuous linear `p` making `x` a
  **valuation quasi-equilibrium**: any bundle an agent strictly prefers costs at
  least `p (x a)`. The implicit transfers are `wₐ = p (x a)`, summing to `p ω̄`.
* `interior_aggBetter_nonempty`: the interior hypothesis holds as soon as every
  agent's strictly-better set is nonempty and one of them has an interior point.
* `IsValuationQuasiEquilibrium.cost_lt_of_cheaper_point` (cf. MWG Prop.
  16.D.2): with a convex consumption set, a relatively open strictly-better set
  and a cheaper point, "costs at least" upgrades to "costs more".
  `exists_cheaper_of_mem_interior`: an interior consumption point gives a
  cheaper point at any nonzero valuation, so
  `second_welfare_theorem_tvs_equilibrium` yields a valuation equilibrium when
  every `x a` is interior to `C a`.
* `linftyEconomy_*`: a toy two-agent economy on `ℓ^∞(ℕ, ℝ)` (positive cone as
  consumption set) satisfying all hypotheses of the quasi-equilibrium theorem;
  it only illustrates that the cone has interior points, not Bewley's
  discounted-utility setting.
* `commonEconomy_*`: a toy economy on `ℓ^∞(ℕ, ℝ)` satisfying all hypotheses of
  the valuation-equilibrium theorem.

**Deviations.** Exchange only; feasibility is exact clearing (no free
disposal). Preferences are arbitrary relations (no completeness or transitivity
needed); convexity is imposed on the strictly-better sets at `x`, which is what
the proof uses. This is MWG's quasi-equilibrium-with-transfers form; Debreu
(1954) instead states equilibrium as cost minimisation over the weakly
preferred set for complete preorders, and includes production. The
equilibrium predicates below do not include market clearing; the theorems
assume `Feasible` separately.
-/
module

public import EconLean.Preferences.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace ValuationEquilibrium

open Set Finset

variable {α X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- Bundles in the consumption set `C` strictly preferred to `x`. -/
def better (C : Set X) (R : X → X → Prop) (x : X) : Set X := {y | y ∈ C ∧ P R y x}

variable [Fintype α]

/-- `x` is **feasible**: every bundle is in its consumption set and markets
clear exactly. -/
def Feasible (C : α → Set X) (ωbar : X) (x : α → X) : Prop :=
  (∀ a, x a ∈ C a) ∧ ∑ a, x a = ωbar

/-- `x` is **weakly Pareto optimal**: no feasible allocation makes every agent
strictly better off. -/
def WeaklyParetoOptimal (C : α → Set X) (R : α → X → X → Prop) (ωbar : X)
    (x : α → X) : Prop :=
  ¬ ∃ y, Feasible C ωbar y ∧ ∀ a, P (R a) (y a) (x a)

/-- The **aggregate better set** `∑ₐ {y ∈ C a | y ≻ₐ xₐ}`. -/
def aggBetter (C : α → Set X) (R : α → X → X → Prop) (x : α → X) : Set X :=
  {z | ∃ y : α → X, (∀ a, y a ∈ better (C a) (R a) (x a)) ∧ ∑ a, y a = z}

/-- `(p, x)` is a **valuation quasi-equilibrium** (with transfers `p (x a)`):
any bundle in `C a` that agent `a` strictly prefers to `x a` costs at least
`p (x a)`. -/
def IsValuationQuasiEquilibrium (C : α → Set X) (R : α → X → X → Prop)
    (p : X →L[ℝ] ℝ) (x : α → X) : Prop :=
  ∀ a, ∀ y ∈ C a, P (R a) y (x a) → p (x a) ≤ p y

/-- `(p, x)` is a **valuation equilibrium** (with transfers `p (x a)`): any
bundle in `C a` that agent `a` strictly prefers to `x a` costs more than
`p (x a)`, so `x a` is best on the budget set `{y ∈ C a | p y ≤ p (x a)}`. -/
def IsValuationEquilibrium (C : α → Set X) (R : α → X → X → Prop)
    (p : X →L[ℝ] ℝ) (x : α → X) : Prop :=
  ∀ a, ∀ y ∈ C a, P (R a) y (x a) → p (x a) < p y

/-- The transfers `wₐ = p (x a)` of a feasible allocation add up to the value
of the aggregate endowment. -/
theorem sum_wealth_eq {C : α → Set X} {ωbar : X} {x : α → X} (hx : Feasible C ωbar x)
    (p : X →L[ℝ] ℝ) : ∑ a, p (x a) = p ωbar := by
  rw [← hx.2, map_sum]

omit [TopologicalSpace X] in
/-- The aggregate better set is convex if every individual better set is. -/
theorem convex_aggBetter {C : α → Set X} {R : α → X → X → Prop} {x : α → X}
    (hconv : ∀ a, Convex ℝ (better (C a) (R a) (x a))) : Convex ℝ (aggBetter C R x) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ s t hs ht hst
  refine ⟨fun a => s • y a + t • y' a, fun a => hconv a (hy a) (hy' a) hs ht hst, ?_⟩
  simp [Finset.sum_add_distrib, Finset.smul_sum]

omit [Module ℝ X] [TopologicalSpace X] in
/-- At a weakly Pareto optimal allocation, the aggregate endowment is not in the
aggregate better set. -/
theorem not_mem_aggBetter {C : α → Set X} {R : α → X → X → Prop} {ωbar : X} {x : α → X}
    (hpo : WeaklyParetoOptimal C R ωbar x) : ωbar ∉ aggBetter C R x := by
  rintro ⟨y, hy, hsum⟩
  exact hpo ⟨y, ⟨fun a => (hy a).1, hsum⟩, fun a => (hy a).2⟩

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

omit [Module ℝ X] [ContinuousSMul ℝ X] in
/-- The interior hypothesis holds if one agent's better set has an interior
point and all better sets are nonempty. -/
theorem interior_aggBetter_nonempty {C : α → Set X} {R : α → X → X → Prop} {x : α → X}
    (hne : ∀ b, (better (C b) (R b) (x b)).Nonempty) (a : α)
    (ha : (interior (better (C a) (R a) (x a))).Nonempty) :
    (interior (aggBetter C R x)).Nonempty := by
  classical
  choose y hy using hne
  obtain ⟨u, hu⟩ := ha
  set c := ∑ b ∈ univ \ {a}, y b
  have hsub : (fun v => v + c) '' interior (better (C a) (R a) (x a)) ⊆ aggBetter C R x := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨Function.update y a v, fun b => ?_, ?_⟩
    · rcases eq_or_ne b a with rfl | hb
      · simpa using interior_subset hv
      · simpa [Function.update_of_ne hb] using hy b
    · rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
  have hopen : IsOpen ((fun v => v + c) '' interior (better (C a) (R a) (x a))) :=
    isOpenMap_add_right c _ isOpen_interior
  exact ⟨u + c, interior_maximal hsub hopen ⟨u, hu, rfl⟩⟩

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] in
/-- A small step from `x` into the strictly-better set changes value by less
than `ε`, by continuity of `p` and local nonsatiation at `x`. -/
theorem exists_better_lt {C : Set X} {R : X → X → Prop} {x : X}
    (hlns : x ∈ closure (better C R x)) (p : X →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ better C R x, p y < p x + ε := by
  have hU : IsOpen {w | p w < p x + ε} := isOpen_lt p.continuous continuous_const
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hlns _ hU (by simpa using hε)
  exact ⟨y, hy2, hy1⟩

/-- **Second Welfare Theorem in a topological vector space** (Debreu 1954,
Thm 2): a weakly Pareto optimal allocation with convex strictly-better sets,
local nonsatiation at `x`, and an aggregate better set with nonempty interior is
supported by a nonzero continuous linear valuation as a valuation
quasi-equilibrium with transfers `p (x a)`. -/
theorem second_welfare_theorem_tvs {C : α → Set X} {R : α → X → X → Prop} {ωbar : X}
    {x : α → X} (hx : Feasible C ωbar x) (hpo : WeaklyParetoOptimal C R ωbar x)
    (hconv : ∀ a, Convex ℝ (better (C a) (R a) (x a)))
    (hlns : ∀ a, x a ∈ closure (better (C a) (R a) (x a)))
    (hint : (interior (aggBetter C R x)).Nonempty) :
    ∃ p : X →L[ℝ] ℝ, p ≠ 0 ∧ IsValuationQuasiEquilibrium C R p x := by
  classical
  have hZ := convex_aggBetter hconv
  have hω : ωbar ∉ interior (aggBetter C R x) := fun h =>
    not_mem_aggBetter hpo (interior_subset h)
  obtain ⟨p, hp⟩ := geometric_hahn_banach_point_open hZ.interior isOpen_interior hω
  -- every aggregate better bundle is worth at least `p ω̄`
  have hge : ∀ z ∈ aggBetter C R x, p ωbar ≤ p z := by
    intro z hz
    have hcl : z ∈ closure (interior (aggBetter C R x)) := by
      rw [hZ.closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure hz
    have : closure (interior (aggBetter C R x)) ⊆ {w | p ωbar ≤ p w} :=
      closure_minimal (fun w hw => (hp w hw).le) (isClosed_le continuous_const p.continuous)
    exact this hcl
  refine ⟨p, ?_, ?_⟩
  · rintro rfl
    obtain ⟨b, hb⟩ := hint
    simpa using hp b hb
  · intro a y hyC hyP
    by_contra hlt
    push Not at hlt
    set δ := p (x a) - p y with hδ
    have hδpos : 0 < δ := by linarith
    set n := Fintype.card α
    set ε := δ / (n + 1) with hε
    have hεpos : 0 < ε := by positivity
    choose y' hy' hy'p using fun b => exists_better_lt (hlns b) p hεpos
    let z := Function.update y' a y
    have hz : ∑ b, z b ∈ aggBetter C R x := by
      refine ⟨z, fun b => ?_, rfl⟩
      rcases eq_or_ne b a with rfl | hb
      · simp only [z, Function.update_self]; exact ⟨hyC, hyP⟩
      · simpa [z, Function.update_of_ne hb] using hy' b
    have h1 := hge _ hz
    rw [map_sum, ← sum_wealth_eq hx p, ← sub_nonneg, ← Finset.sum_sub_distrib,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h1
    have h2 : ∑ b ∈ univ.erase a, (p (z b) - p (x b)) ≤ (univ.erase a).card • ε := by
      apply Finset.sum_le_card_nsmul
      intro b hb
      have hb' : b ≠ a := Finset.ne_of_mem_erase hb
      simp only [z, Function.update_of_ne hb']
      linarith [hy'p b]
    have hcard : ((univ.erase a).card : ℝ) ≤ n := by
      exact_mod_cast Finset.card_le_univ _
    have h3 : ((univ.erase a).card : ℝ) * ε < δ := by
      calc ((univ.erase a).card : ℝ) * ε ≤ n * ε := by gcongr
        _ < (n + 1) * ε := by linarith
        _ = δ := by rw [hε]; field_simp
    simp only [z, Function.update_self, nsmul_eq_mul] at h1 h2
    linarith

omit [Fintype α] in
/-- **Cheaper point** (MWG Prop. 16.D.2): if the consumption
set is convex, the strictly-better set is relatively open in it, and some bundle
in `C a` costs strictly less than `x a`, then at a valuation quasi-equilibrium
every strictly preferred bundle costs strictly more. -/
theorem IsValuationQuasiEquilibrium.cost_lt_of_cheaper_point {C : α → Set X}
    {R : α → X → X → Prop} {p : X →L[ℝ] ℝ} {x : α → X}
    (hq : IsValuationQuasiEquilibrium C R p x) {a : α} (hC : Convex ℝ (C a))
    (hopen : ∃ U, IsOpen U ∧ better (C a) (R a) (x a) = U ∩ C a)
    (hcheap : ∃ w ∈ C a, p w < p (x a)) :
    ∀ y ∈ C a, P (R a) y (x a) → p (x a) < p y := by
  obtain ⟨U, hU, hUeq⟩ := hopen
  obtain ⟨w, hwC, hw⟩ := hcheap
  intro y hyC hyP
  have hle := hq a y hyC hyP
  by_contra hlt
  have heq : p y = p (x a) := le_antisymm (not_lt.1 hlt) hle
  have hyU : y ∈ U := by
    have : y ∈ better (C a) (R a) (x a) := ⟨hyC, hyP⟩
    rw [hUeq] at this
    exact this.1
  have hcont : Continuous fun t : ℝ => y + t • (w - y) := by fun_prop
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioc 0 1), y + t • (w - y) ∈ U := by
    apply eventually_nhdsWithin_of_eventually_nhds
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hyU)
  have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioc 0 1), t ∈ Ioc (0 : ℝ) 1 :=
    self_mem_nhdsWithin
  have : (nhdsWithin (0 : ℝ) (Ioc 0 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨t, htU, ht0, ht1⟩ := (hev.and hmem).exists
  have htC : y + t • (w - y) ∈ C a := hC.add_smul_sub_mem hyC hwC ⟨ht0.le, ht1⟩
  have hbetter : y + t • (w - y) ∈ better (C a) (R a) (x a) := by
    rw [hUeq]; exact ⟨htU, htC⟩
  have h := hq a _ hbetter.1 hbetter.2
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at h
  nlinarith

omit [Fintype α] in
/-- If `xa` is an interior point of the consumption set, every nonzero
continuous linear valuation admits a strictly cheaper point in it. -/
theorem exists_cheaper_of_mem_interior {Ca : Set X} {xa : X} (h : xa ∈ interior Ca)
    {p : X →L[ℝ] ℝ} (hp : p ≠ 0) : ∃ w ∈ Ca, p w < p xa := by
  obtain ⟨v, hv⟩ : ∃ v, p v ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hp (ContinuousLinearMap.ext h')
  have hcont : Continuous fun t : ℝ => xa - t • ((p v)⁻¹ • v) := by fun_prop
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), xa - t • ((p v)⁻¹ • v) ∈ Ca :=
    eventually_nhdsWithin_of_eventually_nhds
      (hcont.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 h))
  obtain ⟨t, htC, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨_, htC, ?_⟩
  have ht : (0 : ℝ) < t := ht0
  simp only [map_sub, map_smul, smul_eq_mul, inv_mul_cancel₀ hv, mul_one]
  linarith

/-- **Second Welfare Theorem, valuation-equilibrium form**: under the hypotheses
of `second_welfare_theorem_tvs`, if moreover consumption sets are convex,
strictly-better sets are relatively open and every `x a` is an interior point of
`C a`, then `x` is a valuation equilibrium. -/
theorem second_welfare_theorem_tvs_equilibrium {C : α → Set X} {R : α → X → X → Prop}
    {ωbar : X} {x : α → X} (hx : Feasible C ωbar x) (hpo : WeaklyParetoOptimal C R ωbar x)
    (hconv : ∀ a, Convex ℝ (better (C a) (R a) (x a)))
    (hlns : ∀ a, x a ∈ closure (better (C a) (R a) (x a)))
    (hint : (interior (aggBetter C R x)).Nonempty) (hC : ∀ a, Convex ℝ (C a))
    (hopen : ∀ a, ∃ U, IsOpen U ∧ better (C a) (R a) (x a) = U ∩ C a)
    (hxint : ∀ a, x a ∈ interior (C a)) :
    ∃ p : X →L[ℝ] ℝ, p ≠ 0 ∧ IsValuationEquilibrium C R p x := by
  obtain ⟨p, hp0, hq⟩ := second_welfare_theorem_tvs hx hpo hconv hlns hint
  exact ⟨p, hp0, fun a => hq.cost_lt_of_cheaper_point (hC a) (hopen a)
    (exists_cheaper_of_mem_interior (hxint a) hp0)⟩

/-! ### Witness: a toy two-agent economy on `ℓ^∞` -/

open scoped lp ENNReal

/-- The positive cone of `ℓ^∞(ℕ, ℝ)`. -/
def cone : Set ℓ^∞(ℕ, ℝ) := {y | ∀ i, 0 ≤ y i}

/-- Agent `a` (of two) cares only about good `a`: `y ≿ₐ z ↔ z a ≤ y a`. -/
def linftyPref (a : Fin 2) (y z : ℓ^∞(ℕ, ℝ)) : Prop := z (a : ℕ) ≤ y (a : ℕ)

/-- Agent `0` gets one unit of good `0` and nothing else. -/
def linftyX0 : ℓ^∞(ℕ, ℝ) := lp.single ∞ 0 1

/-- The allocation: agent `0` gets `e₀`, agent `1` gets the rest of `ω̄ = 1`. -/
def linftyAlloc : Fin 2 → ℓ^∞(ℕ, ℝ) := ![linftyX0, 1 - linftyX0]

theorem linftyX0_apply (i : ℕ) : linftyX0 i = if i = 0 then 1 else 0 := by
  simp [linftyX0, Pi.single_apply]

theorem linftyAlloc_apply (a : Fin 2) (i : ℕ) :
    linftyAlloc a i = if a = 0 then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1) := by
  fin_cases a
  · simp [linftyAlloc, linftyX0_apply]
  · change (1 - linftyX0 : ℓ^∞(ℕ, ℝ)) i = _
    rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply, linftyX0_apply]
    split_ifs <;> simp_all

theorem better_linfty (a : Fin 2) :
    better cone (linftyPref a) (linftyAlloc a) =
      {y | (∀ i, 0 ≤ y i) ∧ linftyAlloc a (a : ℕ) < y (a : ℕ)} := by
  ext y
  simp only [better, cone, linftyPref, P, mem_ofPred_eq, not_le]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.le, h2⟩

theorem linftyEconomy_feasible : Feasible (fun _ => cone) 1 linftyAlloc := by
  refine ⟨fun a i => ?_, ?_⟩
  · rw [linftyAlloc_apply]; split_ifs <;> norm_num
  · simp [Fin.sum_univ_two, linftyAlloc]

theorem linftyEconomy_weaklyParetoOptimal :
    WeaklyParetoOptimal (fun _ => cone) linftyPref 1 linftyAlloc := by
  rintro ⟨y, ⟨hyC, hsum⟩, hy⟩
  have h0 := (hy 0).1
  have h0' := (hy 0).2
  have hsum0 : y 0 0 + y 1 0 = 1 := by
    have := congrArg (fun f : ℓ^∞(ℕ, ℝ) => f 0) hsum
    simpa [Fin.sum_univ_two, lp.coeFn_add] using this
  have h1 := hyC 1 0
  simp only [linftyPref, linftyAlloc_apply] at h0 h0'
  norm_num at h0'
  linarith

theorem linftyEconomy_convex (a : Fin 2) :
    Convex ℝ (better cone (linftyPref a) (linftyAlloc a)) := by
  rw [better_linfty]
  rintro y ⟨hy1, hy2⟩ z ⟨hz1, hz2⟩ s t hs ht hst
  refine ⟨fun i => ?_, ?_⟩
  · simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hy1 i; have := hz1 i; positivity
  · simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs' | rfl
    · have hc : s * linftyAlloc a a + t * linftyAlloc a a = linftyAlloc a a := by
        rw [← add_mul, hst, one_mul]
      nlinarith [mul_pos hs' (sub_pos.2 hy2), mul_nonneg ht (sub_pos.2 hz2).le]
    · simp only [zero_add] at hst; subst hst; simpa using hz2

theorem linftyEconomy_lns (a : Fin 2) :
    linftyAlloc a ∈ closure (better cone (linftyPref a) (linftyAlloc a)) := by
  have ht : Filter.Tendsto (fun n : ℕ => linftyAlloc a + (1 / ((n : ℝ) + 1)) • (1 : ℓ^∞(ℕ, ℝ)))
      Filter.atTop (nhds (linftyAlloc a)) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (1 : ℓ^∞(ℕ, ℝ))).const_add
      (linftyAlloc a)
    simpa using this
  refine mem_closure_of_tendsto ht (Filter.Eventually.of_forall fun n => ?_)
  rw [better_linfty]
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  refine ⟨fun i => ?_, ?_⟩
  · simp only [lp.coeFn_add, lp.coeFn_smul, lp.infty_coeFn_one, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one]
    have : 0 ≤ linftyAlloc a i := by rw [linftyAlloc_apply]; split_ifs <;> norm_num
    linarith
  · simp only [lp.coeFn_add, lp.coeFn_smul, lp.infty_coeFn_one, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one]
    linarith

/-- Agent `0`'s better set contains the ball of radius `1/2` around `2 · 1`:
the positive cone of `ℓ^∞` has interior points (it would have none in `ℓ^p`,
`p < ∞`). -/
theorem linftyEconomy_interior : (interior (better cone (linftyPref 0) (linftyAlloc 0))).Nonempty := by
  refine ⟨(2 : ℝ) • 1, interior_maximal ?_ Metric.isOpen_ball (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1 / 2))⟩
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hi : ∀ i, |y i - 2| < 1 / 2 := by
    intro i
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero (y - (2 : ℝ) • 1) i
    simp only [lp.coeFn_sub, lp.coeFn_smul, lp.infty_coeFn_one, Pi.sub_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs] at this
    linarith
  rw [better_linfty]
  refine ⟨fun i => ?_, ?_⟩
  · have := abs_lt.1 (hi i); linarith
  · have := abs_lt.1 (hi 0)
    change linftyAlloc 0 0 < y 0
    rw [linftyAlloc_apply]; norm_num; linarith

theorem linftyEconomy_aggBetter_interior :
    (interior (aggBetter (fun _ => cone) linftyPref linftyAlloc)).Nonempty :=
  interior_aggBetter_nonempty (fun b => closure_nonempty_iff.1 ⟨_, linftyEconomy_lns b⟩) 0
    linftyEconomy_interior

/-- The Second Welfare Theorem applies to the `ℓ^∞` economy: there is a nonzero
continuous linear valuation supporting the allocation. -/
theorem linftyEconomy_supported :
    ∃ p : ℓ^∞(ℕ, ℝ) →L[ℝ] ℝ, p ≠ 0 ∧
      IsValuationQuasiEquilibrium (fun _ => cone) linftyPref p linftyAlloc :=
  second_welfare_theorem_tvs linftyEconomy_feasible linftyEconomy_weaklyParetoOptimal
    linftyEconomy_convex linftyEconomy_lns linftyEconomy_aggBetter_interior

/-! ### Witness: a toy economy for the valuation-equilibrium form -/

/-- Evaluation at good `0`, a continuous linear valuation on `ℓ^∞`. -/
def eval0 : ℓ^∞(ℕ, ℝ) →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ 0

theorem eval0_apply (y : ℓ^∞(ℕ, ℝ)) : eval0 y = y 0 := rfl

/-- Both agents care only about good `0`: `y ≿ z ↔ z 0 ≤ y 0`. -/
def commonPref (y z : ℓ^∞(ℕ, ℝ)) : Prop := z 0 ≤ y 0

theorem better_common :
    better (univ : Set ℓ^∞(ℕ, ℝ)) commonPref 0 = eval0 ⁻¹' Ioi 0 := by
  ext y
  simp only [better, commonPref, P, eval0_apply, Set.mem_univ, true_and, not_le,
    mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- Consumption sets: all of `ℓ^∞`. -/
def commonC : Fin 2 → Set ℓ^∞(ℕ, ℝ) := fun _ => univ

/-- The allocation: both agents consume `0`. -/
def commonX : Fin 2 → ℓ^∞(ℕ, ℝ) := 0

theorem commonEconomy_feasible : Feasible commonC 0 commonX :=
  ⟨fun _ => Set.mem_univ _, by simp [commonX]⟩

theorem commonEconomy_weaklyParetoOptimal :
    WeaklyParetoOptimal commonC (fun _ => commonPref) 0 commonX := by
  rintro ⟨y, ⟨-, hsum⟩, hy⟩
  have h0 := (hy 0).2
  have h1 := (hy 1).2
  have hsum0 : y 0 0 + y 1 0 = 0 := by
    have := congrArg (fun f : ℓ^∞(ℕ, ℝ) => f 0) hsum
    simpa [Fin.sum_univ_two, lp.coeFn_add] using this
  simp only [commonPref, commonX, Pi.zero_apply, not_le] at h0 h1
  have : ((0 : ℓ^∞(ℕ, ℝ)) : ℕ → ℝ) 0 = 0 := rfl
  linarith

theorem commonEconomy_lns (a : Fin 2) :
    commonX a ∈ closure (better (commonC a) commonPref (commonX a)) := by
  simp only [commonX, commonC, Pi.zero_apply, better_common]
  have ht : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (1 : ℓ^∞(ℕ, ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (1 : ℓ^∞(ℕ, ℝ))
  refine mem_closure_of_tendsto ht (Filter.Eventually.of_forall fun n => ?_)
  simp only [Set.mem_preimage, Set.mem_Ioi, map_smul, smul_eq_mul, eval0_apply, lp.infty_coeFn_one,
    Pi.one_apply, mul_one]
  positivity

/-- The toy economy satisfies every hypothesis of the valuation-equilibrium
form, so `x = 0` is supported as a valuation equilibrium. -/
theorem commonEconomy_supported :
    ∃ p : ℓ^∞(ℕ, ℝ) →L[ℝ] ℝ, p ≠ 0 ∧
      IsValuationEquilibrium commonC (fun _ => commonPref) p commonX := by
  have hopen : IsOpen (eval0 ⁻¹' Ioi 0) := isOpen_Ioi.preimage eval0.continuous
  have hne : (eval0 ⁻¹' Ioi (0 : ℝ)).Nonempty :=
    ⟨1, by simp [eval0_apply, lp.infty_coeFn_one]⟩
  refine second_welfare_theorem_tvs_equilibrium commonEconomy_feasible
    commonEconomy_weaklyParetoOptimal (fun a => ?_) commonEconomy_lns ?_
    (fun _ => convex_univ) (fun a => ⟨_, hopen, ?_⟩) (fun a => by simp [commonC])
  · simp only [commonX, commonC, Pi.zero_apply, better_common]
    exact (convex_Ioi (0 : ℝ)).linear_preimage (eval0 : ℓ^∞(ℕ, ℝ) →ₗ[ℝ] ℝ)
  · refine interior_aggBetter_nonempty (fun b => ?_) 0 ?_
    · simpa [commonX, commonC, better_common] using hne
    · simpa [commonX, commonC, better_common, hopen.interior_eq] using hne
  · simp [commonX, commonC, better_common]

end ValuationEquilibrium
end Econ
