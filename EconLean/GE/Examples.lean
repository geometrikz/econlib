/-
# Worked examples and non-vacuity witnesses for the general-equilibrium files

PLAN.md §8.2 (Layer 2): every headline theorem gets a concrete object that
satisfies *all* its hypotheses, so we know the hypotheses are not
contradictory and the theorem is not vacuously true.

1. **Linear 2×2 economy.** Two consumers, two goods, utility `u(x) = x₀ + x₁`
   (perfect substitutes), endowments `(1, 2)` and `(2, 1)`. At prices `(1, 1)`
   the endowment allocation is a Walrasian equilibrium. Every hypothesis of the
   First Welfare Theorem, the core theorem and the textbook Second Welfare
   Theorem holds, and we apply each one.
2. **A blocked allocation.** Giving everything to consumer 0 is not in the
   core: consumer 1 alone blocks it. So `Blocks` is not an empty notion.
3. **Leontief 2×2 economy.** Utility `u(x) = min(x₀, x₁)`, same endowments.
   Demand `(w, w)` is defined and continuous on the *whole* price simplex
   (including zero prices), so every hypothesis of the two-good existence
   theorem holds.
-/
module

public import EconLean.GE.SecondWelfare
public import EconLean.GE.Existence

@[expose] public section

namespace Econ

namespace GEExamples

open ExchangeEconomy

/-! ### Shared data -/

/-- Endowments: consumer 0 owns `(1, 2)`, consumer 1 owns `(2, 1)`. -/
def endow₂ : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![2, 1]]

theorem endow₂_nonneg : ∀ a, 0 ≤ endow₂ a := by
  intro a i
  fin_cases a <;> fin_cases i <;> simp [endow₂]

theorem endow₂_pos : ∀ a i, 0 < endow₂ a i := by
  intro a i
  fin_cases a <;> fin_cases i <;> simp [endow₂]

/-! ### 1. Perfect substitutes -/

/-- Perfect-substitutes utility `u(x) = x₀ + x₁`. -/
def uLin (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- The linear exchange economy. -/
def linEconomy : ExchangeEconomy (Fin 2) (Fin 2) where
  pref _ := prefOf uLin
  endow := endow₂
  endow_nonneg := endow₂_nonneg

/-- Prices `(1, 1)`. -/
def pOne : Fin 2 → ℝ := fun _ => 1

theorem cost_pOne (x : Fin 2 → ℝ) : cost pOne x = uLin x := by
  simp [cost, pOne, uLin, Fin.sum_univ_two]

theorem continuous_uLin : Continuous uLin := by
  unfold uLin; fun_prop

theorem rational_lin : ∀ a, Rational (linEconomy.pref a) :=
  fun _ => (represents_prefOf uLin).rational

theorem stronglyMonotone_lin : ∀ a, StronglyMonotone (linEconomy.pref a) := by
  intro a x y _ hxy hne
  -- `u x < u y`: weakly larger in both goods, and not equal.
  have hlt : uLin x < uLin y := by
    have h0 := hxy 0
    have h1 := hxy 1
    by_contra hle
    push Not at hle
    apply hne
    funext i
    fin_cases i
    · simp only [uLin] at hle; show x 0 = y 0; linarith
    · simp only [uLin] at hle; show x 1 = y 1; linarith
  exact ⟨hlt.le, not_le.2 hlt⟩

theorem lns_lin : ∀ a, LocallyNonsatiated (linEconomy.pref a) :=
  fun a => (stronglyMonotone_lin a).locallyNonsatiated

theorem continuousPref_lin : ∀ a, ContinuousPref (linEconomy.pref a) :=
  fun _ => continuousPref_prefOf continuous_uLin

theorem convexPref_lin : ∀ a, ConvexPref (linEconomy.pref a) := by
  intro a x y₁ h₁ y₂ h₂ s t hs ht hst
  -- `u` is linear, so `u(s y₁ + t y₂) = s u(y₁) + t u(y₂) ≥ (s + t) u(x)`.
  show uLin x ≤ uLin (s • y₁ + t • y₂)
  have h₁' : uLin x ≤ uLin y₁ := h₁
  have h₂' : uLin x ≤ uLin y₂ := h₂
  have : uLin (s • y₁ + t • y₂) = s * uLin y₁ + t * uLin y₂ := by
    simp only [uLin, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]
  have := mul_le_mul_of_nonneg_left h₁' hs
  have := mul_le_mul_of_nonneg_left h₂' ht
  have hx : uLin x = s * uLin x + t * uLin x := by rw [← add_mul, hst, one_mul]
  linarith

/-- At prices `(1, 1)` the endowment allocation is a Walrasian equilibrium:
the endowment is on the budget line, and every affordable bundle has
`u(y) = p · y ≤ p · ωₐ = u(ωₐ)`. -/
theorem linEconomy_eq : linEconomy.IsWalrasianEquilibrium pOne endow₂ := by
  refine ⟨fun a => ⟨⟨endow₂_nonneg a, le_rfl⟩, fun y hy => ?_⟩, rfl⟩
  show uLin y ≤ uLin (endow₂ a)
  rw [← cost_pOne, ← cost_pOne]
  exact hy.2

/-- First Welfare Theorem applies: the equilibrium allocation is Pareto
optimal. -/
theorem linEconomy_paretoOptimal : linEconomy.ParetoOptimal endow₂ :=
  first_welfare_theorem rational_lin lns_lin linEconomy_eq

/-- Core theorem applies. -/
example : linEconomy.InCore endow₂ := linEconomy_eq.inCore

/-- Second Welfare Theorem (textbook form) applies: all of its hypotheses hold
for this economy and this Pareto optimum. -/
example : ∃ p : Fin 2 → ℝ, p ≠ 0 ∧ 0 ≤ p ∧
    linEconomy.IsPriceEquilibriumWithTransfers p (fun a => cost p (endow₂ a)) endow₂ ∧
    ∀ a, endow₂ a ∈ demand (linEconomy.pref a) p (cost p (endow₂ a)) :=
  second_welfare_theorem_demand rational_lin stronglyMonotone_lin continuousPref_lin
    convexPref_lin linEconomy_paretoOptimal endow₂_pos

/-! ### 1b. A non-degenerate economy: different tastes

In `linEconomy` every feasible allocation is Pareto optimal (total utility is
always 6), so the First Welfare Theorem is tested only weakly there. Here
consumer 0 has `u₀ = 2x₀ + x₁` and consumer 1 has `u₁ = x₀ + 2x₁`. At prices
`(1, 1)` each buys only their favourite good: `x* = ((3, 0), (0, 3))` is a
Walrasian equilibrium, it is Pareto optimal by the First Welfare Theorem, and
the endowment allocation is **not** Pareto optimal (`x*` dominates it). -/

/-- Taste weights: row `a` is consumer `a`'s marginal utilities. -/
def wt : Fin 2 → Fin 2 → ℝ := ![![2, 1], ![1, 2]]

/-- Consumer `a`'s linear utility `u_a(x) = wt a 0 · x₀ + wt a 1 · x₁`. -/
def uAsym (a : Fin 2) (x : Fin 2 → ℝ) : ℝ := wt a 0 * x 0 + wt a 1 * x 1

/-- The economy with different tastes. -/
def asymEconomy : ExchangeEconomy (Fin 2) (Fin 2) where
  pref a := prefOf (uAsym a)
  endow := endow₂
  endow_nonneg := endow₂_nonneg

/-- The equilibrium allocation: each consumer gets 3 units of their favourite good. -/
def xStar : Allocation (Fin 2) (Fin 2) := ![![3, 0], ![0, 3]]

theorem rational_asym : ∀ a, Rational (asymEconomy.pref a) :=
  fun a => (represents_prefOf (uAsym a)).rational

theorem stronglyMonotone_asym : ∀ a, StronglyMonotone (asymEconomy.pref a) := by
  intro a x y _ hxy hne
  have hw0 : 0 < wt a 0 := by fin_cases a <;> simp [wt]
  have hw1 : 0 < wt a 1 := by fin_cases a <;> simp [wt]
  have hlt : uAsym a x < uAsym a y := by
    have h0 := hxy 0
    have h1 := hxy 1
    by_contra hle
    push Not at hle
    simp only [uAsym] at hle
    have e0 : x 0 = y 0 := by nlinarith
    have e1 : x 1 = y 1 := by nlinarith
    apply hne
    funext i
    fin_cases i
    · exact e0
    · exact e1
  exact ⟨hlt.le, not_le.2 hlt⟩

theorem lns_asym : ∀ a, LocallyNonsatiated (asymEconomy.pref a) :=
  fun a => (stronglyMonotone_asym a).locallyNonsatiated

/-- `((3, 0), (0, 3))` at prices `(1, 1)` is a Walrasian equilibrium: each
consumer has wealth 3 and `u_a(y) ≤ 2 (y₀ + y₁) ≤ 6 = u_a(x*_a)` on the budget set. -/
theorem asymEconomy_eq : asymEconomy.IsWalrasianEquilibrium pOne xStar := by
  refine ⟨fun a => ⟨⟨?_, ?_⟩, fun y hy => ?_⟩, ?_⟩
  · intro i; fin_cases a <;> fin_cases i <;> simp [xStar]
  · fin_cases a <;> simp [cost, pOne, xStar, wealth, asymEconomy, endow₂, Fin.sum_univ_two] <;>
      norm_num
  · have hb : y 0 + y 1 ≤ 3 := by
      have := hy.2
      fin_cases a <;>
        simp [cost, pOne, wealth, asymEconomy, endow₂, Fin.sum_univ_two] at this <;> linarith
    have h0 : 0 ≤ y 0 := hy.1 0
    have h1 : 0 ≤ y 1 := hy.1 1
    show uAsym a y ≤ uAsym a (xStar a)
    fin_cases a <;> simp [uAsym, wt, xStar] <;> linarith
  · funext i
    fin_cases i <;> simp [xStar, totalEndowment, asymEconomy, endow₂, Fin.sum_univ_two] <;>
      norm_num

/-- First Welfare Theorem in a non-degenerate economy. -/
theorem asymEconomy_paretoOptimal : asymEconomy.ParetoOptimal xStar :=
  first_welfare_theorem rational_asym lns_asym asymEconomy_eq

/-- The no-trade allocation is not Pareto optimal here, so Pareto optimality is
a real restriction in this economy (each consumer goes from utility 4 to 6). -/
theorem not_paretoOptimal_endow : ¬ asymEconomy.ParetoOptimal endow₂ := by
  intro h
  refine h.2 xStar asymEconomy_eq.feasible ⟨fun a => ?_, 0, ?_⟩
  · show uAsym a (endow₂ a) ≤ uAsym a (xStar a)
    fin_cases a <;> simp [uAsym, wt, xStar, endow₂] <;> norm_num
  · refine ⟨?_, ?_⟩ <;> simp [asymEconomy, prefOf, uAsym, wt, xStar, endow₂] <;> norm_num

/-! ### 2. A blocked allocation -/

/-- Everything goes to consumer 0. -/
def allToZero : Allocation (Fin 2) (Fin 2) := ![![3, 3], 0]

/-- Consumer 1 alone blocks `allToZero` by keeping their endowment, so it is
not in the core. -/
theorem not_inCore_allToZero : ¬ linEconomy.InCore allToZero := by
  intro h
  refine h.2 {1} ⟨Finset.singleton_nonempty 1, endow₂, fun b _ => endow₂_nonneg b, rfl, ?_⟩
  intro b hb
  rw [Finset.mem_singleton.1 hb]
  -- `u(0) = 0 < 3 = u(ω₁)`.
  refine ⟨?_, ?_⟩ <;> simp [linEconomy, prefOf, uLin, allToZero, endow₂] <;> norm_num

/-! ### 3. Leontief preferences: existence witness -/

/-- Leontief utility `u(x) = min(x₀, x₁)` (perfect complements). -/
noncomputable def uLeon (x : Fin 2 → ℝ) : ℝ := min (x 0) (x 1)

/-- The Leontief exchange economy. -/
noncomputable def leonEconomy : ExchangeEconomy (Fin 2) (Fin 2) where
  pref _ := prefOf uLeon
  endow := endow₂
  endow_nonneg := endow₂_nonneg

/-- Leontief preferences are locally nonsatiated (though not strongly
monotone): add `ε/2` of both goods. -/
theorem lns_leon : ∀ a, LocallyNonsatiated (leonEconomy.pref a) := by
  intro a x hx ε hε
  refine ⟨x + fun _ => ε / 2, fun i => ?_, ?_, ?_⟩
  · have := hx i
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
    linarith
  · rw [dist_pi_lt_iff hε]
    intro i
    simp only [Pi.add_apply, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  · have hu : uLeon (x + fun _ => ε / 2) = uLeon x + ε / 2 := by
      simp [uLeon, min_add_add_right]
    have hlt : uLeon x < uLeon (x + fun _ => ε / 2) := by
      rw [hu]; linarith
    exact ⟨hlt.le, not_le.2 hlt⟩

/-- The Leontief demand selection: spend wealth on equal amounts `(w, w)` of
both goods (`p₀ + p₁ = 1` on the simplex). -/
noncomputable def dLeon (a : Fin 2) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun _ => leonEconomy.wealth p a

theorem dLeon_demand :
    leonEconomy.IsDemandSelection dLeon (priceSimplex (Fin 2)) := by
  intro p hp a
  have hsum : p 0 + p 1 = 1 := by simpa [Fin.sum_univ_two] using hp.2
  set w := leonEconomy.wealth p a with hw
  have hw0 : 0 ≤ w := cost_nonneg hp.1 (endow₂_nonneg a)
  refine ⟨⟨fun _ => hw0, ?_⟩, fun y hy => ?_⟩
  · -- `p · (w, w) = w (p₀ + p₁) = w`.
    simp only [dLeon, cost, Fin.sum_univ_two, ← hw]
    nlinarith
  · -- `min(y₀, y₁) (p₀ + p₁) ≤ p · y ≤ w`, so `u(y) ≤ w = u(w, w)`.
    show uLeon y ≤ uLeon (dLeon a p)
    have hcost : p 0 * y 0 + p 1 * y 1 ≤ w := by
      simpa [cost, Fin.sum_univ_two] using hy.2
    have h0 : uLeon y ≤ y 0 := min_le_left _ _
    have h1 : uLeon y ≤ y 1 := min_le_right _ _
    have hp0 := hp.1 0
    have hp1 := hp.1 1
    have h0' := mul_le_mul_of_nonneg_left h0 hp0
    have h1' := mul_le_mul_of_nonneg_left h1 hp1
    have : uLeon y ≤ w := by
      have : uLeon y = p 0 * uLeon y + p 1 * uLeon y := by rw [← add_mul, hsum, one_mul]
      linarith
    simpa [uLeon, dLeon, ← hw] using this

theorem dLeon_continuous : ∀ a, ContinuousOn (dLeon a) (priceSimplex (Fin 2)) := by
  intro a
  refine Continuous.continuousOn (continuous_pi fun _ => ?_)
  simp only [dLeon, wealth, cost]
  fun_prop

/-- The two-good existence theorem applies to the Leontief economy. -/
example : ∃ p ∈ priceSimplex (Fin 2),
    leonEconomy.IsFreeDisposalEquilibrium p (fun a => dLeon a p) :=
  exists_freeDisposalEquilibrium_two_goods lns_leon dLeon_demand dLeon_continuous

end GEExamples

end Econ
