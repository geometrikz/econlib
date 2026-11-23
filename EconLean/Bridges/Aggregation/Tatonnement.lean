/-
# Tâtonnement stability

PLAN.md §7.2a (bridge B0). MWG §17.H (Prop. 17.H.1); Arrow & Hurwicz (1958),
Arrow, Block & Hurwicz (1959).

**The economics.** Walrasian tâtonnement adjusts prices in the direction of
excess demand: `ṗ = z(p)`. Equilibrium `p*` is globally stable if the squared
distance `V(p) = ‖p − p*‖²` is a Lyapunov function. Along a path,

    V̇ = 2 (p − p*) · z(p) = −2 p* · z(p)       (Walras' law: p · z(p) = 0),

so `V` falls whenever `p* · z(p) > 0`: the equilibrium is "revealed preferred"
to every disequilibrium price (the weak axiom relative to `p*`, MWG 17.H).

Results:
Paths start at `t = 0` and are only required for `t ≥ 0`.

1. `tatonnement_hasDerivWithinAt`: the formula for `V̇`.
2. `tatonnement_norm_const`: Walras' law keeps `∑ pᵢ²` constant along the path.
3. `tatonnement_antitone`, `tatonnement_strictAnti`: under `p* · z(p) > 0` off
   equilibrium, the distance to `p*` never rises, and strictly falls while the
   market is out of equilibrium (MWG Prop. 17.H.1, Lyapunov step only).
4. `GrossSubstitutes.cost_pos_two_goods`: with two goods, gross substitutes,
   homogeneity and Walras' law imply `p* · z(p) > 0` off equilibrium, so the
   result applies unconditionally there.

**Not covered yet.** Convergence of the path to the equilibrium ray (needs a
LaSalle-type compactness argument), existence of the path (an ODE), and the
`p* · z(p) > 0` property under gross substitutes for more than two goods
(Arrow–Block–Hurwicz).
-/
module

public import EconLean.Bridges.Aggregation.GrossSubstitutes
public import EconLean.Bridges.Aggregation.LawOfDemand
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section

namespace Econ

open Finset

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean distance between price vectors. -/
def priceDistSq (p q : ι → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2

/-- A **tâtonnement path** for `z`, started at time `0`: `ṗ(t) = z(p(t))` for all
`t ≥ 0` (one-sided derivative at `t = 0`). Paths are not required to exist for
negative times, which for excess demand that blows up at the boundary would
force the path to be constant. -/
def IsTatonnementPath (z : (ι → ℝ) → (ι → ℝ)) (p : ℝ → ι → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt p (z (p t)) (Set.Ici 0) t

/-- The derivative of `‖p − p*‖²` along a path with velocity `v`, given Walras'
law `p · v = 0`: it is `−2 p* · v`. Within-set version. -/
theorem hasDerivWithinAt_priceDistSq {p : ℝ → ι → ℝ} {v : ι → ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt p v s t) (hW : cost (p t) v = 0) (pstar : ι → ℝ) :
    HasDerivWithinAt (fun s => priceDistSq (p s) pstar) (-2 * cost pstar v) s t := by
  have hi : ∀ i, HasDerivWithinAt (fun s => p s i) (v i) s t := hasDerivWithinAt_pi.1 h
  have hsum : HasDerivWithinAt (fun s => ∑ i, (p s i - pstar i) ^ 2)
      (∑ i, 2 * (p t i - pstar i) * v i) s t := by
    have := HasDerivWithinAt.fun_sum (u := Finset.univ)
      (fun i _ => ((hi i).sub_const (pstar i)).pow 2)
    simpa using this
  show HasDerivWithinAt (fun s => ∑ i, (p s i - pstar i) ^ 2) _ s t
  refine hsum.congr_deriv ?_
  simp only [cost] at hW ⊢
  have : ∑ i, 2 * (p t i - pstar i) * v i
      = 2 * ∑ i, p t i * v i - 2 * ∑ i, pstar i * v i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hW]; ring

/-- **The Lyapunov derivative.** Along a tâtonnement path on which Walras' law
holds, `d/dt ‖p(t) − p*‖² = −2 p* · z(p(t))` for `t ≥ 0`. -/
theorem tatonnement_hasDerivWithinAt {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0)
    (pstar : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => priceDistSq (p s) pstar) (-2 * cost pstar (z (p t)))
      (Set.Ici 0) t :=
  hasDerivWithinAt_priceDistSq (hpath t ht) (hW t ht) pstar

/-- Common step: on `[0, ∞)` the Lyapunov function is continuous, and for `t > 0`
its derivative is `−2 p* · z(p(t))`. -/
theorem tatonnement_deriv {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0)
    (pstar : ι → ℝ) :
    ContinuousOn (fun s => priceDistSq (p s) pstar) (Set.Ici 0) ∧
      ∀ t ∈ interior (Set.Ici (0 : ℝ)),
        HasDerivAt (fun s => priceDistSq (p s) pstar) (-2 * cost pstar (z (p t))) t := by
  refine ⟨fun t ht => (tatonnement_hasDerivWithinAt hpath hW pstar ht).continuousWithinAt,
    fun t ht => ?_⟩
  rw [interior_Ici] at ht
  exact (tatonnement_hasDerivWithinAt hpath hW pstar (le_of_lt ht)).hasDerivAt
    (Ici_mem_nhds ht)

/-- **Walras' law conserves the norm** of the price vector along tâtonnement:
`d/dt ∑ pᵢ² = 2 p · z(p) = 0`, so `∑ pᵢ(t)² = ∑ pᵢ(0)²` for `t ≥ 0`. -/
theorem tatonnement_norm_const {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0) {t : ℝ}
    (ht : 0 ≤ t) : priceDistSq (p t) 0 = priceDistSq (p 0) 0 := by
  obtain ⟨hc, hd⟩ := tatonnement_deriv hpath hW 0
  have hd0 : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      deriv (fun s => priceDistSq (p s) 0) x = 0 := fun x hx => by
    rw [(hd x hx).deriv]; simp [cost]
  have hdiff : DifferentiableOn ℝ (fun s => priceDistSq (p s) 0) (interior (Set.Ici 0)) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have h1 := antitoneOn_of_deriv_nonpos (convex_Ici 0) hc hdiff fun x hx => (hd0 x hx).le
  have h2 := monotoneOn_of_deriv_nonneg (convex_Ici 0) hc hdiff fun x hx => (hd0 x hx).ge
  exact le_antisymm (h1 (Set.mem_Ici.2 le_rfl) ht ht) (h2 (Set.mem_Ici.2 le_rfl) ht ht)

/-- **Tâtonnement: Lyapunov monotonicity** (the Lyapunov step of MWG Prop.
17.H.1). Suppose Walras' law holds along the path for `t ≥ 0`, and the
equilibrium `p*` satisfies `p* · z(p(t)) > 0` whenever `z(p(t)) ≠ 0` (the weak
axiom relative to `p*`). Then the distance from `p(t)` to `p*` never increases
on `[0, ∞)`. Convergence is not claimed. -/
theorem tatonnement_antitone {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ} {pstar : ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0)
    (hWA : ∀ t, 0 ≤ t → z (p t) ≠ 0 → 0 < cost pstar (z (p t))) :
    AntitoneOn (fun t => priceDistSq (p t) pstar) (Set.Ici 0) := by
  obtain ⟨hc, hd⟩ := tatonnement_deriv hpath hW pstar
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hc
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) fun t ht => ?_
  rw [(hd t ht).deriv]
  have ht0 : 0 ≤ t := by rw [interior_Ici] at ht; exact le_of_lt ht
  by_cases hz : z (p t) = 0
  · simp [hz, cost]
  · linarith [hWA t ht0 hz]

/-- **Strict decrease out of equilibrium.** If moreover the path is out of
equilibrium at every `t > 0`, the distance to `p*` is strictly decreasing on
`[0, ∞)`. -/
theorem tatonnement_strictAnti {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ} {pstar : ι → ℝ}
    (hpath : IsTatonnementPath z p) (hW : ∀ t, 0 ≤ t → cost (p t) (z (p t)) = 0)
    (hWA : ∀ t, 0 ≤ t → z (p t) ≠ 0 → 0 < cost pstar (z (p t)))
    (hne : ∀ t, 0 < t → z (p t) ≠ 0) :
    StrictAntiOn (fun t => priceDistSq (p t) pstar) (Set.Ici 0) := by
  obtain ⟨hc, hd⟩ := tatonnement_deriv hpath hW pstar
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) hc fun t ht => ?_
  rw [(hd t ht).deriv]
  rw [interior_Ici] at ht
  linarith [hWA t (le_of_lt ht) (hne t ht)]

/-! ### Two goods: gross substitutes gives `p* · z(p) > 0` -/

variable [DecidableEq ι]

/-- Helper: with two goods `k ≠ j` and `qₖ/p*ₖ < qⱼ/p*ⱼ`, gross substitutes,
homogeneity and Walras' law give `p* · z(q) > 0`. -/
theorem GrossSubstitutes.cost_pos_of_ratio_lt {z : (ι → ℝ) → (ι → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) {pstar q : ι → ℝ}
    (hps : PositivePrices pstar) (hq : PositivePrices q) (hzs : z pstar = 0)
    (hWq : cost q (z q) = 0) {k j : ι} (hkj : k ≠ j) (huniv : (Finset.univ : Finset ι) = {k, j})
    (hr : q k / pstar k < q j / pstar j) : 0 < cost pstar (z q) := by
  set c := q k / pstar k with hc
  have hc0 : 0 < c := div_pos (hq k) (hps k)
  set q' := c • pstar with hq'
  have hq'pos : PositivePrices q' := fun i => by
    simp only [hq', Pi.smul_apply, smul_eq_mul]; exact mul_pos hc0 (hps i)
  have hzq' : z q' = 0 := by rw [hq', hhom pstar hps c hc0, hzs]
  have hk : q' k = q k := by
    simp only [hq', Pi.smul_apply, smul_eq_mul, hc]; field_simp [(hps k).ne']
  have hjlt : q' j < q j := by
    simp only [hq', Pi.smul_apply, smul_eq_mul]
    rw [lt_div_iff₀ (hps j)] at hr
    calc c * pstar j < q j := by rw [hc] at hr ⊢; linarith
      _ = q j := rfl
  have hle : q' ≤ q := by
    intro i
    have hi : i = k ∨ i = j := by
      have := Finset.mem_univ i; rw [huniv] at this; simpa using this
    rcases hi with rfl | rfl
    · exact hk.le
    · exact hjlt.le
  have hne : q' ≠ q := fun h => hjlt.ne (by rw [h])
  have hzk : 0 < z q k := by
    have := hGS.lt_of_le hq'pos hle hne hk
    rwa [hzq'] at this
  -- Walras' law at `q` pins down `z_j`.
  have hsum : ∀ x : ι → ℝ, cost x (z q) = x k * z q k + x j * z q j := fun x => by
    simp only [cost, huniv, Finset.sum_pair hkj]
  rw [hsum] at hWq ⊢
  have hzj : z q j = -(q k * z q k) / q j := by
    field_simp [(hq j).ne']; linarith
  rw [hzj]
  have hqk : q k = c * pstar k := by rw [hc]; field_simp [(hps k).ne']
  have key : pstar k * z q k + pstar j * (-(q k * z q k) / q j)
      = pstar k * z q k * (1 - c * pstar j / q j) := by
    rw [hqk]; field_simp [(hq j).ne']; ring
  rw [key]
  have hlt1 : c * pstar j / q j < 1 := by
    rw [div_lt_one (hq j)]; linarith [hjlt, show q' j = c * pstar j by simp [hq']]
  exact mul_pos (mul_pos (hps k) hzk) (by linarith)

/-- **Two goods: gross substitutes implies the weak axiom relative to the
equilibrium.** If `z` is gross substitute, homogeneous of degree zero and
satisfies Walras' law on positive prices, and `p* ≫ 0` is an equilibrium, then
`p* · z(q) > 0` at every positive `q` with `z(q) ≠ 0`. -/
theorem GrossSubstitutes.cost_pos_two_goods {z : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z)
    (hW : ∀ q, PositivePrices q → cost q (z q) = 0) {pstar q : Fin 2 → ℝ}
    (hps : PositivePrices pstar) (hq : PositivePrices q) (hzs : z pstar = 0) (hzq : z q ≠ 0) :
    0 < cost pstar (z q) := by
  have hu01 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hu10 : (Finset.univ : Finset (Fin 2)) = {1, 0} := by decide
  rcases lt_trichotomy (q 0 / pstar 0) (q 1 / pstar 1) with h | h | h
  · exact hGS.cost_pos_of_ratio_lt hhom hps hq hzs (hW q hq) (by decide) hu01 h
  · -- Equal ratios: `q` is a multiple of `p*`, so `z(q) = 0`.
    exfalso; apply hzq
    set c := q 0 / pstar 0
    have hc0 : 0 < c := div_pos (hq 0) (hps 0)
    have hqc : q = c • pstar := by
      funext i
      fin_cases i
      · simp [c]; field_simp [(hps 0).ne']
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, h]
        field_simp [(hps 1).ne']
    rw [hqc, hhom pstar hps c hc0, hzs]
  · exact hGS.cost_pos_of_ratio_lt hhom hps hq hzs (hW q hq) (by decide) hu10 h

end Econ
