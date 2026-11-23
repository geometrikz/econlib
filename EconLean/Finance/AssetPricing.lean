/-
# Finite-state asset pricing: no arbitrage, state prices, complete markets

Duffie, *Dynamic Asset Pricing Theory*, ch. 1; Cochrane, *Asset Pricing*,
ch. 4; LeRoy–Werner, *Principles of Financial Economics*, ch. 6–9; Ross (1976),
Harrison–Kreps (1979).

**Setup.** There are finitely many states `s ∈ σ` tomorrow and finitely many
assets `i ∈ ι`. Asset `i` costs `q_i` today and pays `X_{s i}` in state `s`. A
portfolio `h` costs `q · h` and pays `(X h)_s = Σᵢ X_{s i} h_i`.

* An **arbitrage** is a portfolio with a non-negative payoff in every state
  that costs nothing or less, and either costs strictly less than zero or pays
  strictly positive in some state (`IsArbitrage`).
* A **state-price vector** is `m ≫ 0` with `q_i = Σ_s m_s X_{s i}` for every
  asset (`IsStatePrice`). Given probabilities `π ≫ 0`, `M_s = m_s / π_s` is a
  strictly positive **stochastic discount factor**: `q_i = E[M X_i]`.
* Markets are **complete** if every state-contingent payoff `z ∈ ℝ^σ` is the
  payoff of some portfolio (`Complete`).

**Results.**
* `ftap` (fundamental theorem of asset pricing): there is no arbitrage iff a
  strictly positive state-price vector exists.
* `ftap_sdf`: equivalently, for any strictly positive weights `π` (in
  particular any full-support probability measure), a strictly positive SDF
  prices every asset. This is a rescaling `M = m/π` of `ftap`.
* `complete_iff_unique`: under no arbitrage, markets are complete iff the
  state-price vector is unique.

**The Lean.** The hard direction of `ftap` (Stiemke's lemma) separates the
compact simplex in `ℝ^{1+σ}` from the subspace `{(−q·h, Xh)}` with Mathlib's
geometric Hahn–Banach theorem. The separating functional must vanish on the
subspace and is strictly negative on every vertex of the simplex. Its
coefficients, normalized, are the state prices.
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

namespace Econ
namespace AssetPricing

open Finset

/-- A one-period market: payoff matrix `X s i` and prices `q i`. -/
structure Market (σ ι : Type*) where
  /-- Payoff of asset `i` in state `s`. -/
  X : σ → ι → ℝ
  /-- Price of asset `i`. -/
  q : ι → ℝ

namespace Market

variable {σ ι : Type*} [Fintype σ] [Fintype ι] (M : Market σ ι)

/-- Payoff of portfolio `h` in state `s`. -/
def payoff (h : ι → ℝ) (s : σ) : ℝ := ∑ i, M.X s i * h i

/-- Cost of portfolio `h`. -/
def cost (h : ι → ℝ) : ℝ := ∑ i, M.q i * h i

/-- `h` is an **arbitrage**: non-negative payoff, non-positive cost, and either
negative cost or a strictly positive payoff in some state. -/
def IsArbitrage (h : ι → ℝ) : Prop :=
  (∀ s, 0 ≤ M.payoff h s) ∧ M.cost h ≤ 0 ∧ (M.cost h < 0 ∨ ∃ s, 0 < M.payoff h s)

/-- **No arbitrage.** -/
def NoArbitrage : Prop := ∀ h, ¬ M.IsArbitrage h

/-- `m` is a **strictly positive state-price vector**. -/
def IsStatePrice (m : σ → ℝ) : Prop := (∀ s, 0 < m s) ∧ ∀ i, M.q i = ∑ s, m s * M.X s i

/-- **Complete markets:** every payoff `z ∈ ℝ^σ` is spanned by some portfolio. -/
def Complete : Prop := ∀ z : σ → ℝ, ∃ h, M.payoff h = z

/-- With state prices `m`, the cost of any portfolio is `Σ_s m_s (Xh)_s`. -/
theorem cost_eq {m : σ → ℝ} (hm : M.IsStatePrice m) (h : ι → ℝ) :
    M.cost h = ∑ s, m s * M.payoff h s := by
  simp only [cost, payoff, hm.2, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- Unit vectors in `ℝ^J`. -/
private def unit {J : Type*} [DecidableEq J] (j : J) : J → ℝ := fun k => if j = k then 1 else 0

/-- The map `h ↦ (−q·h, Xh)` into `ℝ^{1+σ}`. -/
private def embed : (ι → ℝ) →ₗ[ℝ] (Option σ → ℝ) where
  toFun h o := match o with
    | none => -M.cost h
    | some s => M.payoff h s
  map_add' h k := by
    funext o; cases o <;> simp [cost, payoff, mul_add, sum_add_distrib]; ring
  map_smul' c h := by
    funext o; cases o <;> simp [cost, payoff, mul_sum] <;> exact sum_congr rfl fun _ _ => by ring

/-- **The fundamental theorem of asset pricing.** There is no arbitrage iff
there is a strictly positive state-price vector. -/
theorem ftap : M.NoArbitrage ↔ ∃ m, M.IsStatePrice m := by
  classical
  constructor
  · intro hna
    set Φ := embed M
    set S : Set (Option σ → ℝ) := convexHull ℝ (Set.range fun j => unit j)
    set T : Set (Option σ → ℝ) := (LinearMap.range Φ : Set (Option σ → ℝ))
    -- the simplex lies in `{z ≥ 0, Σ z = 1}`
    have hS : ∀ z ∈ S, (∀ j, 0 ≤ z j) ∧ ∑ j, z j = 1 := by
      intro z hz
      refine (convexHull_min ?_ ?_ : S ⊆ {z | (∀ j, 0 ≤ z j) ∧ ∑ j, z j = 1}) hz
      · rintro _ ⟨j, rfl⟩
        refine ⟨fun k => by show (0 : ℝ) ≤ if j = k then 1 else 0; split_ifs <;> norm_num, ?_⟩
        simp [unit]
      · intro x hx y hy a b ha hb hab
        refine ⟨fun j => ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
            hx.2, hy.2]
          linarith
    have hdisj : Disjoint S T := by
      rw [Set.disjoint_left]
      rintro z hzS ⟨h, rfl⟩
      obtain ⟨hnn, hsum⟩ := hS _ hzS
      apply hna h
      have hc : M.cost h ≤ 0 := by have := hnn none; simp [Φ, embed] at this; linarith
      refine ⟨fun s => by simpa [Φ, embed] using hnn (some s), hc, ?_⟩
      by_contra hno
      push Not at hno
      have hz : ∀ j, Φ h j = 0 := by
        intro j; cases j with
        | none => have := hnn none; simp only [Φ, embed, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
                  linarith [hno.1]
        | some s => exact le_antisymm (by simpa [Φ, embed] using hno.2 s) (hnn (some s))
      simp [hz] at hsum
    obtain ⟨f, u, v, hfS, huv, hfT⟩ := geometric_hahn_banach_compact_closed (convex_convexHull ℝ _)
      ((Set.finite_range fun j => unit j).isCompact_convexHull (𝕜 := ℝ)) (LinearMap.range Φ).convex
      (Submodule.isClosed_of_finiteDimensional _) hdisj
    have hv : v < 0 := by simpa using hfT 0 (LinearMap.range Φ).zero_mem
    have hf0 : ∀ h, f (Φ h) = 0 := by
      intro h
      by_contra hne
      have := hfT ((v / f (Φ h)) • Φ h) ((LinearMap.range Φ).smul_mem _ ⟨h, rfl⟩)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      exact lt_irrefl _ this
    have hneg : ∀ j, f (unit j) < 0 := fun j =>
      (hfS _ (subset_convexHull ℝ _ ⟨j, rfl⟩)).trans (huv.trans hv)
    set w : Option σ → ℝ := fun j => -f (unit j)
    have hw : ∀ j, 0 < w j := fun j => neg_pos.2 (hneg j)
    have hexp : ∀ h, w none * M.cost h = ∑ s, w (some s) * M.payoff h s := by
      intro h
      have := hf0 h
      have hpi := (f : (Option σ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ (Φ h)
      simp only [ContinuousLinearMap.coe_coe] at hpi
      rw [hpi, Fintype.sum_option] at this
      simp only [Φ, embed, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at this
      simp only [w]
      have e : ∀ s, (fun k => if (some s : Option σ) = k then (1 : ℝ) else 0) = unit (some s) :=
        fun _ => rfl
      have e0 : (fun k => if (none : Option σ) = k then (1 : ℝ) else 0) = unit none := rfl
      simp only [e, e0] at this
      rw [← sub_eq_zero, ← this]
      have e2 : ∑ x, -f (unit (some x)) * M.payoff h x = -∑ x, M.payoff h x * f (unit (some x)) := by
        rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring
      rw [e2]; ring
    refine ⟨fun s => w (some s) / w none, fun s => div_pos (hw _) (hw _), fun i => ?_⟩
    have := hexp (unit i)
    have hc : M.cost (unit i) = M.q i := by
      simp [cost, unit]
    have hp : ∀ s, M.payoff (unit i) s = M.X s i := fun s => by simp [payoff, unit]
    rw [hc] at this
    simp only [hp] at this
    show M.q i = ∑ s, w (some s) / w none * M.X s i
    have e : ∑ s, w (some s) / w none * M.X s i = (∑ s, w (some s) * M.X s i) / w none := by
      rw [sum_div]; exact sum_congr rfl fun _ _ => by ring
    rw [e, ← this]
    field_simp [(hw none).ne']
  · rintro ⟨m, hm⟩ h ⟨hnn, hc, hpos⟩
    have hce := M.cost_eq hm h
    have hge : 0 ≤ M.cost h := hce ▸ sum_nonneg fun s _ => mul_nonneg (hm.1 s).le (hnn s)
    rcases hpos with hlt | ⟨s, hs⟩
    · linarith
    · have : 0 < M.cost h := by
        rw [hce]
        exact sum_pos' (fun t _ => mul_nonneg (hm.1 t).le (hnn t))
          ⟨s, mem_univ s, mul_pos (hm.1 s) hs⟩
      linarith

/-- **FTAP with a stochastic discount factor.** For any strictly positive
probabilities `π`, there is no arbitrage iff some strictly positive SDF `M`
prices every asset: `q_i = Σ_s π_s M_s X_{s i} = E[M X_i]`. -/
theorem ftap_sdf {π : σ → ℝ} (hπ : ∀ s, 0 < π s) :
    M.NoArbitrage ↔ ∃ D : σ → ℝ, (∀ s, 0 < D s) ∧ ∀ i, M.q i = ∑ s, π s * D s * M.X s i := by
  rw [ftap]
  constructor
  · rintro ⟨m, hm0, hm⟩
    refine ⟨fun s => m s / π s, fun s => div_pos (hm0 s) (hπ s), fun i => ?_⟩
    rw [hm i]
    exact sum_congr rfl fun s _ => by field_simp [(hπ s).ne']
  · rintro ⟨D, hD0, hD⟩
    exact ⟨fun s => π s * D s, fun s => mul_pos (hπ s) (hD0 s), hD⟩

/-- **Complete markets ⟺ unique state prices** (under no arbitrage). -/
theorem complete_iff_unique (hna : M.NoArbitrage) : M.Complete ↔ ∃! m, M.IsStatePrice m := by
  classical
  obtain ⟨m, hm⟩ := (M.ftap).1 hna
  constructor
  · intro hc
    refine ⟨m, hm, fun m' hm' => ?_⟩
    obtain ⟨h, hh⟩ := hc (fun s => m' s - m s)
    have h0 : ∑ s, (m' s - m s) * M.payoff h s = 0 := by
      have := (M.cost_eq hm h).symm.trans (M.cost_eq hm' h)
      rw [← sub_eq_zero] at this
      have e : ∑ s, (m' s - m s) * M.payoff h s =
          ∑ s, m' s * M.payoff h s - ∑ s, m s * M.payoff h s := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring
      rw [e]; linarith
    rw [hh] at h0
    have hsq : ∀ s ∈ univ, (m' s - m s) * (m' s - m s) = 0 :=
      (sum_eq_zero_iff_of_nonneg fun s _ => mul_self_nonneg _).1 h0
    funext s
    have := hsq s (mem_univ s)
    nlinarith [mul_self_eq_zero.1 this]
  · rintro ⟨m₀, hm₀, huniq⟩
    by_contra hnc
    -- the span of payoffs is a proper subspace
    set P : (ι → ℝ) →ₗ[ℝ] (σ → ℝ) :=
      { toFun := M.payoff
        map_add' := fun h k => by funext s; simp [payoff, mul_add, sum_add_distrib]
        map_smul' := fun c h => by
          funext s; simp [payoff, mul_sum]; exact sum_congr rfl fun _ _ => by ring }
    have hlt : LinearMap.range P < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hnc fun z => ?_
      have : z ∈ LinearMap.range P := htop ▸ Submodule.mem_top
      obtain ⟨h, hh⟩ := this
      exact ⟨h, hh⟩
    obtain ⟨g, hg0, hgker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
    set z : σ → ℝ := fun s => g (unit s)
    have hgz : ∀ y, g y = ∑ s, y s * z s := fun y => by
      rw [g.pi_apply_eq_sum_univ]; rfl
    have hz : ∃ s, z s ≠ 0 := by
      by_contra h; push Not at h
      apply hg0; ext y; simp [hgz, h]
    have hzX : ∀ i, ∑ s, z s * M.X s i = 0 := fun i => by
      have : g (P (unit i)) = 0 := hgker ⟨unit i, rfl⟩
      rw [hgz] at this
      rw [← this]
      exact sum_congr rfl fun s _ => by simp [P, payoff, unit, mul_comm]
    obtain ⟨s₀, hs₀⟩ := hz
    have hne : (univ : Finset σ).Nonempty := ⟨s₀, mem_univ _⟩
    set c := univ.inf' hne m₀
    have hc : 0 < c := by
      obtain ⟨s, -, hs⟩ := exists_mem_eq_inf' hne m₀
      show 0 < univ.inf' hne m₀
      rw [hs]; exact hm₀.1 s
    set Z := ∑ s, |z s| + 1
    have hZ : 0 < Z := by have := sum_nonneg fun s (_ : s ∈ univ) => abs_nonneg (z s); linarith
    set ε := c / Z
    have hε : 0 < ε := div_pos hc hZ
    have hm' : M.IsStatePrice fun s => m₀ s + ε * z s := by
      refine ⟨fun s => ?_, fun i => ?_⟩
      · have h1 : |z s| ≤ ∑ t, |z t| := single_le_sum (fun t _ => abs_nonneg (z t)) (mem_univ s)
        have h2 : ε * |z s| < c := by
          calc ε * |z s| ≤ ε * (∑ t, |z t|) := mul_le_mul_of_nonneg_left h1 hε.le
            _ < ε * Z := mul_lt_mul_of_pos_left (by linarith) hε
            _ = c := div_mul_cancel₀ _ hZ.ne'
        have h3 : c ≤ m₀ s := inf'_le _ (mem_univ s)
        have h4 := neg_abs_le (z s)
        nlinarith
      · rw [hm₀.2 i]
        have := hzX i
        simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum, this, mul_zero, add_zero]
    have := huniq _ hm'
    have h2 := huniq _ hm₀
    have : ε * z s₀ = 0 := by
      have := congrFun (this.trans h2.symm) s₀
      simpa using this
    rcases mul_eq_zero.1 this with h | h
    · exact hε.ne' h
    · exact hs₀ h

end Market

/-- **Non-vacuity.** Two states; a bond (pays `1` in both, costs `9/10`) and a
stock (pays `2` or `1/2`, costs `1`). State prices `(11/30, 8/15)` are strictly
positive, so the market is arbitrage-free. -/
example : (⟨![![1, 2], ![1, 1 / 2]], ![9 / 10, 1]⟩ : Market (Fin 2) (Fin 2)).NoArbitrage :=
  (Market.ftap _).2 ⟨![11 / 30, 8 / 15], fun s => by fin_cases s <;> norm_num, fun i => by
    fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num⟩

end AssetPricing
end Econ

end
