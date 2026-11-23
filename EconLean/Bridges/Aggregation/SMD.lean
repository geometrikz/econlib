/-
# Sonnenschein–Mantel–Debreu: Debreu's decomposition

PLAN.md §7.2a (bridge B0). Debreu (1974), "Excess demand functions", J. Math.
Econ. 1; Sonnenschein (1972, 1973); Mantel (1974); MWG §17.E (Prop. 17.E.3).

**The economics (background; not all of this is proved here).** The SMD theorem says that the restrictions individual
rationality puts on *aggregate* excess demand are essentially only continuity
and Walras' law (and homogeneity): any such function, on prices bounded away
from the boundary, is the excess demand of some economy with at least `L`
consumers. So aggregate demand need not satisfy the weak axiom, equilibrium
need not be unique, and tâtonnement need not be stable. This is the formal
reason micro restrictions do not carry over to a "representative" macro
aggregate.

**What is formalized here.** The first and central step of Debreu's proof:
every excess demand `z` satisfying Walras' law on (a subset of) the open price
simplex, with `zₗ(p) + c pₗ > 0` for some constant `c` (true when `z` is bounded
below and prices are bounded away from `0`), is the sum of `L` functions

    zˡ(p) = (zₗ(p) + c pₗ) · (eₗ − (pₗ / ‖p‖²) p),        l = 1, …, L,

each of which satisfies Walras' law **and the weak axiom of revealed
preference**. Individual WARP is therefore no restriction on the aggregate
beyond Walras' law: the witness `zBad` below violates WARP (its equilibrium set
is not convex) yet decomposes into two WARP-satisfying pieces.

**Not yet formalized.** WARP is necessary for an individual excess demand to
come from a rational preference, and for two goods also sufficient, but for
`L ≥ 3` it is not sufficient. Debreu's second step, that each piece `zˡ` is the
excess demand of a consumer with a rational, continuous, monotone preference
and some endowment (an integrability / revealed-preference construction). The
result here is the revealed-preference form of SMD.
-/
module

public import EconLean.Bridges.Aggregation.LawOfDemand
public import EconLean.Bridges.Aggregation.GrossSubstitutes

@[expose] public section

namespace Econ

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The open price simplex `{p ≫ 0 | ∑ pᵢ = 1}`. -/
def openPriceSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | PositivePrices p ∧ ∑ i, p i = 1}

/-- Debreu's `l`-th piece: `(zₗ(p) + c pₗ) · (eₗ − (pₗ / ‖p‖²) p)`. -/
noncomputable def debreuPiece (z : (ι → ℝ) → (ι → ℝ)) (c : ℝ) (l : ι) (p : ι → ℝ) : ι → ℝ :=
  (z p l + c * p l) • (Pi.single l 1 - (p l / cost p p) • p)

omit [DecidableEq ι] in
theorem cost_self_pos {p : ι → ℝ} (hp : PositivePrices p) [Nonempty ι] : 0 < cost p p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (p j)) ⟨i, Finset.mem_univ i, mul_pos (hp i) (hp i)⟩

theorem cost_single_right (p : ι → ℝ) (l : ι) : cost p (Pi.single l 1) = p l := by
  simp [cost, Pi.single_apply]

/-- `p · (eₗ − (pₗ/‖p‖²) p) = 0`. -/
theorem cost_debreuDir [Nonempty ι] {p : ι → ℝ} (hp : PositivePrices p) (l : ι) :
    cost p (Pi.single l 1 - (p l / cost p p) • p) = 0 := by
  rw [cost_sub_right, cost_smul_right, cost_single_right]
  field_simp [(cost_self_pos hp).ne']
  ring

/-- Each piece satisfies Walras' law. -/
theorem walrasLaw_debreuPiece [Nonempty ι] (z : (ι → ℝ) → (ι → ℝ)) (c : ℝ) (l : ι)
    {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι) : WalrasLaw (debreuPiece z c l) D := by
  intro p hp
  rw [debreuPiece, cost_smul_right, cost_debreuDir (hD hp).1, mul_zero]

/-- The pieces add up to `z` (uses Walras' law for `z`). -/
theorem sum_debreuPiece [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} (c : ℝ) {p : ι → ℝ}
    (hp : PositivePrices p) (hW : cost p (z p) = 0) :
    ∑ l, debreuPiece z c l p = z p := by
  have hN := (cost_self_pos hp).ne'
  have hsum : ∀ i', ∑ l, (z p l + c * p l) * (p l / cost p p * p i') = c * p i' := by
    intro i'
    have e : ∀ l, (z p l + c * p l) * (p l / cost p p * p i')
        = ((z p l + c * p l) * p l) * (p i' / cost p p) := fun l => by ring
    simp only [e, ← Finset.sum_mul]
    have : ∑ l, (z p l + c * p l) * p l = cost p (z p) + c * cost p p := by
      simp only [cost, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, hW]; field_simp; ring
  funext i
  simp only [debreuPiece, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hsum i]; ring

/-- Each piece is continuous wherever `z` is (on a set of positive prices). -/
theorem continuousOn_debreuPiece [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} (c : ℝ) (l : ι)
    {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι) (hz : ContinuousOn z D) :
    ContinuousOn (debreuPiece z c l) D := by
  have hcost : Continuous fun p : ι → ℝ => cost p p := by unfold cost; fun_prop
  have hzl : ContinuousOn (fun p => z p l) D := (continuous_apply l).comp_continuousOn hz
  unfold debreuPiece
  refine (hzl.add (continuousOn_const.mul (continuous_apply l).continuousOn)).smul ?_
  have hq : ContinuousOn (fun p : ι → ℝ => p l / cost p p) D :=
    (continuous_apply l).continuousOn.div hcost.continuousOn
      fun p hp => (cost_self_pos (hD hp).1).ne'
  exact continuousOn_const.sub (hq.smul continuousOn_id)

omit [DecidableEq ι] in
/-- **Strict Cauchy–Schwarz on the open simplex**: two different points of the
open simplex are not proportional, so `(p·q)² < ‖p‖² ‖q‖²`. Via Lagrange's
identity `‖p‖²‖q‖² − (p·q)² = ½ ∑ᵢⱼ (pᵢqⱼ − pⱼqᵢ)²`. -/
theorem sq_cost_lt {p q : ι → ℝ} (hp : p ∈ openPriceSimplex ι) (hq : q ∈ openPriceSimplex ι)
    (hne : p ≠ q) : cost p q ^ 2 < cost p p * cost q q := by
  have expand : ∀ i j, (p i * q j - p j * q i) ^ 2
      = (p i * p i) * (q j * q j) + (p j * p j) * (q i * q i) - 2 * ((p i * q i) * (p j * q j)) :=
    fun i j => by ring
  have hA : ∑ i, ∑ j, (p i * p i) * (q j * q j) = cost p p * cost q q := by
    simp only [cost]; exact (Finset.sum_mul_sum _ _ _ _).symm
  have hB : ∑ i, ∑ j, (p j * p j) * (q i * q i) = cost p p * cost q q := by
    rw [Finset.sum_comm]; exact hA
  have hC : ∑ i, ∑ j, (p i * q i) * (p j * q j) = cost p q * cost p q := by
    simp only [cost]; exact (Finset.sum_mul_sum _ _ _ _).symm
  have hlag : cost p p * cost q q - cost p q ^ 2
      = (1 / 2) * ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2 := by
    have hsplit : ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2
        = ∑ i, ∑ j, (p i * p i) * (q j * q j) + ∑ i, ∑ j, (p j * p j) * (q i * q i)
          - 2 * ∑ i, ∑ j, (p i * q i) * (p j * q j) := by
      simp only [expand]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [hsplit, hA, hB, hC]; ring
  -- Some cross term is nonzero: otherwise `p` and `q` are proportional, hence equal.
  have hcross : ∃ i j, p i * q j - p j * q i ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have hsum : ∀ i, p i = q i := fun i => by
      have : ∑ j, p i * q j = ∑ j, p j * q i := Finset.sum_congr rfl fun j _ => by
        linarith [h i j]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hp.2, hq.2] at this
      linarith
    exact funext hsum
  obtain ⟨i, j, hij⟩ := hcross
  have hpos : 0 < ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2 := by
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, ?_⟩
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨j, Finset.mem_univ j, by positivity⟩
  linarith

/-- **Each piece satisfies the weak axiom** on the open simplex, provided its
weight `zₗ(p) + c pₗ` is positive there. -/
theorem excessWARP_debreuPiece [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} {c : ℝ} {l : ι}
    {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι) (hα : ∀ p ∈ D, 0 < z p l + c * p l) :
    ExcessWARP (debreuPiece z c l) D := by
  intro p hp q hq hne hle
  have hpS := hD hp
  have hqS := hD hq
  have hpq : p ≠ q := fun h => hne (by rw [h])
  set Np := cost p p
  set Nq := cost q q
  set C := cost p q
  have hNp : 0 < Np := cost_self_pos hpS.1
  have hNq : 0 < Nq := cost_self_pos hqS.1
  have hC : 0 < C := Finset.sum_pos (fun i _ => mul_pos (hpS.1 i) (hqS.1 i)) Finset.univ_nonempty
  have hCqp : cost q p = C := by simp only [C, cost]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hCS := sq_cost_lt hpS hqS hpq
  -- Unpack `p · zˡ(q) ≤ 0`.
  have h1 : cost p (debreuPiece z c l q) = (z q l + c * q l) * (p l - q l / Nq * C) := by
    rw [debreuPiece, cost_smul_right, cost_sub_right, cost_smul_right, cost_single_right]
  have h2 : cost q (debreuPiece z c l p) = (z p l + c * p l) * (q l - p l / Np * C) := by
    rw [debreuPiece, cost_smul_right, cost_sub_right, cost_smul_right, cost_single_right, hCqp]
  rw [h1] at hle
  rw [h2]
  have hαq := hα q hq
  have hαp := hα p hp
  have hle' : p l - q l / Nq * C ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hαq h]
  refine mul_pos hαp ?_
  -- `p_l ≤ q_l C / N_q`, so `q_l − p_l C/N_p ≥ q_l (1 − C²/(N_p N_q)) > 0`.
  have hql := hqS.1 l
  have key : p l * C / Np ≤ q l * C ^ 2 / (Nq * Np) := by
    have : p l ≤ q l * C / Nq := by
      have := hle'; rw [div_mul_eq_mul_div] at this; linarith
    calc p l * C / Np ≤ (q l * C / Nq) * C / Np := by gcongr
      _ = q l * C ^ 2 / (Nq * Np) := by field_simp
  have hfrac : q l * C ^ 2 / (Nq * Np) < q l := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  rw [div_mul_eq_mul_div]
  linarith

/-- **Debreu's decomposition (SMD, revealed-preference form).** Let `z` satisfy
Walras' law on a set `D` of prices in the open simplex, and suppose
`zₗ(p) + c pₗ > 0` on `D` for some constant `c`. Then `z` is the sum of `L`
functions, each satisfying Walras' law and the weak axiom on `D`. -/
theorem debreu_decomposition [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} {c : ℝ}
    {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι) (hW : WalrasLaw z D)
    (hα : ∀ p ∈ D, ∀ l, 0 < z p l + c * p l) :
    ∃ zs : ι → (ι → ℝ) → (ι → ℝ), (∀ p ∈ D, ∑ l, zs l p = z p) ∧
      ∀ l, WalrasLaw (zs l) D ∧ ExcessWARP (zs l) D :=
  ⟨fun l => debreuPiece z c l, fun p hp => sum_debreuPiece c (hD hp).1 (hW p hp),
    fun l => ⟨walrasLaw_debreuPiece z c l hD, excessWARP_debreuPiece hD fun p hp => hα p hp l⟩⟩

/-- **SMD on a truncated simplex.** If `z` satisfies Walras' law and is bounded
below on a set `D` of prices in the open simplex with every price at least
`ε > 0`, then `z` is a sum of `L` functions each satisfying Walras' law and the
weak axiom. -/
theorem debreu_decomposition_of_boundedBelow [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    {D : Set (ι → ℝ)} (hD : D ⊆ openPriceSimplex ι) (hW : WalrasLaw z D) {ε s : ℝ}
    (hε : 0 < ε) (hεD : ∀ p ∈ D, ∀ i, ε ≤ p i) (hb : ∀ p ∈ D, ∀ l, -s < z p l) :
    ∃ zs : ι → (ι → ℝ) → (ι → ℝ), (∀ p ∈ D, ∑ l, zs l p = z p) ∧
      ∀ l, WalrasLaw (zs l) D ∧ ExcessWARP (zs l) D := by
  refine debreu_decomposition (c := max s 0 / ε) hD hW fun p hp l => ?_
  have h1 : max s 0 ≤ max s 0 / ε * p l := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    exact mul_le_mul_of_nonneg_left (hεD p hp l) (le_max_right s 0)
  have := hb p hp l
  linarith [le_max_left s 0]

/-! ### Witness: an aggregate that violates WARP but decomposes into WARP pieces -/

namespace SMDExamples

/-- `f(t) = (t − 1/4)(t − 3/4)`: zero at `t = 1/4, 3/4`, negative at `1/2`. -/
noncomputable def fBad (t : ℝ) : ℝ := (t - 1 / 4) * (t - 3 / 4)

/-- An excess demand with Walras' law and two isolated equilibria
`(1/4, 3/4)` and `(3/4, 1/4)` but not their midpoint. -/
noncomputable def zBad (p : Fin 2 → ℝ) : Fin 2 → ℝ := ![fBad (p 0), -(p 0 * fBad (p 0)) / p 1]

/-- The truncated domain: open simplex with both prices at least `1/8`. -/
def DBad : Set (Fin 2 → ℝ) := {p | p ∈ openPriceSimplex (Fin 2) ∧ ∀ i, 1 / 8 ≤ p i}

theorem DBad_subset : DBad ⊆ openPriceSimplex (Fin 2) := fun _ hp => hp.1

theorem convex_DBad : Convex ℝ DBad := by
  rintro p ⟨⟨hp, hps⟩, hp8⟩ q ⟨⟨hq, hqs⟩, hq8⟩ a b ha hb hab
  refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hp i)) (mul_nonneg hb (hq i).le)
    · subst ha'; simp at hab; subst hab; simpa using hq i
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hps, hqs, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hp8 i, hq8 i]

theorem walrasLaw_zBad : WalrasLaw zBad DBad := by
  rintro p ⟨⟨hp, -⟩, -⟩
  simp only [cost, Fin.sum_univ_two, zBad, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp [(hp 1).ne']
  ring

/-- `zBad` **violates the weak axiom**: its equilibrium set on the convex
domain `DBad` is not convex. -/
theorem not_excessWARP_zBad : ¬ ExcessWARP zBad DBad := by
  intro hWARP
  have hconv := hWARP.convex_equilibria convex_DBad walrasLaw_zBad
  let p₁ : Fin 2 → ℝ := ![1 / 4, 3 / 4]
  let p₂ : Fin 2 → ℝ := ![3 / 4, 1 / 4]
  have hmem : ∀ a b : ℝ, 1 / 8 ≤ a → 1 / 8 ≤ b → a + b = 1 → (![a, b] : Fin 2 → ℝ) ∈ DBad :=
    fun a b ha hb hab => ⟨⟨fun i => by fin_cases i <;> simp <;> linarith, by simp [hab]⟩,
      fun i => by fin_cases i <;> simp <;> linarith⟩
  have h₁ : p₁ ∈ {p | p ∈ DBad ∧ zBad p = 0} := ⟨hmem _ _ (by norm_num) (by norm_num) (by norm_num),
    by funext i; fin_cases i <;> simp [p₁, zBad, fBad]⟩
  have h₂ : p₂ ∈ {p | p ∈ DBad ∧ zBad p = 0} := ⟨hmem _ _ (by norm_num) (by norm_num) (by norm_num),
    by funext i; fin_cases i <;> simp [p₂, zBad, fBad]⟩
  have hmid := hconv h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h0 := congrFun hmid.2 0
  simp [p₁, p₂, zBad, fBad] at h0
  norm_num at h0

/-- The weights of Debreu's pieces are positive on `DBad` with `c = 16`. -/
theorem zBad_weight_pos : ∀ p ∈ DBad, ∀ l, 0 < zBad p l + 16 * p l := by
  rintro p ⟨⟨hp, hs⟩, h8⟩ l
  have hs' : p 0 + p 1 = 1 := by simpa [Fin.sum_univ_two] using hs
  have h80 := h8 0
  have h81 := h8 1
  fin_cases l
  · simp only [zBad, fBad, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    nlinarith
  · simp only [zBad, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hp1 := hp 1
    have hf : fBad (p 0) ≤ 3 / 16 := by unfold fBad; nlinarith
    have hpf : p 0 * fBad (p 0) ≤ 3 / 16 := by
      nlinarith [mul_le_mul_of_nonneg_left hf (hp 0).le]
    have hsq : 1 / 4 ≤ 16 * p 1 * p 1 := by nlinarith
    rw [neg_div, ← sub_eq_neg_add, sub_pos, div_lt_iff₀ hp1]
    nlinarith

/-- **SMD in action.** `zBad` violates WARP in the aggregate, yet it is the sum
of two excess demands each satisfying Walras' law and WARP. -/
theorem zBad_smd : ¬ ExcessWARP zBad DBad ∧
    ∃ zs : Fin 2 → (Fin 2 → ℝ) → (Fin 2 → ℝ), (∀ p ∈ DBad, ∑ l, zs l p = zBad p) ∧
      ∀ l, WalrasLaw (zs l) DBad ∧ ExcessWARP (zs l) DBad :=
  ⟨not_excessWARP_zBad, debreu_decomposition DBad_subset walrasLaw_zBad zBad_weight_pos⟩

end SMDExamples

end Econ
