/-
# Sonnenschein–Mantel–Debreu, step 2: every Debreu piece is a rational consumer

PLAN.md §7.2a (bridge B0). Debreu (1974), "Excess demand functions", J. Math.
Econ. 1; Geanakoplos (1984), "Utility functions for Debreu's excess demands",
J. Math. Econ. 13; MWG §17.E (Prop. 17.E.3).

`SMD.lean` splits an excess demand `z` (Walras' law, prices in the open simplex)
into the pieces

    zˡ(p) = aₗ(p) · (eₗ − (pₗ / ‖p‖²) p),        aₗ(p) = zₗ(p) + c pₗ > 0,

and shows each satisfies the weak axiom. Here we prove the stronger statement
of the SMD theorem: **each piece is the excess demand of a utility-maximizing
consumer**, so `z` itself is the aggregate excess demand of an `L`-consumer
exchange economy.

**Construction (derived here; the level-set idea is standard revealed
preference).** Write `V(q) = q_l / ‖q‖` for the cosine between `q` and the
`l`-th axis and `y(q) = a(q)(e_l − (q_l/‖q‖²) q)` for the piece. For a level
`θ`, let `C_θ` be the convex hull of the pieces `y(q)` at prices with
`V(q) ≤ θ`, and let the utility of a net trade `x` be `−inf {θ | x ∈ C_θ}`
(with a floor). Then:

* the upper contour sets are intersections of the `C_θ`, so the utility is
  quasiconcave (convex preferences);
* `p · y(q) = a(q) (‖p‖ (V p − V q) + (q_l/‖q‖²)(‖p‖‖q‖ − p·q))`, and the second
  term is positive for `q ≠ p` by strict Cauchy–Schwarz. So every point of `C_θ`
  with `θ < V p` costs strictly more than `0` at `p`; hence `y(p)` has utility
  exactly `−V p`, and no affordable net trade does better;
* uniqueness needs a quantitative version: a compactness argument shows an
  affordable `x ≠ y(p)` lies outside `C_θ` for all `θ < V p + δ`.

The consumer with endowment `ω = B·𝟙` (`B` bounding the piece on the compact
price set) and utility `U(x) = u(x − ω)` on the orthant then has Walrasian
demand exactly `{ω + y(p)}`.

**Scope and caveat.** The preferences are rational (complete and transitive:
they come from a utility) and convex (quasiconcave utility), demand is
single-valued and equal to the piece on the whole compact price set, and
endowments are strictly positive. Debreu (and MWG 17.E.3) obtain more:
**continuous, strictly convex, monotone** preferences. The utility built here
has none of these three properties, and provably so: `C_θ` stops growing at
`θ = 1`, so `u = −2` off the bounded set `C_1` (a jump, satiation, and thick
indifference regions). Getting standard consumers needs a different utility
(Geanakoplos 1984 or Mantel 1974); that is an open item, not a gap in this
proof. Individual budget exhaustion holds on `K` because `p · y(p) = 0`, not
because of local nonsatiation. Prices are normalized to a compact subset `K`
of the open simplex, which includes Debreu's `S_ε`; demand is homogeneous of
degree zero (`demand_smul`), so nothing is lost by normalizing.
-/
module

public import EconLean.Bridges.Aggregation.SMD
public import EconLean.Consumer.Demand
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Econ

open Finset Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cosine between `q` and the `l`-th coordinate axis: `q_l / ‖q‖`. -/
noncomputable def dirCos (l : ι) (q : ι → ℝ) : ℝ := q l / Real.sqrt (cost q q)

/-- A Debreu-type piece with a general positive weight `a`:
`a(q) · (e_l − (q_l / ‖q‖²) q)`. `debreuPiece z c l` is the case
`a q = z q l + c q l`. -/
noncomputable def weightedPiece (a : (ι → ℝ) → ℝ) (l : ι) (q : ι → ℝ) : ι → ℝ :=
  a q • (Pi.single l 1 - (q l / cost q q) • q)

theorem debreuPiece_eq_weightedPiece (z : (ι → ℝ) → (ι → ℝ)) (c : ℝ) (l : ι) :
    debreuPiece z c l = weightedPiece (fun q => z q l + c * q l) l := rfl

/-- The level-`θ` better set: the convex hull of the pieces at prices in `K`
whose cosine with axis `l` is at most `θ`. -/
noncomputable def pieceLevelSet (K : Set (ι → ℝ)) (a : (ι → ℝ) → ℝ) (l : ι) (θ : ℝ) :
    Set (ι → ℝ) :=
  convexHull ℝ (weightedPiece a l '' {q | q ∈ K ∧ dirCos l q ≤ θ})

/-- The utility over net trades that rationalizes the piece:
`u(x) = −inf ({2} ∪ {θ | x ∈ C_θ})`. -/
noncomputable def pieceUtility (K : Set (ι → ℝ)) (a : (ι → ℝ) → ℝ) (l : ι) (x : ι → ℝ) : ℝ :=
  -sInf (insert 2 {θ | x ∈ pieceLevelSet K a l θ})

/-! ### Algebra of the pieces -/

omit [DecidableEq ι] in
theorem cost_comm (p q : ι → ℝ) : cost p q = cost q p := by
  simp only [cost]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cost_weightedPiece (a : (ι → ℝ) → ℝ) (l : ι) (p q : ι → ℝ) :
    cost p (weightedPiece a l q) = a q * (p l - q l * cost p q / cost q q) := by
  rw [weightedPiece, cost_smul_right, cost_sub_right, cost_smul_right, cost_single_right]
  ring

omit [DecidableEq ι] in
/-- The key identity:
`p_l − q_l (p·q)/‖q‖² = ‖p‖ (V p − V q) + (q_l/‖q‖²)(‖p‖‖q‖ − p·q)`. -/
theorem piece_identity [Nonempty ι] {p q : ι → ℝ} (hp : PositivePrices p) (hq : PositivePrices q)
    (l : ι) :
    p l - q l * cost p q / cost q q
      = Real.sqrt (cost p p) * (dirCos l p - dirCos l q)
        + q l / cost q q * (Real.sqrt (cost p p) * Real.sqrt (cost q q) - cost p q) := by
  have hNp := cost_self_pos hp
  have hNq := cost_self_pos hq
  have sp := Real.sqrt_pos.2 hNp
  have sq := Real.sqrt_pos.2 hNq
  have eq : cost q q = Real.sqrt (cost q q) ^ 2 := (Real.sq_sqrt hNq.le).symm
  unfold dirCos
  generalize Real.sqrt (cost q q) = t at eq sq ⊢
  generalize Real.sqrt (cost p p) = s at sp ⊢
  rw [eq]
  field_simp
  ring

omit [DecidableEq ι] in
/-- The Cauchy–Schwarz gap `‖p‖‖q‖ − p·q` is nonnegative on the open simplex and
positive for `q ≠ p`. -/
theorem cs_gap_pos {p q : ι → ℝ} (hp : p ∈ openPriceSimplex ι) (hq : q ∈ openPriceSimplex ι)
    (hne : p ≠ q) : 0 < Real.sqrt (cost p p) * Real.sqrt (cost q q) - cost p q := by
  have hC : 0 < cost p q := by
    have : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simpa using hp.2
    exact Finset.sum_pos (fun i _ => mul_pos (hp.1 i) (hq.1 i)) Finset.univ_nonempty
  have hlt := sq_cost_lt hp hq hne
  rw [← Real.sqrt_mul (cost_self_nonneg p), sub_pos, Real.lt_sqrt hC.le]
  exact hlt
where
  cost_self_nonneg (p : ι → ℝ) : 0 ≤ cost p p :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)

omit [DecidableEq ι] in
theorem cs_gap_nonneg {p q : ι → ℝ} (hp : p ∈ openPriceSimplex ι) (hq : q ∈ openPriceSimplex ι) :
    0 ≤ Real.sqrt (cost p p) * Real.sqrt (cost q q) - cost p q := by
  by_cases h : p = q
  · subst h
    rw [Real.mul_self_sqrt (show 0 ≤ cost p p from
      Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)), sub_self]
  · exact (cs_gap_pos hp hq h).le

omit [DecidableEq ι] in
theorem dirCos_pos [Nonempty ι] {q : ι → ℝ} (hq : PositivePrices q) (l : ι) : 0 < dirCos l q :=
  div_pos (hq l) (Real.sqrt_pos.2 (cost_self_pos hq))

omit [DecidableEq ι] in
theorem dirCos_le_one [Nonempty ι] {q : ι → ℝ} (hq : PositivePrices q) (l : ι) :
    dirCos l q ≤ 1 := by
  have hs := Real.sqrt_pos.2 (cost_self_pos hq)
  rw [dirCos, div_le_one hs, Real.le_sqrt (hq l).le (cost_self_pos hq).le, sq]
  exact Finset.single_le_sum (f := fun i => q i * q i) (fun i _ => mul_self_nonneg (q i))
    (Finset.mem_univ l)

/-! ### Convex combinations of pieces -/

theorem exists_comb_of_mem_pieceLevelSet {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι} {θ : ℝ}
    {x : ι → ℝ} (hx : x ∈ pieceLevelSet K a l θ) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (q : κ → ι → ℝ), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ (∀ i, q i ∈ K ∧ dirCos l (q i) ≤ θ) ∧
      ∑ i, w i • weightedPiece a l (q i) = x := by
  obtain ⟨κ, hκ, w, z, hw0, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.1 hx
  choose q hq hqz using hz
  refine ⟨κ, hκ, w, q, hw0, hw1, hq, ?_⟩
  simpa only [hqz] using hx

omit [DecidableEq ι] in
theorem cost_comb (p : ι → ℝ) {κ : Type} [Fintype κ] (w : κ → ℝ) (v : κ → ι → ℝ) :
    cost p (∑ i, w i • v i) = ∑ i, w i * cost p (v i) := by
  simp only [cost, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A weighted average (weights `≥ 0` summing to `1`) of positive numbers is
positive. -/
theorem wsum_pos {κ : Type} [Fintype κ] {w t : κ → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (ht : ∀ i, 0 < t i) : 0 < ∑ i, w i * t i := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (ht j).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (ht i)⟩

/-- **Strict separation below the level of `p`.** Every point of `C_θ` with
`θ < V p` costs strictly more than `0` at `p`. -/
theorem cost_pos_of_mem_pieceLevelSet [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ}
    {l : ι} (hKS : K ⊆ openPriceSimplex ι) (hapos : ∀ q ∈ K, 0 < a q) {p : ι → ℝ}
    (hp : p ∈ K) {θ : ℝ} (hθ : θ < dirCos l p) {x : ι → ℝ} (hx : x ∈ pieceLevelSet K a l θ) :
    0 < cost p x := by
  obtain ⟨κ, _, w, q, hw0, hw1, hq, rfl⟩ := exists_comb_of_mem_pieceLevelSet hx
  rw [cost_comb]
  refine wsum_pos hw0 hw1 fun i => ?_
  rw [cost_weightedPiece, piece_identity (hKS hp).1 (hKS (hq i).1).1]
  refine mul_pos (hapos _ (hq i).1) ?_
  have h1 : 0 < Real.sqrt (cost p p) * (dirCos l p - dirCos l (q i)) :=
    mul_pos (Real.sqrt_pos.2 (cost_self_pos (hKS hp).1)) (by linarith [(hq i).2])
  have h2 : 0 ≤ q i l / cost (q i) (q i) *
      (Real.sqrt (cost p p) * Real.sqrt (cost (q i) (q i)) - cost p (q i)) :=
    mul_nonneg (div_pos ((hKS (hq i).1).1 l) (cost_self_pos (hKS (hq i).1).1)).le
      (cs_gap_nonneg (hKS hp) (hKS (hq i).1))
  linarith

theorem continuousOn_weightedPiece [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} (l : ι)
    (hKS : K ⊆ openPriceSimplex ι) (ha : ContinuousOn a K) :
    ContinuousOn (weightedPiece a l) K := by
  have hcost : Continuous fun p : ι → ℝ => cost p p := by unfold cost; fun_prop
  unfold weightedPiece
  refine ha.smul ?_
  have hq : ContinuousOn (fun p : ι → ℝ => p l / cost p p) K :=
    (continuous_apply l).continuousOn.div hcost.continuousOn
      fun p hp => (cost_self_pos (hKS hp).1).ne'
  exact continuousOn_const.sub (hq.smul continuousOn_id)

/-- **Quantitative uniqueness.** On a compact price set, an affordable net trade
`x ≠ y(p)` (i.e. `p · x ≤ 0`) stays outside every `C_θ` with `θ < V p + δ`, for
some `δ > 0`. -/
theorem exists_gap [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι}
    (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι) (ha : ContinuousOn a K)
    (hapos : ∀ q ∈ K, 0 < a q) {p : ι → ℝ} (hp : p ∈ K) {x : ι → ℝ} (hx : cost p x ≤ 0)
    (hne : x ≠ weightedPiece a l p) :
    ∃ δ > 0, ∀ θ, θ < dirCos l p + δ → x ∉ pieceLevelSet K a l θ := by
  set y := weightedPiece a l with hy_def
  have hy : ContinuousOn y K := continuousOn_weightedPiece l hKS ha
  have hNp := cost_self_pos (hKS hp).1
  set sp := Real.sqrt (cost p p) with hsp_def
  have hsp : 0 < sp := Real.sqrt_pos.2 hNp
  set η := ‖x - y p‖ / 2 with hη_def
  have hη : 0 < η := by
    have : 0 < ‖x - y p‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    positivity
  -- The far set `F`, where the piece is at least `η` away from `y(p)`.
  have hdist : ContinuousOn (fun q => ‖y q - y p‖) K := (hy.sub continuousOn_const).norm
  set F := K ∩ (fun q => ‖y q - y p‖) ⁻¹' Ici η with hF_def
  have hFc : IsCompact F :=
    hK.of_isClosed_subset (hdist.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  -- The Cauchy–Schwarz term `g(q)` is bounded below by some `μ > 0` on `F`.
  set g : (ι → ℝ) → ℝ := fun q => q l / cost q q * (sp * Real.sqrt (cost q q) - cost p q)
    with hg_def
  have hgc : ContinuousOn g K := by
    have hcost : Continuous fun q : ι → ℝ => cost q q := by unfold cost; fun_prop
    have hcp : Continuous fun q : ι → ℝ => cost p q := by unfold cost; fun_prop
    refine ((continuous_apply l).continuousOn.div hcost.continuousOn
      fun q hq => (cost_self_pos (hKS hq).1).ne').mul ?_
    exact (continuousOn_const.mul (Real.continuous_sqrt.comp hcost).continuousOn).sub
      hcp.continuousOn
  obtain ⟨μ, hμ, hμF⟩ : ∃ μ > 0, ∀ q ∈ F, μ ≤ g q := by
    rcases F.eq_empty_or_nonempty with hE | hne'
    · exact ⟨1, one_pos, fun q hq => by simp [hE] at hq⟩
    obtain ⟨q₀, hq₀, hmin⟩ := hFc.exists_isMinOn hne' (hgc.mono inter_subset_left)
    refine ⟨g q₀, ?_, fun q hq => hmin hq⟩
    have hq₀K := hq₀.1
    have hq₀p : p ≠ q₀ := by
      rintro rfl
      have : η ≤ ‖y p - y p‖ := hq₀.2
      simp at this; linarith
    exact mul_pos (div_pos ((hKS hq₀K).1 l) (cost_self_pos (hKS hq₀K).1))
      (cs_gap_pos (hKS hp) (hKS hq₀K) hq₀p)
  -- Bounds on the weight `a` and on the distance of pieces.
  obtain ⟨qm, hqmK, hqm⟩ := hK.exists_isMinOn ⟨p, hp⟩ ha
  obtain ⟨qM, hqMK, hqM⟩ := hK.exists_isMaxOn ⟨p, hp⟩ ha
  obtain ⟨qB, hqBK, hqB⟩ := hK.exists_isMaxOn ⟨p, hp⟩ hdist
  set m := a qm
  set M := a qM
  set B := ‖y qB - y p‖
  have hm : 0 < m := hapos qm hqmK
  have hmM : m ≤ M := hqm hqMK
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hB : 0 ≤ B := norm_nonneg _
  set D := 2 * B * M * sp / (m * μ) with hD_def
  have hD : 0 ≤ D := by positivity
  set δ := min (μ / (2 * sp)) (η / (D + 1)) with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, fun θ hθ hxθ => ?_⟩
  obtain ⟨κ, _, w, q, hw0, hw1, hq, hxw⟩ := exists_comb_of_mem_pieceLevelSet hxθ
  have hqK : ∀ i, q i ∈ K := fun i => (hq i).1
  -- `Φᵢ`: the cost of the `i`-th piece per unit weight.
  set Φ : κ → ℝ := fun i => p l - q i l * cost p (q i) / cost (q i) (q i) with hΦ_def
  have hΦ : ∀ i, Φ i = sp * (dirCos l p - dirCos l (q i)) + g (q i) := fun i =>
    piece_identity (hKS hp).1 (hKS (hqK i)).1 l
  have hg0 : ∀ i, 0 ≤ g (q i) := fun i =>
    mul_nonneg (div_pos ((hKS (hqK i)).1 l) (cost_self_pos (hKS (hqK i)).1)).le
      (cs_gap_nonneg (hKS hp) (hKS (hqK i)))
  have hlow : ∀ i, -(sp * δ) < Φ i - g (q i) := by
    intro i
    rw [hΦ i, add_sub_cancel_right]
    have : dirCos l (q i) < dirCos l p + δ := lt_of_le_of_lt (hq i).2 hθ
    nlinarith
  have hδμ : sp * δ ≤ μ / 2 := by
    have := min_le_left (μ / (2 * sp)) (η / (D + 1))
    calc sp * δ ≤ sp * (μ / (2 * sp)) := by gcongr
      _ = μ / 2 := by field_simp
  -- Per-term bounds.
  have hcostq : ∀ i, cost p (y (q i)) = a (q i) * Φ i := fun i => cost_weightedPiece a l p (q i)
  set r : κ → ℝ := fun i => a (q i) * Φ i + M * sp * δ with hr_def
  have hr0 : ∀ i, 0 ≤ r i := by
    intro i
    have ha_i := hapos _ (hqK i)
    have hM_i : a (q i) ≤ M := hqM (hqK i)
    have hΦi : -(sp * δ) < Φ i := by linarith [hlow i, hg0 i]
    simp only [hr_def]
    rcases le_or_gt 0 (Φ i) with h | h
    · have := mul_nonneg ha_i.le h
      have : 0 ≤ M * sp * δ := by positivity
      linarith
    · nlinarith
  have hfar : ∀ i, ‖y (q i) - y p‖ ≤ η + 2 * B / (m * μ) * r i := by
    intro i
    rcases lt_or_ge ‖y (q i) - y p‖ η with h | h
    · have : 0 ≤ 2 * B / (m * μ) * r i := mul_nonneg (by positivity) (hr0 i)
      linarith
    · have hiF : q i ∈ F := ⟨hqK i, h⟩
      have hgi := hμF _ hiF
      have hΦi : μ / 2 ≤ Φ i := by linarith [hlow i]
      have ha_i : m ≤ a (q i) := hqm (hqK i)
      have hri : m * μ / 2 ≤ r i := by
        simp only [hr_def]
        have : m * (μ / 2) ≤ a (q i) * Φ i :=
          mul_le_mul ha_i hΦi (by positivity) (hapos _ (hqK i)).le
        have : 0 ≤ M * sp * δ := by positivity
        linarith
      have hBi : ‖y (q i) - y p‖ ≤ B := hqB (hqK i)
      have : B ≤ 2 * B / (m * μ) * r i := by
        calc B = 2 * B / (m * μ) * (m * μ / 2) := by field_simp
          _ ≤ 2 * B / (m * μ) * r i := by gcongr
      linarith
  -- Sum up.
  have hsumr : ∑ i, w i * r i = cost p x + M * sp * δ := by
    simp only [hr_def, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    rw [← hxw, cost_comb]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [cost_weightedPiece]
  have hxdiff : x - y p = ∑ i, w i • (y (q i) - y p) := by
    rw [← hxw]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
    rfl
  have hnorm : ‖x - y p‖ ≤ η + 2 * B / (m * μ) * (M * sp * δ) := by
    calc ‖x - y p‖ = ‖∑ i, w i • (y (q i) - y p)‖ := by rw [hxdiff]
      _ ≤ ∑ i, ‖w i • (y (q i) - y p)‖ := norm_sum_le _ _
      _ = ∑ i, w i * ‖y (q i) - y p‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (hw0 i)]
      _ ≤ ∑ i, w i * (η + 2 * B / (m * μ) * r i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfar i) (hw0 i)
      _ = η + 2 * B / (m * μ) * ∑ i, w i * r i := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul,
            Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ η + 2 * B / (m * μ) * (M * sp * δ) := by
          rw [hsumr]
          have : 0 ≤ 2 * B / (m * μ) := by positivity
          gcongr
          linarith
  have hDδ : 2 * B / (m * μ) * (M * sp * δ) = D * δ := by
    simp only [hD_def]; field_simp
  have hDδlt : D * δ < η := by
    have h1 : δ ≤ η / (D + 1) := min_le_right _ _
    calc D * δ ≤ D * (η / (D + 1)) := by gcongr
      _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have : ‖x - y p‖ = 2 * η := by rw [hη_def]; ring
  linarith

/-! ### The utility rationalizes the piece -/

theorem bddBelow_levels [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι}
    (hKS : K ⊆ openPriceSimplex ι) (x : ι → ℝ) :
    BddBelow (insert 2 {θ | x ∈ pieceLevelSet K a l θ}) := by
  refine ⟨0, ?_⟩
  rintro θ (rfl | hθ)
  · norm_num
  · obtain ⟨_, ⟨q, ⟨hqK, hqθ⟩, -⟩⟩ :=
      convexHull_nonempty_iff.1 (⟨x, hθ⟩ : (pieceLevelSet K a l θ).Nonempty)
    exact ((dirCos_pos (hKS hqK).1 l).trans_le hqθ).le

theorem pieceLevelSet_mono {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι} {θ θ' : ℝ}
    (h : θ ≤ θ') : pieceLevelSet K a l θ ⊆ pieceLevelSet K a l θ' :=
  convexHull_mono (image_mono fun _ hq => ⟨hq.1, hq.2.trans h⟩)

/-- **Convex preferences.** The utility is quasiconcave. -/
theorem quasiconcaveOn_pieceUtility [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι}
    (hKS : K ⊆ openPriceSimplex ι) : QuasiconcaveOn ℝ univ (pieceUtility K a l) := by
  intro r x₁ hx₁ x₂ hx₂ s t hs ht hst
  refine ⟨mem_univ _, ?_⟩
  simp only [mem_ofPred_eq, pieceUtility] at hx₁ hx₂ ⊢
  have h₁ : sInf (insert 2 {θ | x₁ ∈ pieceLevelSet K a l θ}) ≤ -r := by linarith [hx₁.2]
  have h₂ : sInf (insert 2 {θ | x₂ ∈ pieceLevelSet K a l θ}) ≤ -r := by linarith [hx₂.2]
  rw [Real.sInf_le_iff (bddBelow_levels hKS _) (insert_nonempty _ _)] at h₁ h₂
  suffices sInf (insert 2 {θ | s • x₁ + t • x₂ ∈ pieceLevelSet K a l θ}) ≤ -r by linarith
  rw [Real.sInf_le_iff (bddBelow_levels hKS _) (insert_nonempty _ _)]
  intro ε hε
  obtain ⟨θ₁, hθ₁, hθ₁ε⟩ := h₁ ε hε
  obtain ⟨θ₂, hθ₂, hθ₂ε⟩ := h₂ ε hε
  rcases hθ₁ with rfl | hθ₁
  · exact ⟨2, mem_insert _ _, hθ₁ε⟩
  rcases hθ₂ with rfl | hθ₂
  · exact ⟨2, mem_insert _ _, hθ₂ε⟩
  refine ⟨max θ₁ θ₂, mem_insert_of_mem _ ?_, max_lt hθ₁ε hθ₂ε⟩
  exact (convex_convexHull ℝ _) (pieceLevelSet_mono (le_max_left θ₁ θ₂) hθ₁)
    (pieceLevelSet_mono (le_max_right θ₁ θ₂) hθ₂) hs ht hst

/-- The piece `y(p)` has utility exactly `−V(p)`. -/
theorem pieceUtility_self [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι}
    (hKS : K ⊆ openPriceSimplex ι) (hapos : ∀ q ∈ K, 0 < a q) {p : ι → ℝ} (hp : p ∈ K) :
    pieceUtility K a l (weightedPiece a l p) = -dirCos l p := by
  rw [pieceUtility, neg_inj]
  refine le_antisymm (csInf_le (bddBelow_levels hKS _) (mem_insert_of_mem _ ?_))
    (le_csInf (insert_nonempty _ _) ?_)
  · exact subset_convexHull ℝ _ ⟨p, ⟨hp, le_rfl⟩, rfl⟩
  · rintro θ (rfl | hθ)
    · linarith [dirCos_le_one (hKS hp).1 l]
    · by_contra hlt
      push Not at hlt
      have := cost_pos_of_mem_pieceLevelSet hKS hapos hp hlt hθ
      rw [cost_weightedPiece] at this
      have hz : p l - p l * cost p p / cost p p = 0 := by
        field_simp [(cost_self_pos (hKS hp).1).ne']; ring
      rw [hz, mul_zero] at this
      exact lt_irrefl _ this

/-- **The piece is the unique optimum.** Among net trades `x` affordable at `p`
(`p · x ≤ 0`), the piece `y(p)` is strictly preferred to every other. -/
theorem pieceUtility_lt [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι}
    (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι) (ha : ContinuousOn a K)
    (hapos : ∀ q ∈ K, 0 < a q) {p : ι → ℝ} (hp : p ∈ K) {x : ι → ℝ} (hx : cost p x ≤ 0)
    (hne : x ≠ weightedPiece a l p) :
    pieceUtility K a l x < pieceUtility K a l (weightedPiece a l p) := by
  rw [pieceUtility_self hKS hapos hp, pieceUtility, neg_lt_neg_iff]
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hK hKS ha hapos hp hx hne
  have hle : dirCos l p + min δ 1 ≤ sInf (insert 2 {θ | x ∈ pieceLevelSet K a l θ}) := by
    refine le_csInf (insert_nonempty _ _) ?_
    rintro θ (rfl | hθ)
    · linarith [dirCos_le_one (hKS hp).1 l, min_le_right δ 1]
    · by_contra hlt
      push Not at hlt
      exact hgap θ (lt_of_lt_of_le hlt (by linarith [min_le_left δ 1])) hθ
  linarith [lt_min hδ one_pos]

/-- **A rational consumer for each piece (Debreu's step 2).** Let `K` be a
compact set of prices in the open simplex and `a` a continuous, positive weight
on `K`. There is a utility `U` with convex upper contour sets and a nonnegative
endowment `ω` such that, at every `p ∈ K`, the consumer's Walrasian demand is
exactly the single bundle `ω + a(p)(e_l − (p_l/‖p‖²) p)`. So the piece is the
consumer's excess demand.

Caveat: `U` is quasiconcave but not continuous, not monotone and not strictly
quasiconcave (see the module docstring). -/
theorem exists_consumer_weightedPiece [Nonempty ι] {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ}
    (l : ι) (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι) (ha : ContinuousOn a K)
    (hapos : ∀ q ∈ K, 0 < a q) :
    ∃ (U : (ι → ℝ) → ℝ) (ω : ι → ℝ), QuasiconcaveOn ℝ univ U ∧ (∀ i, 0 < ω i) ∧
      ∀ p ∈ K, demand (prefOf U) p (cost p ω) = {ω + weightedPiece a l p} := by
  set y := weightedPiece a l
  set u := pieceUtility K a l
  -- A bound on the pieces, giving an endowment large enough that `ω + y(p) ≥ 0`.
  obtain ⟨b, hb⟩ : ∃ b, ∀ q ∈ K, ‖y q‖ ≤ b := by
    obtain ⟨b, hb⟩ := (hK.image_of_continuousOn
      (continuousOn_weightedPiece l hKS ha).norm).isBounded.bddAbove
    exact ⟨b, fun q hq => hb ⟨q, hq, rfl⟩⟩
  set ω : ι → ℝ := fun _ => max b 1
  refine ⟨fun x => u (x - ω), ω, ?_, fun i => lt_of_lt_of_le one_pos (le_max_right b 1), ?_⟩
  · intro r
    have hc := quasiconcaveOn_pieceUtility (a := a) (l := l) hKS r
    have : {x | x ∈ (univ : Set (ι → ℝ)) ∧ r ≤ u (x - ω)}
        = (fun x => -ω + x) ⁻¹' {x | x ∈ univ ∧ r ≤ u x} := by
      ext x; simp [sub_eq_neg_add]
    rw [this]
    exact hc.translate_preimage_right (-ω)
  · intro p hp
    have hy0 : 0 ≤ ω + y p := fun i => by
      have h1 : |y p i| ≤ ‖y p‖ := by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (y p) i
      have h2 := hb p hp
      simp only [Pi.add_apply, Pi.zero_apply, ω]
      have := neg_abs_le (y p i)
      linarith [le_max_left b 1]
    have hcy : cost p (y p) = 0 := by
      rw [cost_weightedPiece]
      have : p l - p l * cost p p / cost p p = 0 := by
        field_simp [(cost_self_pos (hKS hp).1).ne']; ring
      rw [this, mul_zero]
    have hbud : ω + y p ∈ budgetSet p (cost p ω) :=
      ⟨hy0, by rw [cost_add_right, hcy, add_zero]⟩
    have key : ∀ x ∈ budgetSet p (cost p ω), x ≠ ω + y p → u (x - ω) < u (y p) := by
      intro x hx hne
      refine pieceUtility_lt hK hKS ha hapos hp ?_ ?_
      · rw [cost_sub_right]; linarith [hx.2]
      · intro h; exact hne (sub_eq_iff_eq_add'.1 h)
    ext x
    simp only [demand, mem_ofPred_eq, mem_singleton_iff, prefOf]
    constructor
    · rintro ⟨hx, hmax⟩
      by_contra hne
      have h1 := hmax _ hbud
      have h2 := key x hx hne
      simp only [add_sub_cancel_left] at h1
      linarith
    · rintro rfl
      refine ⟨hbud, fun x hx => ?_⟩
      simp only [add_sub_cancel_left]
      by_cases hxe : x = ω + y p
      · rw [hxe, add_sub_cancel_left]
      · exact (key x hx hxe).le

/-! ### The Sonnenschein–Mantel–Debreu theorem -/

/-- **Sonnenschein–Mantel–Debreu, with convex (quasiconcave) consumers.** Let `z`
be continuous and satisfy Walras' law on a compact set `K` of prices in the open
simplex (for example Debreu's `S_ε`). Then `z` is the aggregate excess demand of
an exchange economy with `L` consumers, each with a quasiconcave utility and a
strictly positive endowment, whose Walrasian demand is single-valued at every
`p ∈ K`.

Caveat: the canonical theorem also makes the preferences continuous, strictly
convex and monotone. The utilities here are none of these (they are satiated
and discontinuous), which makes rationalization easier; see the module
docstring. -/
theorem sonnenschein_mantel_debreu_quasiconcave [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)} {K : Set (ι → ℝ)}
    (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι) (hz : ContinuousOn z K)
    (hW : WalrasLaw z K) :
    ∃ (U : ι → (ι → ℝ) → ℝ) (ω : ι → ι → ℝ),
      (∀ l, QuasiconcaveOn ℝ univ (U l) ∧ ∀ i, 0 < ω l i) ∧
      ∀ p ∈ K, ∃ x : ι → ι → ℝ,
        (∀ l, demand (prefOf (U l)) p (cost p (ω l)) = {x l}) ∧ ∑ l, (x l - ω l) = z p := by
  -- A constant `c` making every weight `z_l + c p_l` positive on `K`.
  have hbd : ∀ l, ∃ b, ∀ q ∈ K, b ≤ z q l / q l := by
    intro l
    have hc : ContinuousOn (fun q => z q l / q l) K :=
      ((continuous_apply l).comp_continuousOn hz).div (continuous_apply l).continuousOn
        fun q hq => ((hKS hq).1 l).ne'
    obtain ⟨b, hb⟩ := (hK.image_of_continuousOn hc).isBounded.bddBelow
    exact ⟨b, fun q hq => hb ⟨q, hq, rfl⟩⟩
  choose b hb using hbd
  set c := 1 + ∑ l, |b l|
  have hα : ∀ l, ∀ q ∈ K, 0 < z q l + c * q l := by
    intro l q hq
    have hql := (hKS hq).1 l
    have h1 := hb l q hq
    have h2 : |b l| ≤ ∑ l, |b l| :=
      Finset.single_le_sum (f := fun l => |b l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have h3 : -|b l| ≤ b l := neg_abs_le _
    have h4 : -(∑ l, |b l|) ≤ z q l / q l := by linarith
    rw [le_div_iff₀ hql] at h4
    simp only [c]
    nlinarith
  have hcons : ∀ l, ∃ (U : (ι → ℝ) → ℝ) (ω : ι → ℝ), QuasiconcaveOn ℝ univ U ∧ (∀ i, 0 < ω i) ∧
      ∀ p ∈ K, demand (prefOf U) p (cost p ω) = {ω + debreuPiece z c l p} := fun l =>
    exists_consumer_weightedPiece l hK hKS
      (((continuous_apply l).comp_continuousOn hz).add
        (continuousOn_const.mul (continuous_apply l).continuousOn)) (hα l)
  choose U ω hU hω hdem using hcons
  refine ⟨U, ω, fun l => ⟨hU l, hω l⟩, fun p hp => ⟨fun l => ω l + debreuPiece z c l p,
    fun l => hdem l p hp, ?_⟩⟩
  simp only [add_sub_cancel_left]
  exact sum_debreuPiece c (hKS hp).1 (hW p hp)

/-! ### Witness: a WARP-violating aggregate generated by two rational consumers -/

namespace SMDExamples

theorem isCompact_DBad : IsCompact DBad := by
  have hset : DBad = {p : Fin 2 → ℝ | ∑ i, p i = 1} ∩ ⋂ i, {p | 1 / 8 ≤ p i} := by
    ext p
    simp only [DBad, openPriceSimplex, PositivePrices, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨⟨-, hs⟩, h8⟩; exact ⟨hs, h8⟩
    · rintro ⟨hs, h8⟩; exact ⟨⟨fun i => lt_of_lt_of_le (by norm_num) (h8 i), hs⟩, h8⟩
  have hclosed : IsClosed DBad := by
    rw [hset]
    refine (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_iInter fun i => ?_)
    exact isClosed_le continuous_const (continuous_apply i)
  refine (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).of_isClosed_subset hclosed ?_
  rintro p ⟨⟨hp, hs⟩, -⟩
  refine ⟨fun i => (hp i).le, fun i => ?_⟩
  have := Finset.single_le_sum (f := p) (fun j _ => (hp j).le) (Finset.mem_univ i)
  simp only [Pi.one_apply]
  linarith

theorem continuousOn_zBad : ContinuousOn zBad DBad := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · simp only [zBad, fBad, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    fun_prop
  · simp only [zBad, fBad, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => (hp.1.1 1).ne'

/-- **SMD in action, with consumers.** `zBad` violates the weak axiom in the
aggregate, yet it is exactly the aggregate excess demand of two consumers with
quasiconcave utilities and strictly positive endowments, each with
single-valued demand on `DBad`. Caveat: these consumers are convex but
satiated and discontinuous, as in `sonnenschein_mantel_debreu_quasiconcave`. -/
theorem zBad_rational_consumers : ¬ ExcessWARP zBad DBad ∧
    ∃ (U : Fin 2 → (Fin 2 → ℝ) → ℝ) (ω : Fin 2 → Fin 2 → ℝ),
      (∀ l, QuasiconcaveOn ℝ univ (U l) ∧ ∀ i, 0 < ω l i) ∧
      ∀ p ∈ DBad, ∃ x : Fin 2 → Fin 2 → ℝ,
        (∀ l, demand (prefOf (U l)) p (cost p (ω l)) = {x l}) ∧ ∑ l, (x l - ω l) = zBad p :=
  ⟨not_excessWARP_zBad,
    sonnenschein_mantel_debreu_quasiconcave isCompact_DBad DBad_subset continuousOn_zBad walrasLaw_zBad⟩

end SMDExamples

end Econ
