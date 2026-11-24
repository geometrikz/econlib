/-
# Sonnenschein–Mantel–Debreu with continuous, strongly monotone consumers

PLAN.md §7.2a (bridge B0). Debreu (1974), "Excess demand functions"; Mantel
(1974); Geanakoplos (1984); MWG Prop. 17.E.3.

`SMDConsumer.lean` rationalized each Debreu piece by a quasiconcave utility that
is satiated and discontinuous. Here we build, for each piece, a consumer whose
utility is **continuous** (proved via a Lipschitz bound), **strongly monotone** and
**quasiconcave**, with a strictly positive endowment, whose Walrasian demand is
exactly the piece. This removes satiation and jumps; the only property of
Debreu's consumers still missing is *strict* convexity.

**Construction (derived here).** Fix good `l`, a compact set `K` of prices in
the open simplex with every price at least `2ε`, and a continuous weight
`a > 0` on `K`. Write `‖q‖ = √(q·q)`, `V(q) = q_l/‖q‖`,
`d(q) = e_l − (q_l/‖q‖²) q` and `y(q) = a(q) d(q)` (the piece). Let `Q` be the box
`{q | ε ≤ q_i ≤ 2}` and, for `q ∈ Q`, `p' ∈ K`, level `θ`:

    G(q, p', θ) = a(p') · (q · d(p') + ‖q‖ (V(p') − θ)).

A net trade `x` reaches level `θ` when `∀ q ∈ Q, ∃ p' ∈ K, G(q, p', θ) ≤ q · x`,
and `u(x) = −inf {θ | x reaches θ}`. Each condition is a half-space in `x`, so
upper contour sets are convex. `G` falls in `θ` at rate `a ‖q‖ ∈ [mε, M·2L]`
(a loose but valid upper bound),
which makes `u` Lipschitz (continuous) and, since every `q ∈ Q` is strictly
positive, strictly increasing in each good. Taking `p' = p` shows `y(p)` reaches
`V(p)`; Cauchy–Schwarz shows nothing affordable at `p` reaches below `V(p)`; and
a first-order argument at `q = p − t (x − y(p))` (using only continuity of `a`
and compactness of `K`) shows any other affordable `x` falls short by some
`δ > 0`.

**Scope.** Not proved: strict convexity (the upper contour sets are
intersections of half-spaces and can have flat parts). Consequently each
consumer's demand is guaranteed single-valued only at prices in `K`, not at
every positive price; Debreu's consumers have demand *functions* everywhere.
Off the simplex, demand is homogeneous of degree zero (`demand_smul`), so the
result extends to the cone over `K`. Prices are normalized
to a compact subset of the open simplex, which includes Debreu's `S_ε`.
-/
module

public import EconLean.Bridges.Aggregation.SMDConsumer

@[expose] public section

namespace Econ

open Finset Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Euclidean norm via `cost` -/

/-- The Euclidean norm `√(q·q)`. -/
noncomputable def cnorm (q : ι → ℝ) : ℝ := Real.sqrt (cost q q)

omit [DecidableEq ι] in
theorem cost_self_nonneg' (q : ι → ℝ) : 0 ≤ cost q q :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (q i)

omit [DecidableEq ι] in
theorem cnorm_nonneg (q : ι → ℝ) : 0 ≤ cnorm q := Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem cnorm_sq (q : ι → ℝ) : cnorm q ^ 2 = cost q q := Real.sq_sqrt (cost_self_nonneg' q)

omit [DecidableEq ι] in
theorem cnorm_mul_self (q : ι → ℝ) : cnorm q * cnorm q = cost q q :=
  Real.mul_self_sqrt (cost_self_nonneg' q)

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for `cost`. -/
theorem cost_sq_le (p q : ι → ℝ) : cost p q ^ 2 ≤ cost p p * cost q q := by
  have expand : ∀ i j, (p i * q j - p j * q i) ^ 2
      = (p i * p i) * (q j * q j) + (p j * p j) * (q i * q i) - 2 * ((p i * q i) * (p j * q j)) :=
    fun i j => by ring
  have hA : ∑ i, ∑ j, (p i * p i) * (q j * q j) = cost p p * cost q q := by
    simp only [cost]; exact (Finset.sum_mul_sum _ _ _ _).symm
  have hB : ∑ i, ∑ j, (p j * p j) * (q i * q i) = cost p p * cost q q := by
    rw [Finset.sum_comm]; exact hA
  have hC : ∑ i, ∑ j, (p i * q i) * (p j * q j) = cost p q * cost p q := by
    simp only [cost]; exact (Finset.sum_mul_sum _ _ _ _).symm
  have hsplit : ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2
      = ∑ i, ∑ j, (p i * p i) * (q j * q j) + ∑ i, ∑ j, (p j * p j) * (q i * q i)
        - 2 * ∑ i, ∑ j, (p i * q i) * (p j * q j) := by
    simp only [expand]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hnn : 0 ≤ ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [hsplit, hA, hB, hC] at hnn
  nlinarith

omit [DecidableEq ι] in
theorem abs_cost_le (p q : ι → ℝ) : |cost p q| ≤ cnorm p * cnorm q := by
  rw [cnorm, cnorm, ← Real.sqrt_mul (cost_self_nonneg' p)]
  exact Real.abs_le_sqrt (cost_sq_le p q)

omit [DecidableEq ι] in
theorem cost_le_cnorm_mul (p q : ι → ℝ) : cost p q ≤ cnorm p * cnorm q :=
  (le_abs_self _).trans (abs_cost_le p q)

omit [DecidableEq ι] in
theorem cost_sub_sub (q p : ι → ℝ) :
    cost (q - p) (q - p) = cost q q + cost p p - 2 * cost q p := by
  have h : ∀ i, (q - p) i * (q - p) i = q i * q i + p i * p i - 2 * (q i * p i) := fun i => by
    simp only [Pi.sub_apply]; ring
  simp only [cost, h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [DecidableEq ι] in
theorem cost_comm' (p q : ι → ℝ) : cost p q = cost q p := by
  simp only [cost]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ι] in
/-- Reverse triangle inequality. -/
theorem abs_cnorm_sub_le (q p : ι → ℝ) : |cnorm q - cnorm p| ≤ cnorm (q - p) := by
  refine Real.abs_le_sqrt (x := cnorm q - cnorm p) ?_
  rw [cost_sub_sub, sub_sq, cnorm_sq, cnorm_sq]
  have := cost_le_cnorm_mul q p
  nlinarith

omit [DecidableEq ι] in
theorem abs_apply_le_cnorm (q : ι → ℝ) (i : ι) : |q i| ≤ cnorm q := by
  refine Real.abs_le_sqrt ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => q j * q j) (fun j _ => mul_self_nonneg (q j))
    (Finset.mem_univ i)

omit [DecidableEq ι] in
/-- `‖q‖‖p‖ − q·p ≤ ‖q − p‖²/2`. -/
theorem cnorm_mul_sub_cost_le (q p : ι → ℝ) :
    cnorm q * cnorm p - cost q p ≤ cost (q - p) (q - p) / 2 := by
  rw [cost_sub_sub, ← cnorm_mul_self q, ← cnorm_mul_self p]
  nlinarith [sq_nonneg (cnorm q - cnorm p)]

/-! ### Directions and cosines -/

/-- `d(q) = e_l − (q_l/‖q‖²) q`. -/
noncomputable def dvec (l : ι) (q : ι → ℝ) : ι → ℝ := Pi.single l 1 - (q l / cost q q) • q

theorem weightedPiece_eq_smul_dvec (a : (ι → ℝ) → ℝ) (l : ι) (q : ι → ℝ) :
    weightedPiece a l q = a q • dvec l q := rfl

theorem cost_dvec (l : ι) (p q : ι → ℝ) : cost p (dvec l q) = p l - q l * cost p q / cost q q := by
  rw [dvec, cost_sub_right, cost_smul_right, cost_single_right]
  ring

/-- The Cauchy–Schwarz gap term `(p'_l/‖p'‖²)(‖q‖‖p'‖ − q·p')`. -/
noncomputable def csGap (l : ι) (q p' : ι → ℝ) : ℝ :=
  p' l / cost p' p' * (cnorm q * cnorm p' - cost q p')

omit [DecidableEq ι] in
theorem csGap_nonneg (l : ι) {q p' : ι → ℝ} (hp' : ∀ i, 0 < p' i) : 0 ≤ csGap l q p' := by
  unfold csGap
  by_cases h0 : cost p' p' = 0
  · rw [h0, div_zero, zero_mul]
  · exact mul_nonneg (div_nonneg (hp' l).le (cost_self_nonneg' p'))
      (sub_nonneg.2 (cost_le_cnorm_mul q p'))

omit [DecidableEq ι] in
theorem cost_dvec_eq [Nonempty ι] (l : ι) {q p' : ι → ℝ} (hq : PositivePrices q)
    (hp' : PositivePrices p') :
    q l - p' l * cost q p' / cost p' p' = cnorm q * (dirCos l q - dirCos l p') + csGap l q p' :=
  piece_identity hq hp' l

omit [DecidableEq ι] in
theorem dirCos_eq (l : ι) (q : ι → ℝ) : dirCos l q = q l / cnorm q := rfl

omit [DecidableEq ι] in
theorem cnorm_pos [Nonempty ι] {q : ι → ℝ} (hq : PositivePrices q) : 0 < cnorm q :=
  Real.sqrt_pos.2 (cost_self_pos hq)

omit [DecidableEq ι] in
theorem abs_dirCos_sub_le [Nonempty ι] (l : ι) {q p : ι → ℝ} (hq : PositivePrices q)
    (hp : PositivePrices p) : |dirCos l q - dirCos l p| ≤ 2 * cnorm (q - p) / cnorm q := by
  have nq := cnorm_pos hq
  have np := cnorm_pos hp
  have e : dirCos l q - dirCos l p
      = ((q l - p l) * cnorm p + p l * (cnorm p - cnorm q)) / (cnorm q * cnorm p) := by
    rw [dirCos_eq, dirCos_eq]; field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos nq np), div_le_div_iff₀ (mul_pos nq np) nq]
  have h1 : |q l - p l| ≤ cnorm (q - p) := by
    have := abs_apply_le_cnorm (q - p) l; simpa using this
  have h2 : |cnorm p - cnorm q| ≤ cnorm (q - p) := by
    rw [abs_sub_comm]; exact abs_cnorm_sub_le q p
  have h3 : |p l| ≤ cnorm p := abs_apply_le_cnorm p l
  have hpl : 0 ≤ p l := (hp l).le
  calc |(q l - p l) * cnorm p + p l * (cnorm p - cnorm q)| * cnorm q
      ≤ (|q l - p l| * cnorm p + |p l| * |cnorm p - cnorm q|) * cnorm q := by
        gcongr
        calc _ ≤ |(q l - p l) * cnorm p| + |p l * (cnorm p - cnorm q)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_pos np]
    _ ≤ (cnorm (q - p) * cnorm p + cnorm p * cnorm (q - p)) * cnorm q := by
        gcongr
    _ = 2 * cnorm (q - p) * (cnorm q * cnorm p) := by ring

omit [DecidableEq ι] in
theorem abs_csGap_sub_le (l : ι) {q p p' : ι → ℝ} (hp' : ∀ i, 0 < p' i) :
    |csGap l q p' - csGap l p p'| ≤ 2 * cnorm (q - p) := by
  unfold csGap
  by_cases h0 : cost p' p' = 0
  · simp only [h0, div_zero, zero_mul, sub_self, abs_zero]
    exact mul_nonneg zero_le_two (cnorm_nonneg _)
  have hN : 0 < cost p' p' := lt_of_le_of_ne (cost_self_nonneg' p') (Ne.symm h0)
  have np' : 0 < cnorm p' := Real.sqrt_pos.2 hN
  have hc : 0 ≤ p' l / cost p' p' := div_nonneg (hp' l).le hN.le
  have e : p' l / cost p' p' * (cnorm q * cnorm p' - cost q p')
      - p' l / cost p' p' * (cnorm p * cnorm p' - cost p p')
      = p' l / cost p' p' * ((cnorm q - cnorm p) * cnorm p' - cost (q - p) p') := by
    have : cost (q - p) p' = cost q p' - cost p p' := by
      rw [cost_comm', cost_sub_right, cost_comm' p' q, cost_comm' p' p]
    rw [this]; ring
  rw [e, abs_mul, abs_of_nonneg hc]
  have h1 : |(cnorm q - cnorm p) * cnorm p' - cost (q - p) p'| ≤ 2 * cnorm (q - p) * cnorm p' := by
    calc _ ≤ |(cnorm q - cnorm p) * cnorm p'| + |cost (q - p) p'| := abs_sub _ _
      _ ≤ cnorm (q - p) * cnorm p' + cnorm (q - p) * cnorm p' := by
          gcongr
          · rw [abs_mul, abs_of_pos np']; gcongr; exact abs_cnorm_sub_le q p
          · exact abs_cost_le _ _
      _ = _ := by ring
  have h2 : p' l / cost p' p' * cnorm p' ≤ 1 := by
    rw [← cnorm_mul_self p', div_mul_eq_mul_div, div_le_one (mul_pos np' np'),
      mul_comm (cnorm p') (cnorm p')]
    have := abs_apply_le_cnorm p' l
    rw [abs_of_pos (hp' l)] at this
    nlinarith
  calc p' l / cost p' p' * |(cnorm q - cnorm p) * cnorm p' - cost (q - p) p'|
      ≤ p' l / cost p' p' * (2 * cnorm (q - p) * cnorm p') := by gcongr
    _ = 2 * cnorm (q - p) * (p' l / cost p' p' * cnorm p') := by ring
    _ ≤ 2 * cnorm (q - p) * 1 :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two (cnorm_nonneg _))
    _ = 2 * cnorm (q - p) := mul_one _

/-! ### The construction -/

/-- The box of strictly positive price vectors used to test levels. The upper
bound `2` is arbitrary: it only needs to exceed `1 ≥ p_i` for `p` in the simplex,
so that small perturbations of `p` stay in the box. -/
def priceBox (ε : ℝ) : Set (ι → ℝ) := {q | ∀ i, ε ≤ q i ∧ q i ≤ 2}

/-- `G(q, p', θ) = a(p') (q · d(p') + ‖q‖ (V(p') − θ))`. -/
noncomputable def levelGap (a : (ι → ℝ) → ℝ) (l : ι) (q p' : ι → ℝ) (θ : ℝ) : ℝ :=
  a p' * (cost q (dvec l p') + cnorm q * (dirCos l p' - θ))

/-- `x` reaches level `θ`: for every test price `q` in the box some `p' ∈ K` has
`G(q, p', θ) ≤ q · x`. -/
def ReachesLevel (K : Set (ι → ℝ)) (a : (ι → ℝ) → ℝ) (l : ι) (ε : ℝ) (x : ι → ℝ) (θ : ℝ) :
    Prop :=
  ∀ q ∈ priceBox ε, ∃ p' ∈ K, levelGap a l q p' θ ≤ cost q x

/-- The utility rationalizing the piece. It is continuous, strongly monotone and
quasiconcave under `PieceData K a ε` (otherwise the level set may be empty or
unbounded and `sInf` takes a junk value). -/
noncomputable def stdUtility (K : Set (ι → ℝ)) (a : (ι → ℝ) → ℝ) (l : ι) (ε : ℝ)
    (x : ι → ℝ) : ℝ :=
  -sInf {θ | ReachesLevel K a l ε x θ}

theorem levelGap_add (a : (ι → ℝ) → ℝ) (l : ι) (q p' : ι → ℝ) (θ Δ : ℝ) :
    levelGap a l q p' (θ + Δ) = levelGap a l q p' θ - a p' * cnorm q * Δ := by
  unfold levelGap; ring

section Bounds

variable {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι} {ε : ℝ}

omit [DecidableEq ι] in
theorem cnorm_ge_of_mem_priceBox (hε : 0 ≤ ε) {q : ι → ℝ} (hq : q ∈ priceBox ε) (i : ι) :
    ε ≤ cnorm q := by
  have := abs_apply_le_cnorm q i
  rw [abs_of_nonneg (hε.trans (hq i).1)] at this
  exact (hq i).1.trans this

omit [DecidableEq ι] in
theorem cnorm_le_of_mem_priceBox (hε : 0 ≤ ε) {q : ι → ℝ} (hq : q ∈ priceBox ε) :
    cnorm q ≤ 2 * Fintype.card ι := by
  have hL : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [cnorm, Real.sqrt_le_left (by positivity)]
  · calc cost q q ≤ ∑ _i : ι, (4 : ℝ) := Finset.sum_le_sum fun i _ => by
          have := hq i; nlinarith
      _ = 4 * Fintype.card ι := by simp [mul_comm]
      _ ≤ (2 * Fintype.card ι) ^ 2 := by
          rcases (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _).eq_or_lt with h | h
          · rw [← h]; norm_num
          · have : (1 : ℝ) ≤ Fintype.card ι := by
              exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast h.ne')
            nlinarith

omit [DecidableEq ι] in
theorem abs_cost_le_of_mem_priceBox (hε : 0 ≤ ε) {q : ι → ℝ} (hq : q ∈ priceBox ε)
    (x : ι → ℝ) : |cost q x| ≤ 2 * Fintype.card ι * ‖x‖ := by
  calc |cost q x| ≤ ∑ i, |q i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, 2 * ‖x‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hε.trans (hq i).1)]
        exact mul_le_mul (hq i).2 (norm_le_pi_norm x i) (abs_nonneg _) zero_le_two
    _ = 2 * Fintype.card ι * ‖x‖ := by simp; ring

theorem abs_cost_dvec_add_le [Nonempty ι] (hε : 0 ≤ ε) {q p' : ι → ℝ} (hq : q ∈ priceBox ε)
    (hp' : PositivePrices p') :
    |cost q (dvec l p') + cnorm q * dirCos l p'| ≤ 6 * Fintype.card ι := by
  have hN := cost_self_pos hp'
  have hd : ∀ i, |dvec l p' i| ≤ 2 := by
    intro i
    have np := cnorm_pos hp'
    have h1 : |p' l * p' i| ≤ cost p' p' := by
      rw [abs_mul, ← cnorm_mul_self]
      exact mul_le_mul (abs_apply_le_cnorm p' l) (abs_apply_le_cnorm p' i) (abs_nonneg _)
        (cnorm_nonneg _)
    simp only [dvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    have h2 : |p' l / cost p' p' * p' i| ≤ 1 := by
      rw [div_mul_eq_mul_div, abs_div, abs_of_pos hN, div_le_one hN]; exact h1
    have h3 : |(if i = l then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc _ ≤ |(if i = l then (1 : ℝ) else 0)| + |p' l / cost p' p' * p' i| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hc : |cost q (dvec l p')| ≤ 4 * Fintype.card ι := by
    calc |cost q (dvec l p')| ≤ ∑ i, |q i * dvec l p' i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, (4 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hε.trans (hq i).1)]
          exact (mul_le_mul (hq i).2 (hd i) (abs_nonneg _) zero_le_two).trans (by norm_num)
      _ = 4 * Fintype.card ι := by simp [mul_comm]
  have hv0 := (dirCos_pos hp' l).le
  have hv1 := dirCos_le_one hp' l
  have hn := cnorm_le_of_mem_priceBox hε hq
  have hn0 := cnorm_nonneg q
  have : |cnorm q * dirCos l p'| ≤ 2 * Fintype.card ι := by
    rw [abs_of_nonneg (mul_nonneg hn0 hv0)]
    calc cnorm q * dirCos l p' ≤ cnorm q * 1 := by gcongr
      _ ≤ _ := by linarith
  calc _ ≤ |cost q (dvec l p')| + |cnorm q * dirCos l p'| := abs_add_le _ _
    _ ≤ _ := by linarith

end Bounds

/-- `sInf S' ≤ sInf S + c` when every `θ ∈ S` gives `θ + c ∈ S'`. -/
theorem sInf_le_sInf_add {S S' : Set ℝ} (hS : S.Nonempty) (hS' : BddBelow S') {c : ℝ}
    (hc : ∀ θ ∈ S, θ + c ∈ S') : sInf S' ≤ sInf S + c := by
  have : sInf S' - c ≤ sInf S := le_csInf hS fun θ hθ => by
    have := csInf_le hS' (hc θ hθ); linarith
  linarith

/-- `y(p)` reaches level `V(p)` (take `p' = p`). -/
theorem reaches_self {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {l : ι} {ε : ℝ} {p : ι → ℝ}
    (hp : p ∈ K) : ReachesLevel K a l ε (weightedPiece a l p) (dirCos l p) := fun q _ =>
  ⟨p, hp, by rw [levelGap, sub_self, mul_zero, add_zero, weightedPiece_eq_smul_dvec,
    cost_smul_right]⟩

/-! ### Standing hypotheses -/

/-- The data of one Debreu piece: a compact price set `K` in the open simplex,
bounded away from the boundary by `2ε`, and a continuous positive weight. -/
structure PieceData (K : Set (ι → ℝ)) (a : (ι → ℝ) → ℝ) (ε : ℝ) : Prop where
  compact : IsCompact K
  nonempty : K.Nonempty
  subset : K ⊆ openPriceSimplex ι
  eps_pos : 0 < ε
  ge_eps : ∀ p ∈ K, ∀ i, 2 * ε ≤ p i
  cont : ContinuousOn a K
  pos : ∀ q ∈ K, 0 < a q

namespace PieceData

variable {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ} {ε : ℝ} {l : ι} (h : PieceData K a ε)
include h

omit [DecidableEq ι] in
theorem nonemptyι : Nonempty ι := by
  obtain ⟨p, hp⟩ := h.nonempty
  by_contra hι
  rw [not_nonempty_iff] at hι
  simpa using (h.subset hp).2

omit [DecidableEq ι] in
theorem mem_priceBox {p : ι → ℝ} (hp : p ∈ K) : p ∈ priceBox ε := by
  intro i
  refine ⟨by linarith [h.ge_eps p hp i, h.eps_pos], ?_⟩
  have := Finset.single_le_sum (f := p) (fun j _ => ((h.subset hp).1 j).le) (Finset.mem_univ i)
  rw [(h.subset hp).2] at this
  linarith

omit [DecidableEq ι] in
theorem exists_min : ∃ m > 0, ∀ q ∈ K, m ≤ a q := by
  obtain ⟨q, hq, hmin⟩ := h.compact.exists_isMinOn h.nonempty h.cont
  exact ⟨a q, h.pos q hq, fun q' hq' => hmin hq'⟩

omit [DecidableEq ι] in
theorem exists_max : ∃ M > 0, ∀ q ∈ K, a q ≤ M := by
  obtain ⟨q, hq, hmax⟩ := h.compact.exists_isMaxOn h.nonempty h.cont
  exact ⟨a q, h.pos q hq, fun q' hq' => hmax hq'⟩

theorem levels_nonempty (x : ι → ℝ) : {θ | ReachesLevel K a l ε x θ}.Nonempty := by
  have := h.nonemptyι
  obtain ⟨m, hm, hma⟩ := h.exists_min
  obtain ⟨p₀, hp₀⟩ := h.nonempty
  set L : ℝ := (Fintype.card ι : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hε := h.eps_pos
  refine ⟨(6 * L + 2 * L * ‖x‖ / m) / ε, fun q hq => ⟨p₀, hp₀, ?_⟩⟩
  have hB := abs_cost_dvec_add_le (l := l) h.eps_pos.le hq (h.subset hp₀).1
  have hn := cnorm_ge_of_mem_priceBox h.eps_pos.le hq (Classical.arbitrary ι)
  have hx := abs_cost_le_of_mem_priceBox h.eps_pos.le hq x
  have hθ : 0 ≤ (6 * L + 2 * L * ‖x‖ / m) / ε := by positivity
  have key : cost q (dvec l p₀) + cnorm q * (dirCos l p₀ - (6 * L + 2 * L * ‖x‖ / m) / ε)
      ≤ -(2 * L * ‖x‖ / m) := by
    have : ε * ((6 * L + 2 * L * ‖x‖ / m) / ε) = 6 * L + 2 * L * ‖x‖ / m := by
      field_simp [h.eps_pos.ne']
    have h1 : ε * ((6 * L + 2 * L * ‖x‖ / m) / ε) ≤ cnorm q * ((6 * L + 2 * L * ‖x‖ / m) / ε) :=
      mul_le_mul_of_nonneg_right hn hθ
    have h2 := (abs_le.1 hB).2
    nlinarith
  have hapos := h.pos p₀ hp₀
  have hma0 := hma p₀ hp₀
  unfold levelGap
  have hnx : 0 ≤ 2 * L * ‖x‖ / m := by positivity
  calc a p₀ * (cost q (dvec l p₀) + cnorm q * (dirCos l p₀ - (6 * L + 2 * L * ‖x‖ / m) / ε))
      ≤ m * (cost q (dvec l p₀) + cnorm q * (dirCos l p₀ - (6 * L + 2 * L * ‖x‖ / m) / ε)) :=
        mul_le_mul_of_nonpos_right hma0 (by linarith)
    _ ≤ m * (-(2 * L * ‖x‖ / m)) := by gcongr
    _ = -(2 * L * ‖x‖) := by field_simp
    _ ≤ cost q x := by linarith [(abs_le.1 hx).1]

theorem levels_bddBelow (x : ι → ℝ) : BddBelow {θ | ReachesLevel K a l ε x θ} := by
  have := h.nonemptyι
  obtain ⟨m, hm, hma⟩ := h.exists_min
  obtain ⟨p₀, hp₀⟩ := h.nonempty
  set L : ℝ := (Fintype.card ι : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hε := h.eps_pos
  refine ⟨-((6 * L + 2 * L * ‖x‖ / m) / ε), fun θ hθ => ?_⟩
  by_contra hlt
  push Not at hlt
  have hq := h.mem_priceBox hp₀
  obtain ⟨p', hp', hle⟩ := hθ p₀ hq
  have hB := abs_cost_dvec_add_le (l := l) h.eps_pos.le hq (h.subset hp').1
  have hn := cnorm_ge_of_mem_priceBox h.eps_pos.le hq (Classical.arbitrary ι)
  have hx := abs_cost_le_of_mem_priceBox h.eps_pos.le hq x
  have hθ0 : θ < 0 := lt_of_lt_of_le hlt (by
    have : 0 ≤ (6 * L + 2 * L * ‖x‖ / m) / ε := by positivity
    linarith)
  have key : 2 * L * ‖x‖ / m < cost p₀ (dvec l p') + cnorm p₀ * (dirCos l p' - θ) := by
    have : ε * (-θ) ≤ cnorm p₀ * (-θ) := mul_le_mul_of_nonneg_right hn (by linarith)
    have h3 : 6 * L + 2 * L * ‖x‖ / m < ε * (-θ) := by
      have : (6 * L + 2 * L * ‖x‖ / m) / ε < -θ := by linarith
      exact (div_lt_iff₀' h.eps_pos).1 this
    have h2 := (abs_le.1 hB).1
    nlinarith
  have hma0 := hma p' hp'
  have hnx : 0 ≤ 2 * L * ‖x‖ / m := by positivity
  have : 2 * L * ‖x‖ < levelGap a l p₀ p' θ := by
    unfold levelGap
    calc 2 * L * ‖x‖ = m * (2 * L * ‖x‖ / m) := by field_simp
      _ < m * (cost p₀ (dvec l p') + cnorm p₀ * (dirCos l p' - θ)) := by gcongr
      _ ≤ a p' * (cost p₀ (dvec l p') + cnorm p₀ * (dirCos l p' - θ)) :=
          mul_le_mul_of_nonneg_right hma0 (by linarith)
  linarith [(abs_le.1 hx).2]

theorem reaches_mono {x : ι → ℝ} {θ θ' : ℝ} (hx : ReachesLevel K a l ε x θ) (hθ : θ ≤ θ') :
    ReachesLevel K a l ε x θ' := by
  intro q hq
  obtain ⟨p', hp', hle⟩ := hx q hq
  refine ⟨p', hp', le_trans ?_ hle⟩
  have : θ' = θ + (θ' - θ) := by ring
  rw [this, levelGap_add]
  have := mul_nonneg (mul_nonneg (h.pos p' hp').le (cnorm_nonneg q)) (sub_nonneg.2 hθ)
  linarith

/-- **Lipschitz shift.** Reaching `θ` from `x` implies reaching
`θ + 2L‖x − x'‖/(mε)` from `x'`. -/
theorem reaches_shift {m : ℝ} (hm : 0 < m) (hma : ∀ q ∈ K, m ≤ a q) {x x' : ι → ℝ} {θ : ℝ}
    (hx : ReachesLevel K a l ε x θ) :
    ReachesLevel K a l ε x' (θ + 2 * Fintype.card ι * ‖x - x'‖ / (m * ε)) := by
  intro q hq
  obtain ⟨p', hp', hle⟩ := hx q hq
  refine ⟨p', hp', ?_⟩
  rw [levelGap_add]
  have hn := cnorm_ge_of_mem_priceBox h.eps_pos.le hq
  have hxx := abs_cost_le_of_mem_priceBox h.eps_pos.le hq (x - x')
  rw [cost_sub_right] at hxx
  have hΔ : 0 ≤ 2 * (Fintype.card ι : ℝ) * ‖x - x'‖ / (m * ε) := by
    have := h.eps_pos; positivity
  have hεn : m * ε ≤ a p' * cnorm q := by
    obtain ⟨i⟩ := h.nonemptyι
    exact mul_le_mul (hma p' hp') (hn i) h.eps_pos.le (h.pos p' hp').le
  have : m * ε * (2 * (Fintype.card ι : ℝ) * ‖x - x'‖ / (m * ε))
      = 2 * (Fintype.card ι : ℝ) * ‖x - x'‖ := by
    field_simp [hm.ne', h.eps_pos.ne']
  have := mul_le_mul_of_nonneg_right hεn hΔ
  linarith [(abs_le.1 hxx).2]

/-- **Continuity**: the utility is Lipschitz. -/
theorem stdUtility_lipschitz (x x' : ι → ℝ) {m : ℝ} (hm : 0 < m) (hma : ∀ q ∈ K, m ≤ a q) :
    |stdUtility K a l ε x - stdUtility K a l ε x'|
      ≤ 2 * Fintype.card ι / (m * ε) * ‖x - x'‖ := by
  have h1 := sInf_le_sInf_add (h.levels_nonempty (l := l) x) (h.levels_bddBelow x')
    (c := 2 * Fintype.card ι * ‖x - x'‖ / (m * ε)) fun θ hθ => h.reaches_shift hm hma hθ
  have h2 := sInf_le_sInf_add (h.levels_nonempty (l := l) x') (h.levels_bddBelow x)
    (c := 2 * Fintype.card ι * ‖x' - x‖ / (m * ε)) fun θ hθ => h.reaches_shift hm hma hθ
  rw [norm_sub_rev x' x] at h2
  unfold stdUtility
  rw [abs_le]
  have e : 2 * (Fintype.card ι : ℝ) * ‖x - x'‖ / (m * ε)
      = 2 * Fintype.card ι / (m * ε) * ‖x - x'‖ := by ring
  constructor <;> linarith

theorem continuous_stdUtility : Continuous (stdUtility K a l ε) := by
  obtain ⟨m, hm, hma⟩ := h.exists_min
  set κ : ℝ := 2 * Fintype.card ι / (m * ε)
  have hκ : 0 ≤ κ := by have := h.eps_pos; positivity
  refine (LipschitzWith.of_dist_le_mul (K := ⟨κ, hκ⟩) fun x x' => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact h.stdUtility_lipschitz x x' hm hma

/-- **Strong monotonicity.** -/
theorem stdUtility_strictMono {x x' : ι → ℝ} (hle : x ≤ x') (hne : x ≠ x') :
    stdUtility K a l ε x < stdUtility K a l ε x' := by
  have := h.nonemptyι
  obtain ⟨M, hM, hMa⟩ := h.exists_max
  obtain ⟨i, hi⟩ : ∃ i, x i < x' i := by
    by_contra hc
    push Not at hc
    exact hne (funext fun j => le_antisymm (hle j) (hc j))
  set L : ℝ := (Fintype.card ι : ℝ)
  have hL : 0 < L := by simp only [L]; exact_mod_cast Fintype.card_pos
  set Δ := ε * (x' i - x i) / (M * (2 * L))
  have hΔ : 0 < Δ := by have := h.eps_pos; have : 0 < x' i - x i := by linarith
                        positivity
  have hshift : ∀ θ ∈ {θ | ReachesLevel K a l ε x θ}, θ + (-Δ) ∈ {θ | ReachesLevel K a l ε x' θ} := by
    intro θ hθ q hq
    obtain ⟨p', hp', hle'⟩ := hθ q hq
    refine ⟨p', hp', ?_⟩
    rw [levelGap_add]
    have hn := cnorm_le_of_mem_priceBox h.eps_pos.le hq
    have hgain : ε * (x' i - x i) ≤ cost q x' - cost q x := by
      rw [← cost_sub_right]
      calc ε * (x' i - x i) ≤ q i * (x' - x) i := by
            simp only [Pi.sub_apply]
            exact mul_le_mul_of_nonneg_right (hq i).1 (by linarith)
        _ ≤ cost q (x' - x) := Finset.single_le_sum (f := fun j => q j * (x' - x) j)
            (fun j _ => mul_nonneg (h.eps_pos.le.trans (hq j).1) (sub_nonneg.2 (hle j)))
            (Finset.mem_univ i)
    have hc : a p' * cnorm q * Δ ≤ M * (2 * L) * Δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hMa p' hp') hn (cnorm_nonneg q) hM.le) hΔ.le
    have : M * (2 * L) * Δ = ε * (x' i - x i) := by
      simp only [Δ]; field_simp
    linarith
  have := sInf_le_sInf_add (h.levels_nonempty (l := l) x) (h.levels_bddBelow x') hshift
  unfold stdUtility
  linarith

/-- **Convex preferences.** -/
theorem quasiconcaveOn_stdUtility : QuasiconcaveOn ℝ univ (stdUtility K a l ε) := by
  have hconv : ∀ θ x₁ x₂, ReachesLevel K a l ε x₁ θ → ReachesLevel K a l ε x₂ θ →
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 → ReachesLevel K a l ε (s • x₁ + t • x₂) θ := by
    intro θ x₁ x₂ h₁ h₂ s t hs ht hst q hq
    obtain ⟨p₁, hp₁, hle₁⟩ := h₁ q hq
    obtain ⟨p₂, hp₂, hle₂⟩ := h₂ q hq
    have hc : cost q (s • x₁ + t • x₂) = s * cost q x₁ + t * cost q x₂ := by
      rw [cost_add_right, cost_smul_right, cost_smul_right]
    rcases le_total (levelGap a l q p₁ θ) (levelGap a l q p₂ θ) with h12 | h12
    · refine ⟨p₁, hp₁, ?_⟩; rw [hc]
      have e : levelGap a l q p₁ θ = s * levelGap a l q p₁ θ + t * levelGap a l q p₁ θ := by
        rw [← add_mul, hst, one_mul]
      nlinarith [mul_nonneg hs (sub_nonneg.2 hle₁), mul_nonneg ht (sub_nonneg.2 (h12.trans hle₂))]
    · refine ⟨p₂, hp₂, ?_⟩; rw [hc]
      have e : levelGap a l q p₂ θ = s * levelGap a l q p₂ θ + t * levelGap a l q p₂ θ := by
        rw [← add_mul, hst, one_mul]
      nlinarith [mul_nonneg ht (sub_nonneg.2 hle₂), mul_nonneg hs (sub_nonneg.2 (h12.trans hle₁))]
  intro r x₁ hx₁ x₂ hx₂ s t hs ht hst
  refine ⟨mem_univ _, ?_⟩
  simp only [mem_ofPred_eq, stdUtility] at hx₁ hx₂ ⊢
  have h₁ : sInf {θ | ReachesLevel K a l ε x₁ θ} ≤ -r := by linarith [hx₁.2]
  have h₂ : sInf {θ | ReachesLevel K a l ε x₂ θ} ≤ -r := by linarith [hx₂.2]
  rw [Real.sInf_le_iff (h.levels_bddBelow _) (h.levels_nonempty _)] at h₁ h₂
  suffices sInf {θ | ReachesLevel K a l ε (s • x₁ + t • x₂) θ} ≤ -r by linarith
  rw [Real.sInf_le_iff (h.levels_bddBelow _) (h.levels_nonempty _)]
  intro e he
  obtain ⟨θ₁, hθ₁, hθ₁e⟩ := h₁ e he
  obtain ⟨θ₂, hθ₂, hθ₂e⟩ := h₂ e he
  exact ⟨max θ₁ θ₂, hconv _ _ _ (h.reaches_mono hθ₁ (le_max_left _ _))
    (h.reaches_mono hθ₂ (le_max_right _ _)) s t hs ht hst, max_lt hθ₁e hθ₂e⟩

/-- Nothing affordable at `p` reaches a level below `V(p)`. -/
theorem not_reaches_below {p : ι → ℝ} (hp : p ∈ K) {x : ι → ℝ} (hx : cost p x ≤ 0) {θ : ℝ}
    (hθ : θ < dirCos l p) : ¬ ReachesLevel K a l ε x θ := by
  have := h.nonemptyι
  intro hr
  obtain ⟨p', hp', hle⟩ := hr p (h.mem_priceBox hp)
  have hpS := h.subset hp
  have hp'S := h.subset hp'
  have hid := cost_dvec_eq l hpS.1 hp'S.1
  rw [← cost_dvec] at hid
  have hg := csGap_nonneg l (q := p) hp'S.1
  have hpos : 0 < levelGap a l p p' θ := by
    unfold levelGap
    refine mul_pos (h.pos p' hp') ?_
    rw [hid]
    have := mul_pos (cnorm_pos hpS.1) (sub_pos.2 hθ)
    nlinarith
  linarith

/-- **Quantitative uniqueness.** An affordable `x ≠ y(p)` falls short of every
level below `V(p) + δ`, for some `δ > 0`. Test price: `q = p − t (x − y(p))`. -/
theorem exists_gap {p : ι → ℝ} (hp : p ∈ K) {x : ι → ℝ} (hx : cost p x ≤ 0)
    (hne : x ≠ weightedPiece a l p) :
    ∃ δ > 0, ∀ θ, θ < dirCos l p + δ → ¬ ReachesLevel K a l ε x θ := by
  have := h.nonemptyι
  have hε := h.eps_pos
  obtain ⟨m, hm, hma⟩ := h.exists_min
  obtain ⟨M, hM, hMa⟩ := h.exists_max
  have hpS := h.subset hp
  set L : ℝ := (Fintype.card ι : ℝ)
  have hL : 0 < L := by simp only [L]; exact_mod_cast Fintype.card_pos
  set N := 2 * L with hN_def
  have hN : 0 < N := by positivity
  set y := weightedPiece a l p with hy_def
  set w := x - y with hw_def
  have hw : w ≠ 0 := sub_ne_zero.2 hne
  set γ := cost w w with hγ_def
  have hγ : 0 < γ := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc; push Not at hc; exact hw (funext hc)
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (w j))
      ⟨i, Finset.mem_univ i, mul_self_pos.2 hi⟩
  set nw := cnorm w with hnw_def
  have hnw : 0 < nw := Real.sqrt_pos.2 hγ
  have hcy : cost p y = 0 := by
    rw [hy_def, cost_weightedPiece]
    have : p l - p l * cost p p / cost p p = 0 := by
      field_simp [(cost_self_pos hpS.1).ne']; ring
    rw [this, mul_zero]
  have hpw : cost p w ≤ 0 := by rw [hw_def, cost_sub_right, hcy]; linarith
  have hNp := cost_self_pos hpS.1
  set CV := 2 * nw / ε with hCV_def
  have hCV : 0 < CV := by positivity
  set Cg := p l / cost p p * γ / 2 with hCg_def
  have hCg : 0 ≤ Cg := by have := hpS.1 l; positivity
  set η₀ := γ / (4 * N * CV) with hη₀_def
  have hη₀ : 0 < η₀ := by positivity
  -- Far weights: `csGap l p ·` is bounded below by `μ > 0` where `a` is far from `a p`.
  obtain ⟨μ, hμ, hμF⟩ : ∃ μ > 0, ∀ p' ∈ K, η₀ ≤ |a p' - a p| → μ ≤ csGap l p p' := by
    set F := K ∩ (fun p' => |a p' - a p|) ⁻¹' Ici η₀
    have hFc : IsCompact F := h.compact.of_isClosed_subset
      ((h.cont.sub continuousOn_const).abs.preimage_isClosed_of_isClosed h.compact.isClosed
        isClosed_Ici) inter_subset_left
    rcases F.eq_empty_or_nonempty with hE | hF
    · refine ⟨1, one_pos, fun p' hp' hfar => ?_⟩
      have : p' ∈ F := ⟨hp', hfar⟩
      simp [hE] at this
    have hcost : Continuous fun q : ι → ℝ => cost q q := by unfold cost; fun_prop
    have hcp : Continuous fun q : ι → ℝ => cost p q := by unfold cost; fun_prop
    have hgc : ContinuousOn (fun p' => csGap l p p') K := by
      unfold csGap cnorm
      refine ((continuous_apply l).continuousOn.div hcost.continuousOn
        fun q hq => (cost_self_pos (h.subset hq).1).ne').mul ?_
      exact (continuousOn_const.mul (Real.continuous_sqrt.comp hcost).continuousOn).sub
        hcp.continuousOn
    obtain ⟨p₀, hp₀, hmin⟩ := hFc.exists_isMinOn hF (hgc.mono inter_subset_left)
    refine ⟨csGap l p p₀, ?_, fun p' hp' hfar => hmin ⟨hp', hfar⟩⟩
    have hne₀ : p ≠ p₀ := by
      rintro rfl
      have : η₀ ≤ |a p - a p| := hp₀.2
      simp at this; linarith
    have hp₀S := h.subset hp₀.1
    exact mul_pos (div_pos (hp₀S.1 l) (cost_self_pos hp₀S.1)) (cs_gap_pos hpS hp₀S hne₀)
  -- The step size `t`.
  set S := 2 * M * N * CV + 2 * m * nw + M * Cg + 1 with hS_def
  have hS : 0 < S := by positivity
  set t := min (min (ε / nw) (1 / nw)) (min (min (γ / (4 * M * Cg + 1)) 1) (m * μ / (3 * S)))
    with ht_def
  have ht : 0 < t := by
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (lt_min ?_ one_pos) ?_) <;>
      positivity
  have ht1 : t * nw ≤ ε := by
    have : t ≤ ε / nw := (min_le_left _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hnw] at this
  have ht2 : t * nw ≤ 1 := by
    have : t ≤ 1 / nw := (min_le_left _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hnw] at this
  have ht3 : M * Cg * t ≤ γ / 4 := by
    have h1 : t ≤ γ / (4 * M * Cg + 1) :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : M * Cg * t ≤ M * Cg * (γ / (4 * M * Cg + 1)) := by gcongr
    have h3 : M * Cg * (γ / (4 * M * Cg + 1)) ≤ γ / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hM.le hCg]
    linarith
  have ht4 : t ≤ 1 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht5 : t * S ≤ m * μ / 3 := by
    have : t ≤ m * μ / (3 * S) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- The test price.
  set q := p - t • w with hq_def
  have hqbox : q ∈ priceBox ε := by
    intro i
    have hwi := abs_apply_le_cnorm w i
    have hti : |t * w i| ≤ t * nw := by
      rw [abs_mul, abs_of_pos ht]; exact mul_le_mul_of_nonneg_left hwi ht.le
    have hpi := (h.mem_priceBox hp i)
    have hpi2 := h.ge_eps p hp i
    have hp1 : p i ≤ 1 := by
      have := Finset.single_le_sum (f := p) (fun j _ => (hpS.1 j).le) (Finset.mem_univ i)
      rw [hpS.2] at this; exact this
    simp only [hq_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith [(abs_le.1 hti).1, (abs_le.1 hti).2]
  have hqpos : PositivePrices q := fun i => lt_of_lt_of_le hε (hqbox i).1
  have hqp : cnorm (q - p) = t * nw := by
    have e : q - p = (-t) • w := by rw [hq_def]; ext i; simp
    rw [e, cnorm, cost_smul_left, cost_smul_right, ← mul_assoc, neg_mul_neg,
      Real.sqrt_mul (by positivity), Real.sqrt_mul_self ht.le]
    rfl
  have hnq : cnorm q ≤ N := cnorm_le_of_mem_priceBox hε.le hqbox
  have hnq0 := cnorm_nonneg q
  have hnqε : ε ≤ cnorm q := cnorm_ge_of_mem_priceBox hε.le hqbox (Classical.arbitrary ι)
  set D := cnorm q * (dirCos l q - dirCos l p) with hD_def
  have hD : |D| ≤ N * CV * t := by
    have hV := abs_dirCos_sub_le l hqpos hpS.1
    rw [hqp] at hV
    have hV' : |dirCos l q - dirCos l p| ≤ CV * t := by
      calc _ ≤ 2 * (t * nw) / cnorm q := hV
        _ ≤ 2 * (t * nw) / ε := by gcongr
        _ = CV * t := by rw [hCV_def]; ring
    rw [hD_def, abs_mul, abs_of_nonneg hnq0]
    calc cnorm q * |dirCos l q - dirCos l p| ≤ N * (CV * t) :=
          mul_le_mul hnq hV' (abs_nonneg _) hN.le
      _ = N * CV * t := by ring
  have hgp : csGap l q p ≤ Cg * t ^ 2 := by
    have h1 := cnorm_mul_sub_cost_le q p
    have h2 : cost (q - p) (q - p) = t ^ 2 * γ := by
      rw [← cnorm_mul_self, hqp, hγ_def, ← cnorm_mul_self w]; ring
    unfold csGap
    rw [h2] at h1
    have hc : 0 ≤ p l / cost p p := by have := hpS.1 l; positivity
    calc p l / cost p p * (cnorm q * cnorm p - cost q p) ≤ p l / cost p p * (t ^ 2 * γ / 2) := by
          gcongr
      _ = Cg * t ^ 2 := by rw [hCg_def]; ring
  have hgp0 : 0 ≤ csGap l q p := csGap_nonneg l hpS.1
  -- The per-`p'` estimate.
  have hE : ∀ p' ∈ K, cost q (dvec l p') + cnorm q * (dirCos l p' - dirCos l p)
      = D + csGap l q p' := by
    intro p' hp'
    rw [cost_dvec, cost_dvec_eq l hqpos (h.subset hp').1, hD_def]; ring
  have key : ∀ p' ∈ K, a p * (D + csGap l q p) - γ * t / 2 ≤ a p' * (D + csGap l q p') := by
    intro p' hp'
    have hap' := h.pos p' hp'
    have hap := h.pos p hp
    have hMp' := hMa p' hp'
    have hMp := hMa p hp
    have hg' := csGap_nonneg l (q := q) (h.subset hp').1
    have hapg : a p * csGap l q p ≤ γ * t / 4 := by
      calc a p * csGap l q p ≤ M * (Cg * t ^ 2) := mul_le_mul hMp hgp hgp0 hM.le
        _ = (M * Cg * t) * t := by ring
        _ ≤ γ / 4 * t := by gcongr
        _ = γ * t / 4 := by ring
    have hDl := (abs_le.1 hD).1
    have hDu := (abs_le.1 hD).2
    rcases lt_or_ge (|a p' - a p|) η₀ with hnear | hfar
    · -- Near: `(a p' − a p) D ≥ −η₀ N CV t = −γt/4`.
      have h1 : -(η₀ * (N * CV * t)) ≤ (a p' - a p) * D := by
        have := abs_mul (a p' - a p) D
        have h2 : |(a p' - a p) * D| ≤ η₀ * (N * CV * t) := by
          rw [abs_mul]; exact mul_le_mul hnear.le hD (abs_nonneg _) hη₀.le
        linarith [(abs_le.1 h2).1]
      have h3 : η₀ * (N * CV * t) = γ * t / 4 := by
        rw [hη₀_def]; field_simp
      have h4 : 0 ≤ a p' * csGap l q p' := mul_nonneg hap'.le hg'
      have e1 : a p * (D + csGap l q p) = a p * D + a p * csGap l q p := by ring
      have e2 : a p' * (D + csGap l q p')
          = a p * D + (a p' - a p) * D + a p' * csGap l q p' := by ring
      rw [e1, e2]; linarith
    · -- Far: the gap term dominates.
      have hμp := hμF p' hp' hfar
      have hgu := abs_csGap_sub_le l (q := q) (p := p) (h.subset hp').1
      rw [hqp] at hgu
      have hg'μ : μ - 2 * (t * nw) ≤ csGap l q p' := by linarith [(abs_le.1 hgu).1]
      have hdiff : |a p' - a p| ≤ M := by
        rw [abs_le]; constructor <;> linarith
      have h1 : -(M * (N * CV * t)) ≤ (a p' - a p) * D := by
        have h2 : |(a p' - a p) * D| ≤ M * (N * CV * t) := by
          rw [abs_mul]; exact mul_le_mul hdiff hD (abs_nonneg _) hM.le
        linarith [(abs_le.1 h2).1]
      have hA : 0 ≤ M * (N * CV * t) := by positivity
      have hB : 0 ≤ M * Cg * t := by positivity
      have hSe : t * S = 2 * (M * (N * CV * t)) + 2 * m * nw * t + M * Cg * t + t := by
        rw [hS_def]; ring
      have hmμ : 0 ≤ m * μ := by positivity
      have hsum : M * (N * CV * t) + 2 * m * nw * t ≤ m * μ := by linarith
      have hpos2 : 0 ≤ μ - 2 * (t * nw) := by
        have h7 : m * (2 * (t * nw)) ≤ m * μ := by
          have : m * (2 * (t * nw)) = 2 * m * nw * t := by ring
          linarith
        have := le_of_mul_le_mul_left h7 hm
        linarith
      have h5 : m * (μ - 2 * (t * nw)) ≤ a p' * csGap l q p' :=
        mul_le_mul (hma p' hp') hg'μ hpos2 hap'.le
      have h8 : m * (μ - 2 * (t * nw)) = m * μ - 2 * m * nw * t := by ring
      have hγt : 0 ≤ γ * t := by positivity
      have e1 : a p * (D + csGap l q p) = a p * D + a p * csGap l q p := by ring
      have e2 : a p' * (D + csGap l q p')
          = a p * D + (a p' - a p) * D + a p' * csGap l q p' := by ring
      rw [e1, e2]; linarith
  -- Conclude.
  set δ := γ * t / (4 * M * N) with hδ_def
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, fun θ hθ hr => ?_⟩
  obtain ⟨p', hp', hle⟩ := hr q hqbox
  have hap' := h.pos p' hp'
  have hlg : levelGap a l q p' θ
      = a p' * (D + csGap l q p') - a p' * cnorm q * (θ - dirCos l p) := by
    rw [levelGap, ← hE p' hp']; ring
  have hshift : a p' * cnorm q * (θ - dirCos l p) ≤ γ * t / 4 := by
    have hMN : a p' * cnorm q ≤ M * N := mul_le_mul (hMa p' hp') hnq hnq0 hM.le
    have h0 : 0 ≤ a p' * cnorm q := mul_nonneg hap'.le hnq0
    rcases le_or_gt (θ - dirCos l p) 0 with hneg | hpos
    · have := mul_nonpos_of_nonneg_of_nonpos h0 hneg
      have : 0 ≤ γ * t / 4 := by positivity
      linarith
    · calc a p' * cnorm q * (θ - dirCos l p) ≤ M * N * δ :=
            mul_le_mul hMN (by linarith) hpos.le (by positivity)
        _ = γ * t / 4 := by rw [hδ_def]; field_simp
  have hself : a p * (D + csGap l q p) = cost q y := by
    have := hE p hp
    rw [sub_self, mul_zero, add_zero] at this
    rw [← this, hy_def, weightedPiece_eq_smul_dvec, cost_smul_right]
  have hcq : cost q x ≤ cost q y - γ * t := by
    have : cost q w = cost p w - t * γ := by
      rw [hq_def, cost_sub_left, cost_smul_left]
    have hxw : x = y + w := by rw [hw_def]; abel
    rw [hxw, cost_add_right]
    have e : t * γ = γ * t := mul_comm _ _
    linarith
  have := key p' hp'
  have hγt : 0 < γ * t := by positivity
  linarith

theorem stdUtility_self {p : ι → ℝ} (hp : p ∈ K) :
    stdUtility K a l ε (weightedPiece a l p) = -dirCos l p := by
  have := h.nonemptyι
  have hc : cost p (weightedPiece a l p) = 0 := by
    rw [cost_weightedPiece]
    have : p l - p l * cost p p / cost p p = 0 := by
      field_simp [(cost_self_pos (h.subset hp).1).ne']; ring
    rw [this, mul_zero]
  rw [stdUtility, neg_inj]
  refine le_antisymm (csInf_le (h.levels_bddBelow _) (reaches_self hp))
    (le_csInf (h.levels_nonempty _) fun θ hθ => ?_)
  by_contra hlt
  push Not at hlt
  exact h.not_reaches_below hp hc.le hlt hθ

/-- **The piece is the unique optimum.** -/
theorem stdUtility_lt {p : ι → ℝ} (hp : p ∈ K) {x : ι → ℝ} (hx : cost p x ≤ 0)
    (hne : x ≠ weightedPiece a l p) :
    stdUtility K a l ε x < stdUtility K a l ε (weightedPiece a l p) := by
  have := h.nonemptyι
  rw [h.stdUtility_self hp, stdUtility, neg_lt_neg_iff]
  obtain ⟨δ, hδ, hgap⟩ := h.exists_gap hp hx hne
  have hle : dirCos l p + δ ≤ sInf {θ | ReachesLevel K a l ε x θ} := by
    refine le_csInf (h.levels_nonempty x) fun θ hθ => ?_
    by_contra hlt
    push Not at hlt
    exact hgap θ hlt hθ
  linarith

end PieceData

omit [DecidableEq ι] in
/-- A compact set of prices in the open simplex is bounded away from the
boundary. -/
theorem exists_eps_of_compact {K : Set (ι → ℝ)} (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι)
    (hne : K.Nonempty) : ∃ ε > 0, ∀ p ∈ K, ∀ i, 2 * ε ≤ p i := by
  have hb : ∀ i, ∃ b > 0, ∀ p ∈ K, b ≤ p i := by
    intro i
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne (continuous_apply i).continuousOn
    exact ⟨p i, (hKS hp).1 i, fun q hq => hmin hq⟩
  choose b hb0 hb using hb
  have : Nonempty ι := by
    obtain ⟨p, hp⟩ := hne
    by_contra hι; rw [not_nonempty_iff] at hι; simpa using (hKS hp).2
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ b Finset.univ_nonempty
  refine ⟨b i₀ / 2, by linarith [hb0 i₀], fun p hp i => ?_⟩
  have := hi₀ i (Finset.mem_univ i)
  have := hb i p hp
  linarith

/-- **A standard consumer for each piece (Debreu's step 2 at full strength,
except strict convexity).** Let `K` be a compact set of prices in the open
simplex and `a` a continuous positive weight on `K`. There is a continuous,
strongly monotone, quasiconcave utility `U` and a strictly positive endowment
`ω` such that at every `p ∈ K` the consumer's Walrasian demand is exactly
`{ω + a(p)(e_l − (p_l/‖p‖²) p)}`. -/
theorem exists_standard_consumer_weightedPiece {K : Set (ι → ℝ)} {a : (ι → ℝ) → ℝ}
    (l : ι) (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι) (ha : ContinuousOn a K)
    (hapos : ∀ q ∈ K, 0 < a q) :
    ∃ (U : (ι → ℝ) → ℝ) (ω : ι → ℝ), Continuous U ∧ StronglyMonotone (prefOf U) ∧
      QuasiconcaveOn ℝ univ U ∧ (∀ i, 0 < ω i) ∧
      ∀ p ∈ K, demand (prefOf U) p (cost p ω) = {ω + weightedPiece a l p} := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · -- No prices to rationalize: any standard utility works.
    refine ⟨fun x => ∑ i, x i, fun _ => 1, by fun_prop, ?_, ?_, fun _ => one_pos,
      fun p hp => by simp [hE] at hp⟩
    · intro x y _ hle hne'
      obtain ⟨i, hi⟩ : ∃ i, x i < y i := by
        by_contra hc; push Not at hc
        exact hne' (funext fun j => le_antisymm (hle j) (hc j))
      have hlt : ∑ j, x j < ∑ j, y j :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
      exact ⟨hlt.le, not_le.2 hlt⟩
    · intro r x₁ hx₁ x₂ hx₂ s t hs ht hst
      refine ⟨mem_univ _, ?_⟩
      simp only [mem_ofPred_eq] at hx₁ hx₂ ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      have e : r = s * r + t * r := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_nonneg hs (sub_nonneg.2 hx₁.2), mul_nonneg ht (sub_nonneg.2 hx₂.2)]
  obtain ⟨ε, hε, hKε⟩ := exists_eps_of_compact hK hKS hne
  have h : PieceData K a ε := ⟨hK, hne, hKS, hε, hKε, ha, hapos⟩
  have := h.nonemptyι
  set y := weightedPiece a l
  set u := stdUtility K a l ε
  obtain ⟨b, hb⟩ : ∃ b, ∀ q ∈ K, ‖y q‖ ≤ b := by
    obtain ⟨b, hb⟩ := (hK.image_of_continuousOn
      (continuousOn_weightedPiece l hKS ha).norm).isBounded.bddAbove
    exact ⟨b, fun q hq => hb ⟨q, hq, rfl⟩⟩
  set ω : ι → ℝ := fun _ => max b 1
  refine ⟨fun x => u (x - ω), ω, h.continuous_stdUtility.comp (by fun_prop), ?_, ?_,
    fun i => lt_of_lt_of_le one_pos (le_max_right b 1), ?_⟩
  · intro x x' _ hle hne'
    have hlt : u (x - ω) < u (x' - ω) :=
      h.stdUtility_strictMono (fun i => by simp only [Pi.sub_apply]; linarith [hle i])
        (fun he => hne' (by simpa using he))
    exact ⟨hlt.le, not_le.2 hlt⟩
  · intro r
    have hc := h.quasiconcaveOn_stdUtility (l := l) r
    have : {x | x ∈ (univ : Set (ι → ℝ)) ∧ r ≤ u (x - ω)}
        = (fun x => -ω + x) ⁻¹' {x | x ∈ Set.univ ∧ r ≤ u x} := by
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
      intro x hx hne'
      refine h.stdUtility_lt hp ?_ ?_
      · rw [cost_sub_right]; linarith [hx.2]
      · intro he; exact hne' (sub_eq_iff_eq_add'.1 he)
    ext x
    simp only [demand, mem_ofPred_eq, mem_singleton_iff, prefOf]
    constructor
    · rintro ⟨hx, hmax⟩
      by_contra hne'
      have h1 := hmax _ hbud
      have h2 := key x hx hne'
      simp only [add_sub_cancel_left] at h1
      linarith
    · rintro rfl
      refine ⟨hbud, fun x hx => ?_⟩
      simp only [add_sub_cancel_left]
      by_cases hxe : x = ω + y p
      · rw [hxe, add_sub_cancel_left]
      · exact (key x hx hxe).le

/-! ### Sonnenschein–Mantel–Debreu with standard consumers -/

/-- **Sonnenschein–Mantel–Debreu** (Debreu 1974; MWG 17.E.3), with consumers
whose utilities are continuous, strongly monotone and quasiconcave. Let `z` be
continuous and satisfy Walras' law on a compact set `K` of prices in the open
simplex (for example Debreu's `S_ε`). Then `z` is the aggregate excess demand
of an exchange economy with `L` such consumers, each with a strictly positive
endowment and single-valued Walrasian demand at every `p ∈ K`.

Caveat: Debreu's consumers also have *strictly* convex preferences; these are
only convex. Consequently individual demand is guaranteed single-valued only on
`K`, not at every positive price. -/
theorem sonnenschein_mantel_debreu_monotone [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    {K : Set (ι → ℝ)} (hK : IsCompact K) (hKS : K ⊆ openPriceSimplex ι)
    (hz : ContinuousOn z K) (hW : WalrasLaw z K) :
    ∃ (U : ι → (ι → ℝ) → ℝ) (ω : ι → ι → ℝ),
      (∀ l, Continuous (U l) ∧ StronglyMonotone (prefOf (U l)) ∧
        QuasiconcaveOn ℝ univ (U l) ∧ ∀ i, 0 < ω l i) ∧
      ∀ p ∈ K, ∃ x : ι → ι → ℝ,
        (∀ l, demand (prefOf (U l)) p (cost p (ω l)) = {x l}) ∧ ∑ l, (x l - ω l) = z p := by
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
  have hcons : ∀ l, ∃ (U : (ι → ℝ) → ℝ) (ω : ι → ℝ), Continuous U ∧
      StronglyMonotone (prefOf U) ∧ QuasiconcaveOn ℝ univ U ∧ (∀ i, 0 < ω i) ∧
      ∀ p ∈ K, demand (prefOf U) p (cost p ω) = {ω + debreuPiece z c l p} := fun l =>
    exists_standard_consumer_weightedPiece l hK hKS
      (((continuous_apply l).comp_continuousOn hz).add
        (continuousOn_const.mul (continuous_apply l).continuousOn)) (hα l)
  choose U ω hUc hUm hUq hω hdem using hcons
  refine ⟨U, ω, fun l => ⟨hUc l, hUm l, hUq l, hω l⟩, fun p hp =>
    ⟨fun l => ω l + debreuPiece z c l p, fun l => hdem l p hp, ?_⟩⟩
  simp only [add_sub_cancel_left]
  exact sum_debreuPiece c (hKS hp).1 (hW p hp)

namespace SMDExamples

/-- **SMD in action, with standard consumers.** `zBad` violates the weak axiom
in the aggregate, yet it is exactly the aggregate excess demand of two
consumers with continuous, strongly monotone, quasiconcave utilities and
strictly positive endowments, each with single-valued demand on `DBad`. -/
theorem zBad_standard_consumers : ¬ ExcessWARP zBad DBad ∧
    ∃ (U : Fin 2 → (Fin 2 → ℝ) → ℝ) (ω : Fin 2 → Fin 2 → ℝ),
      (∀ l, Continuous (U l) ∧ StronglyMonotone (prefOf (U l)) ∧
        QuasiconcaveOn ℝ univ (U l) ∧ ∀ i, 0 < ω l i) ∧
      ∀ p ∈ DBad, ∃ x : Fin 2 → Fin 2 → ℝ,
        (∀ l, demand (prefOf (U l)) p (cost p (ω l)) = {x l}) ∧ ∑ l, (x l - ω l) = zBad p :=
  ⟨not_excessWARP_zBad,
    sonnenschein_mantel_debreu_monotone isCompact_DBad DBad_subset continuousOn_zBad
      walrasLaw_zBad⟩

end SMDExamples

end Econ
