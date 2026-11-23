/-
# Network games: Bonacich centrality and the key player

Reference: C. Ballester, A. Calvó-Armengol and Y. Zenou (2006), "Who's who in
networks. Wanted: the key player", *Econometrica* 74(5): 1403–1417 (BCZ).

**Game.** Players `n` on a network with weighted adjacency matrix `G`
(`G i j ≥ 0`, no self-loops `G i i = 0`). Player `i` chooses effort
`x i ∈ ℝ` with payoff

    u i x = α x_i - x_i² / 2 + φ Σ_j G i j x_i x_j

(BCZ's local-complementarity game with the global-substitutability term set to
zero, i.e. `γ = 0` in their notation, `σ = 1`). The best response is
`x_i = α + φ Σ_j G i j x_j` (`isNash_iff`).

**Bonacich centrality.** `M = (I - φ G)⁻¹` and `b = M 1`. Under the
sufficient condition `φ · (max row sum of G) < 1` (`Dominant`; it implies
BCZ's `φ ρ(G) < 1`), `I - φ G` is invertible, `M ≥ 0`, `M i i ≥ 1`, and
`b ≥ 1` (`Dominant.isUnit`, `Dominant.inv_nonneg`, `Dominant.one_le_inv_diag`,
`Dominant.one_le_bonacich`). **BCZ Theorem 1** (`isNash_iff_eq_bonacich`):
the unique Nash equilibrium is `x = α b`, and it is positive when `α > 0`, so
it is also an equilibrium when efforts must be nonnegative.

**Key player (BCZ Theorem 3).** Removing player `i` changes the inverse by a
rank-one update (`inv_remove`): for `j, k ≠ i`,
`M₋ᵢ j k = M j k - M j i M i k / M i i`. Hence the aggregate centrality
`B = Σ_j b_j` falls by the *intercentrality*
`c_i = b_i · (Σ_j M j i) / M i i` (`aggregate_remove`), which is `b_i² / M i i`
for an undirected network (`intercentrality_symm`). Equilibrium aggregate
effort is `α B`, so the key player, whose removal minimizes aggregate effort,
is the one with the highest intercentrality (`keyPlayer`).
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace Econ

namespace Networks

open Finset Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The game -/

/-- BCZ payoff with `γ = 0`: own benefit `α xᵢ - xᵢ²/2` plus local
complementarities `φ Σⱼ gᵢⱼ xᵢ xⱼ`. -/
noncomputable def payoff (α φ : ℝ) (G : Matrix n n ℝ) (i : n) (x : n → ℝ) : ℝ :=
  α * x i - x i ^ 2 / 2 + φ * ∑ j, G i j * x i * x j

/-- Nash equilibrium in efforts `x ∈ ℝⁿ`. -/
def IsNash (α φ : ℝ) (G : Matrix n n ℝ) (x : n → ℝ) : Prop :=
  ∀ i y, payoff α φ G i (Function.update x i y) ≤ payoff α φ G i x

theorem payoff_update {G : Matrix n n ℝ} (hG0 : ∀ i, G i i = 0) (α φ : ℝ) (i : n) (x : n → ℝ)
    (y : ℝ) : payoff α φ G i (Function.update x i y) =
      -(y - (α + φ * ∑ j, G i j * x j)) ^ 2 / 2 + (α + φ * ∑ j, G i j * x j) ^ 2 / 2 := by
  have hs : ∑ j, G i j * Function.update x i y i * Function.update x i y j =
      y * ∑ j, G i j * x j := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [hG0]
    · simp [Function.update_of_ne hj]; ring
  rw [payoff, hs, Function.update_self]
  ring

/-- **Best responses.** With no self-loops, `x` is a Nash equilibrium iff every
player plays `α + φ Σⱼ gᵢⱼ xⱼ`. -/
theorem isNash_iff {G : Matrix n n ℝ} (hG0 : ∀ i, G i i = 0) (α φ : ℝ) (x : n → ℝ) :
    IsNash α φ G x ↔ ∀ i, x i = α + φ * ∑ j, G i j * x j := by
  constructor
  · intro h i
    have h1 := h i (α + φ * ∑ j, G i j * x j)
    have h2 := payoff_update hG0 α φ i x (x i)
    rw [Function.update_eq_self] at h2
    rw [payoff_update hG0, h2] at h1
    nlinarith [sq_nonneg (x i - (α + φ * ∑ j, G i j * x j))]
  · intro h i y
    have h2 := payoff_update hG0 α φ i x (x i)
    rw [Function.update_eq_self] at h2
    rw [payoff_update hG0, h2, ← h i]
    nlinarith [sq_nonneg (y - x i)]

/-! ### Bonacich centrality -/

/-- `M = (I - φ G)⁻¹`. -/
noncomputable def leontief (G : Matrix n n ℝ) (φ : ℝ) : Matrix n n ℝ := (1 - φ • G)⁻¹

/-- Bonacich centrality `b = (I - φ G)⁻¹ 1`. -/
noncomputable def bonacich (G : Matrix n n ℝ) (φ : ℝ) : n → ℝ := leontief G φ *ᵥ fun _ => 1

/-- Sufficient condition for a well-behaved equilibrium: nonnegative links,
`φ ≥ 0`, and `φ` times every row sum below `1`. -/
structure Dominant (G : Matrix n n ℝ) (φ : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ G i j
  phi_nonneg : 0 ≤ φ
  row : ∀ i, φ * ∑ j, G i j < 1

theorem mulVec_one_sub_apply (G : Matrix n n ℝ) (φ : ℝ) (x : n → ℝ) (i : n) :
    ((1 - φ • G) *ᵥ x) i = x i - φ * ∑ j, G i j * x j := by
  simp [mulVec, dotProduct, sub_mul, sum_sub_distrib, Matrix.one_apply, mul_sum, mul_assoc]

namespace Dominant

variable {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ)
include hD

omit [DecidableEq n] in
/-- Solutions of `x = c + φ G x` with `c ≥ 0` satisfy `x ≥ c`. -/
theorem le_of_fixed {x c : n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i, x i = c i + φ * ∑ j, G i j * x j) : ∀ i, c i ≤ x i := by
  have hpos : ∀ i, 0 ≤ x i := by
    by_contra h
    push Not at h
    have hne : (univ : Finset n).Nonempty := by obtain ⟨i, -⟩ := h; exact ⟨i, mem_univ i⟩
    obtain ⟨i₀, -, hmin⟩ := univ.exists_min_image x hne
    obtain ⟨k, hk⟩ := h
    have hneg : x i₀ < 0 := lt_of_le_of_lt (hmin k (mem_univ k)) hk
    have hsum : (∑ j, G i₀ j) * x i₀ ≤ ∑ j, G i₀ j * x j := by
      rw [sum_mul]
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmin j (mem_univ j)) (hD.nonneg i₀ j)
    have h1 := hx i₀
    have h2 := mul_le_mul_of_nonneg_left hsum hD.phi_nonneg
    have h3 := hD.row i₀
    have h4 := hc i₀
    nlinarith
  intro i
  have := hx i
  have : 0 ≤ φ * ∑ j, G i j * x j :=
    mul_nonneg hD.phi_nonneg (sum_nonneg fun j _ => mul_nonneg (hD.nonneg i j) (hpos j))
  linarith

/-- `I - φ G` is invertible. -/
theorem isUnit : IsUnit (1 - φ • G) := by
  rw [← mulVec_injective_iff_isUnit]
  have key : ∀ v : n → ℝ, (1 - φ • G) *ᵥ v = 0 → ∀ i, 0 ≤ v i := by
    intro v hv
    have := hD.le_of_fixed (c := 0) (fun _ => le_rfl) (x := v) fun i => by
      have := congrFun hv i
      rw [mulVec_one_sub_apply] at this
      simp only [Pi.zero_apply, zero_add] at this ⊢
      linarith
    simpa using this
  intro u v huv
  have hw : (1 - φ • G) *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
  have hw' : (1 - φ • G) *ᵥ (v - u) = 0 := by rw [mulVec_sub, huv, sub_self]
  funext i
  have a := key _ hw i
  have b := key _ hw' i
  simp only [Pi.sub_apply] at a b
  linarith

theorem mul_leontief : (1 - φ • G) * leontief G φ = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hD.isUnit)

/-- Column `k` of `M` solves `x = e_k + φ G x`. -/
theorem leontief_col (k i : n) :
    leontief G φ i k = (if i = k then 1 else 0) + φ * ∑ j, G i j * leontief G φ j k := by
  have := congrFun (congrFun hD.mul_leontief i) k
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.one_apply, smul_eq_mul] at this
  linarith

theorem inv_nonneg (i k : n) : 0 ≤ leontief G φ i k := by
  have := hD.le_of_fixed (c := fun i => if i = k then 1 else 0) (x := fun i => leontief G φ i k)
    (fun i => by split_ifs <;> norm_num) (fun i => hD.leontief_col k i) i
  refine le_trans ?_ this
  split_ifs <;> norm_num

theorem one_le_inv_diag (k : n) : 1 ≤ leontief G φ k k := by
  have := hD.le_of_fixed (c := fun i => if i = k then 1 else 0) (x := fun i => leontief G φ i k)
    (fun i => by split_ifs <;> norm_num) (fun i => hD.leontief_col k i) k
  simpa using this

theorem one_le_bonacich (i : n) : 1 ≤ bonacich G φ i := by
  have h : 1 ≤ ∑ k, leontief G φ i k := by
    rw [← add_sum_erase _ _ (mem_univ i)]
    have := hD.one_le_inv_diag i
    have : 0 ≤ ∑ k ∈ univ.erase i, leontief G φ i k := sum_nonneg fun k _ => hD.inv_nonneg i k
    linarith
  simpa [bonacich, mulVec, dotProduct] using h

end Dominant

/-- **BCZ Theorem 1.** Under `Dominant`, the unique Nash equilibrium is
`α` times Bonacich centrality. -/
theorem isNash_iff_eq_bonacich {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ)
    (hG0 : ∀ i, G i i = 0) (α : ℝ) (x : n → ℝ) :
    IsNash α φ G x ↔ x = α • bonacich G φ := by
  rw [isNash_iff hG0]
  have hdet := (isUnit_iff_isUnit_det _).1 hD.isUnit
  have hfoc : (∀ i, x i = α + φ * ∑ j, G i j * x j) ↔ (1 - φ • G) *ᵥ x = fun _ => α := by
    constructor
    · intro h; funext i; rw [mulVec_one_sub_apply]; linarith [h i]
    · intro h i; have := congrFun h i; rw [mulVec_one_sub_apply] at this; linarith
  rw [hfoc, bonacich, leontief, ← mulVec_smul]
  have e : (α • fun _ : n => (1 : ℝ)) = fun _ => α := by funext; simp
  rw [e]
  constructor
  · intro h
    rw [← h, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  · intro h
    rw [h, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

/-- The equilibrium is positive when `α > 0`. -/
theorem nash_pos {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) {α : ℝ} (hα : 0 < α) (i : n) :
    0 < (α • bonacich G φ) i := by
  simpa using mul_pos hα (lt_of_lt_of_le one_pos (hD.one_le_bonacich i))

/-! ### The key player -/

/-- The network without player `i`. -/
def remove (G : Matrix n n ℝ) (i : n) : Matrix {j // j ≠ i} {j // j ≠ i} ℝ :=
  G.submatrix Subtype.val Subtype.val

theorem sum_ne (i : n) (f : n → ℝ) : ∑ l : {l // l ≠ i}, f l = ∑ l, f l - f i := by
  rw [← Finset.sum_subtype (univ.erase i) (fun x => by simp) f, sum_erase_eq_sub (mem_univ i)]

/-- **Removing a player is a rank-one update of `M`.** -/
theorem inv_remove {G : Matrix n n ℝ} {φ : ℝ} (hU : IsUnit (1 - φ • G)) (i : n)
    (hii : leontief G φ i i ≠ 0) :
    leontief (remove G i) φ = Matrix.of fun j k : {j // j ≠ i} =>
      leontief G φ j k - leontief G φ j i * leontief G φ i k / leontief G φ i i := by
  set M := leontief G φ
  set A : Matrix n n ℝ := 1 - φ • G
  have hAM : ∀ j k, ∑ l, A j l * M l k = if j = k then 1 else 0 := by
    intro j k
    have := congrFun (congrFun (mul_nonsing_inv A ((isUnit_iff_isUnit_det _).1 hU)) j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  unfold leontief
  apply inv_eq_right_inv
  ext j k
  have hA' : ∀ l : {j // j ≠ i}, (1 - φ • remove G i) j l = A j l := by
    intro l
    simp only [A, remove, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply,
      Matrix.one_apply, Subtype.ext_iff]
  simp only [Matrix.mul_apply, hA', Matrix.of_apply]
  rw [sum_ne i (fun l => A j l * (M l k - M l i * M i k / M i i))]
  have e1 : ∑ l, A j l * (M l k - M l i * M i k / M i i) =
      ∑ l, A j l * M l k - (∑ l, A j l * M l i) * M i k / M i i := by
    rw [sum_mul, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [e1, hAM, hAM, ite_eq_right j.2]
  have : A j i * (M i k - M i i * M i k / M i i) = 0 := by field_simp; ring
  rw [this]
  simp [Matrix.one_apply, Subtype.ext_iff]

/-- Aggregate centrality `Σⱼ bⱼ`. -/
noncomputable def aggregate {m : Type*} [Fintype m] [DecidableEq m] (G : Matrix m m ℝ) (φ : ℝ) :
    ℝ := ∑ j, bonacich G φ j

/-- Intercentrality of player `i`. -/
noncomputable def intercentrality (G : Matrix n n ℝ) (φ : ℝ) (i : n) : ℝ :=
  bonacich G φ i * (∑ j, leontief G φ j i) / leontief G φ i i

/-- **Removing player `i` lowers aggregate centrality by its
intercentrality.** -/
theorem aggregate_remove {G : Matrix n n ℝ} {φ : ℝ} (hU : IsUnit (1 - φ • G)) (i : n)
    (hii : leontief G φ i i ≠ 0) :
    aggregate (remove G i) φ = aggregate G φ - intercentrality G φ i := by
  set M := leontief G φ
  have hb : ∀ j, bonacich G φ j = ∑ k, M j k := fun j => by
    simp [bonacich, mulVec, dotProduct, M]
  simp only [aggregate, intercentrality, bonacich, inv_remove hU i hii, mulVec, dotProduct,
    Matrix.of_apply, mul_one]
  rw [sum_ne i (fun j => ∑ k : {k // k ≠ i}, (M j k - M j i * M i k / M i i))]
  have inner : ∀ j : n, ∑ k : {k // k ≠ i}, (M j k - M j i * M i k / M i i) =
      ∑ k, M j k - M j i * (∑ k, M i k) / M i i := by
    intro j
    rw [sum_ne i (fun k => M j k - M j i * M i k / M i i), sum_sub_distrib, ← sum_div, ← mul_sum]
    field_simp
    ring
  simp only [inner]
  rw [sum_sub_distrib, ← sum_div, ← sum_mul]
  simp only [M] at hii ⊢
  field_simp
  ring

/-- For an undirected network (`G` symmetric) intercentrality is
`bᵢ² / M i i` (BCZ). -/
theorem intercentrality_symm {G : Matrix n n ℝ} {φ : ℝ} (hsymm : Gᵀ = G) (i : n) :
    intercentrality G φ i = bonacich G φ i ^ 2 / leontief G φ i i := by
  have hMt : (leontief G φ)ᵀ = leontief G φ := by
    rw [leontief, transpose_nonsing_inv, transpose_sub, transpose_one, transpose_smul, hsymm]
  have : ∑ j, leontief G φ j i = bonacich G φ i := by
    simp only [bonacich, mulVec, dotProduct, mul_one]
    exact sum_congr rfl fun j _ => by
      rw [← transpose_apply (leontief G φ) i j, hMt]
  rw [intercentrality, this, sq]

/-- **BCZ Theorem 3 (key player).** Under `Dominant`, with `α > 0`, the player
whose removal minimizes equilibrium aggregate effort `α · B` is a player with
maximal intercentrality. -/
theorem keyPlayer {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) {α : ℝ} (hα : 0 < α)
    (i j : n) :
    α * aggregate (remove G i) φ ≤ α * aggregate (remove G j) φ ↔
      intercentrality G φ j ≤ intercentrality G φ i := by
  have hi := (lt_of_lt_of_le one_pos (hD.one_le_inv_diag i)).ne'
  have hj := (lt_of_lt_of_le one_pos (hD.one_le_inv_diag j)).ne'
  rw [aggregate_remove hD.isUnit i hi, aggregate_remove hD.isUnit j hj,
    mul_le_mul_iff_of_pos_left hα]
  constructor <;> intro h <;> linarith

/-- The removed network inherits `Dominant` (row sums only fall). -/
theorem Dominant.remove {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) (i : n) :
    Dominant (Networks.remove G i) φ := by
  refine ⟨fun j k => hD.nonneg j k, hD.phi_nonneg, fun j => ?_⟩
  have hsum : ∑ k : {k // k ≠ i}, Networks.remove G i j k ≤ ∑ k, G j k := by
    rw [show (∑ k : {k // k ≠ i}, Networks.remove G i j k) = ∑ k : {k // k ≠ i}, G j k from rfl,
      sum_ne i (fun k => G j k)]
    linarith [hD.nonneg j i]
  calc φ * ∑ k, Networks.remove G i j k ≤ φ * ∑ k, G j k := mul_le_mul_of_nonneg_left hsum hD.phi_nonneg
    _ < 1 := hD.row j

/-- **Equilibrium aggregate effort after removing `i`** is `α` times the
aggregate centrality of the removed network: with `Dominant` and no
self-loops, the reduced game's unique equilibrium is `α b(G₋ᵢ)`. -/
theorem isNash_remove {G : Matrix n n ℝ} {φ : ℝ} (hD : Dominant G φ) (hG0 : ∀ i, G i i = 0)
    (α : ℝ) (i : n) (x : {j // j ≠ i} → ℝ) :
    IsNash α φ (remove G i) x ↔ x = α • bonacich (remove G i) φ :=
  isNash_iff_eq_bonacich (hD.remove i) (fun j => hG0 j) α x

/-- Non-vacuity: a two-player link with `φ = 1/2` satisfies `Dominant`. -/
theorem dominant_pair : Dominant (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by norm_num,
    fun i => by fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num⟩

/-- The two-player example: `M = [[4/3, 2/3], [2/3, 4/3]]`. -/
theorem leontief_pair : leontief (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) =
    !![4 / 3, 2 / 3; 2 / 3, 4 / 3] := by
  unfold leontief
  apply inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

/-- In the two-player example `b = (2, 2)`, aggregate centrality is `4`, each
player's intercentrality is `3`, and removing either leaves aggregate `1`. -/
theorem pair_numbers :
    bonacich (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) = ![2, 2] ∧
      aggregate (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) = 4 ∧
      intercentrality (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) 0 = 3 ∧
      aggregate (remove (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0) (1 / 2) = 1 := by
  have hb : bonacich (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) = ![2, 2] := by
    rw [bonacich, leontief_pair]
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hagg : aggregate (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) = 4 := by
    rw [aggregate, hb]; simp [Fin.sum_univ_two]; norm_num
  have hc : intercentrality (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) 0 = 3 := by
    rw [intercentrality, hb, leontief_pair]; simp [Fin.sum_univ_two]; norm_num
  refine ⟨hb, hagg, hc, ?_⟩
  rw [aggregate_remove dominant_pair.isUnit 0 (by rw [leontief_pair]; simp), hagg, hc]
  norm_num

end Networks

end Econ
