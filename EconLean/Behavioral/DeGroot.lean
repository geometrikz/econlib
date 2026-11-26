/-
# DeGroot learning: consensus and the influence vector

References. M. H. DeGroot (1974), "Reaching a Consensus", *JASA* 69;
B. Golub and M. O. Jackson (2010), "Naïve Learning in Social Networks and the
Wisdom of Crowds", *AEJ: Micro* 2(1), §II (convergence of strongly connected,
aperiodic listening matrices, influence weights, and the degree formula for
undirected networks); only the sufficiency direction is formalized.

**Model.** Finitely many agents `ι` hold beliefs `p : ι → ℝ`. A row-stochastic
listening matrix `T` (`IsStochastic`: nonnegative, rows sum to one) updates
beliefs by `p ↦ T p`, so after `t` rounds beliefs are `T^t p`.

**Results.**
* `consensus` (DeGroot 1974): if `T` is stochastic and *primitive*
  (`IsPrimitive`: some power `T^k` has all entries positive; for nonnegative
  matrices this is equivalent to strong connectivity plus aperiodicity, an
  equivalence not formalized here), every agent's belief converges to one
  common limit. The proof is a Dobrushin contraction: the spread
  `max − min` of beliefs never increases and shrinks by the factor
  `1 − |ι| δ < 1` every `k` rounds, where `δ > 0` is the smallest entry of `T^k`
  (`spread_mul_le`).
* `influence` (Golub–Jackson): the limit is `π · p` for an *influence
  vector* `π` (`IsInfluence`: a probability vector with `π T = π`, i.e. a
  left unit eigenvector) that has all entries positive; `T^t` converges
  entrywise to the matrix with every row `π`. The influence vector is unique
  among probability vectors (`influence_unique`), so it is *the* stationary
  distribution of `T`.
* `influence_degree`, `consensus_degree` (Golub–Jackson, undirected case):
  if listening weights come from a symmetric nonnegative weight matrix `g`
  with positive weighted degrees by normalizing rows (`normalize`;
  `influence_degree` itself needs only symmetry and positive degrees), the influence vector is
  `π i = d_i / ∑ d` with `d_i = ∑_j g i j` the weighted degree: in a
  primitive undirected network the consensus is the degree-weighted average
  of initial beliefs.
* Aperiodicity cannot be dropped (`swap_not_converge`): two agents who only
  listen to each other (`swap`, strongly connected with period 2) are
  stochastic and have an influence vector (`swap_influence`) but are not
  primitive (`swap_not_primitive`), and agent 0's belief from `p = (1, 0)`
  alternates `1, 0, 1, …` and does not converge. Non-vacuity of the
  hypotheses: `primitive_of_pos`, `half_stochastic`, `half_primitive`, and
  `normalize_ones` (`half` is the normalized complete graph with self-loops,
  so all hypotheses of `consensus_degree` hold for `g = 1`).

Not covered: the converse (a strongly connected periodic matrix fails to
converge for some initial beliefs) beyond the `swap` example, the equivalence of primitivity with strong connectivity and
aperiodicity, the non-primitive (multiple closed classes) case, and
Golub–Jackson's wisdom-of-crowds results for growing networks.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

namespace Econ

namespace DeGroot

open Matrix Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A (row-)stochastic listening matrix: nonnegative weights, each row sums to one. -/
def IsStochastic (T : Matrix ι ι ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧ ∀ i, ∑ j, T i j = 1

/-- Primitivity: some power of `T` has all entries strictly positive. -/
def IsPrimitive (T : Matrix ι ι ℝ) : Prop :=
  ∃ k : ℕ, ∀ i j, 0 < (T ^ k) i j

/-- An influence vector: a probability vector that is a left fixed point of `T`. -/
def IsInfluence (T : Matrix ι ι ℝ) (π : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ π ᵥ* T = π

theorem isStochastic_one : IsStochastic (1 : Matrix ι ι ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply]

omit [DecidableEq ι] in
theorem IsStochastic.mul {A B : Matrix ι ι ℝ} (hA : IsStochastic A) (hB : IsStochastic B) :
    IsStochastic (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hA.1 i l) (hB.1 l j)
  · simp_rw [Matrix.mul_apply]
    rw [sum_comm]
    simp_rw [← mul_sum, hB.2, mul_one]
    exact hA.2 i

theorem IsStochastic.pow {T : Matrix ι ι ℝ} (hT : IsStochastic T) (t : ℕ) :
    IsStochastic (T ^ t) := by
  induction t with
  | zero => simpa using (isStochastic_one : IsStochastic (1 : Matrix ι ι ℝ))
  | succ t ih => rw [pow_succ]; exact ih.mul hT

omit [DecidableEq ι] in
/-- Updated beliefs are bounded above by any upper bound of the old beliefs. -/
theorem IsStochastic.mulVec_le {A : Matrix ι ι ℝ} (hA : IsStochastic A) {p : ι → ℝ} {c : ℝ}
    (hp : ∀ j, p j ≤ c) (i : ι) : (A *ᵥ p) i ≤ c := by
  simp only [mulVec, dotProduct]
  calc ∑ j, A i j * p j ≤ ∑ j, A i j * c :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) (hA.1 i j)
    _ = c := by rw [← sum_mul, hA.2 i, one_mul]

omit [DecidableEq ι] in
/-- Updated beliefs are bounded below by any lower bound of the old beliefs. -/
theorem IsStochastic.le_mulVec {A : Matrix ι ι ℝ} (hA : IsStochastic A) {p : ι → ℝ} {c : ℝ}
    (hp : ∀ j, c ≤ p j) (i : ι) : c ≤ (A *ᵥ p) i := by
  simp only [mulVec, dotProduct]
  calc c = ∑ j, A i j * c := by rw [← sum_mul, hA.2 i, one_mul]
    _ ≤ ∑ j, A i j * p j :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) (hA.1 i j)

omit [DecidableEq ι] in
/-- **Dobrushin contraction**: if every entry of the stochastic matrix `A` is at
least `δ`, one update shrinks the spread of beliefs by the factor `1 − |ι| δ`. -/
theorem spread_mul_le {A : Matrix ι ι ℝ} (hA : IsStochastic A) {δ : ℝ}
    (hδ : ∀ i j, δ ≤ A i j) {p : ι → ℝ} {lo hi : ℝ} (hlo : ∀ j, lo ≤ p j)
    (hhi : ∀ j, p j ≤ hi) (i i' : ι) :
    (A *ᵥ p) i - (A *ᵥ p) i' ≤ (1 - Fintype.card ι * δ) * (hi - lo) := by
  have key : ∀ i, (A *ᵥ p) i = ∑ j, (A i j - δ) * p j + δ * ∑ j, p j := by
    intro i
    simp only [mulVec, dotProduct, sub_mul, sum_sub_distrib, mul_sum]
    ring
  have hrow : ∀ i, ∑ j, (A i j - δ) = 1 - Fintype.card ι * δ := by
    intro i
    rw [sum_sub_distrib, hA.2 i, sum_const, card_univ, nsmul_eq_mul]
  have h1 : ∑ j, (A i j - δ) * p j ≤ ∑ j, (A i j - δ) * hi :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hhi j) (sub_nonneg.2 (hδ i j))
  have h2 : ∑ j, (A i' j - δ) * lo ≤ ∑ j, (A i' j - δ) * p j :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlo j) (sub_nonneg.2 (hδ i' j))
  rw [← sum_mul, hrow] at h1 h2
  rw [key i, key i']
  nlinarith

/-- Positivity of a power propagates to the next power. -/
theorem pos_pow_succ {T : Matrix ι ι ℝ} (hT : IsStochastic T) {k : ℕ}
    (hk : ∀ i j, 0 < (T ^ k) i j) (i j : ι) : 0 < (T ^ (k + 1)) i j := by
  rw [pow_succ', Matrix.mul_apply]
  refine sum_pos' (fun l _ => mul_nonneg (hT.1 i l) (hk l j).le) ?_
  by_contra h
  push Not at h
  have hz : ∀ l, T i l = 0 := fun l =>
    le_antisymm (by
      have := h l (mem_univ _)
      by_contra hne
      push Not at hne
      exact absurd this (not_le.2 (mul_pos hne (hk l j))))
      (hT.1 i l)
  have := hT.2 i
  simp [hz] at this

/-- **DeGroot consensus**: under a stochastic primitive listening matrix, all
agents' beliefs converge to a common limit. -/
theorem consensus {T : Matrix ι ι ℝ} (hT : IsStochastic T) (hP : IsPrimitive T) (p : ι → ℝ) :
    ∃ L : ℝ, ∀ i, Tendsto (fun t => (T ^ t *ᵥ p) i) atTop (𝓝 L) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨k, hk⟩ := hP
  set K := k + 1 with hK
  have hKpos : ∀ i j, 0 < (T ^ K) i j := pos_pow_succ hT hk
  have hne : (univ : Finset (ι × ι)).Nonempty := univ_nonempty
  set δ := univ.inf' hne (fun ij : ι × ι => (T ^ K) ij.1 ij.2) with hδdef
  have hδpos : 0 < δ := (lt_inf'_iff hne).2 fun ij _ => hKpos ij.1 ij.2
  have hδle : ∀ i j, δ ≤ (T ^ K) i j := fun i j =>
    inf'_le (fun ij : ι × ι => (T ^ K) ij.1 ij.2) (mem_univ (i, j))
  set c := 1 - Fintype.card ι * δ with hc
  have hc0 : 0 ≤ c := by
    obtain ⟨i⟩ := hι
    have h1 := (hT.pow K).2 i
    have : ∑ j : ι, δ ≤ ∑ j, (T ^ K) i j := sum_le_sum fun j _ => hδle i j
    rw [sum_const, card_univ, nsmul_eq_mul, h1] at this
    linarith
  have hc1 : c < 1 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have := mul_pos this hδpos
    linarith
  set x : ℕ → ι → ℝ := fun t => T ^ t *ᵥ p with hx
  have hstep : ∀ t, x (t + 1) = T *ᵥ x t := fun t => by
    simp only [hx, mulVec_mulVec, pow_succ']
  have hstepK : ∀ t, x (t + K) = T ^ K *ᵥ x t := fun t => by
    simp only [hx, mulVec_mulVec, ← pow_add, add_comm]
  have hu : (univ : Finset ι).Nonempty := univ_nonempty
  set a : ℕ → ℝ := fun t => univ.sup' hu (x t) with ha
  set b : ℕ → ℝ := fun t => univ.inf' hu (x t) with hb
  have hxa : ∀ t i, x t i ≤ a t := fun t i => le_sup' (x t) (mem_univ i)
  have hxb : ∀ t i, b t ≤ x t i := fun t i => inf'_le (x t) (mem_univ i)
  have ha_anti : Antitone a := antitone_nat_of_succ_le fun t =>
    sup'_le _ _ fun i _ => by rw [hstep]; exact hT.mulVec_le (hxa t) i
  have hb_mono : Monotone b := monotone_nat_of_le_succ fun t =>
    le_inf' _ _ fun i _ => by rw [hstep]; exact hT.le_mulVec (hxb t) i
  have hspreadK : ∀ t, a (t + K) - b (t + K) ≤ c * (a t - b t) := fun t => by
    obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' hu (x (t + K))
    obtain ⟨i', -, hi'⟩ := exists_mem_eq_inf' hu (x (t + K))
    simp only [ha, hb] at hi hi' ⊢
    rw [hi, hi', hstepK]
    exact spread_mul_le (hT.pow K) hδle (hxb t) (hxa t) i i'
  have hspread_nonneg : ∀ t, 0 ≤ a t - b t := fun t => by
    obtain ⟨i⟩ := hι
    linarith [hxa t i, hxb t i]
  have hgeom : ∀ j, a (K * j) - b (K * j) ≤ c ^ j * (a 0 - b 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc a (K * (j + 1)) - b (K * (j + 1)) = a (K * j + K) - b (K * j + K) := by
            rw [mul_add, mul_one]
        _ ≤ c * (a (K * j) - b (K * j)) := hspreadK _
        _ ≤ c * (c ^ j * (a 0 - b 0)) := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (j + 1) * (a 0 - b 0) := by ring
  have hspread_to : Tendsto (fun t => a t - b t) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t => c ^ (t / K) * (a 0 - b 0)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp
        (Nat.tendsto_div_const_atTop (by omega : K ≠ 0))).mul_const (a 0 - b 0)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      hspread_nonneg fun t => ?_
    calc a t - b t ≤ a (K * (t / K)) - b (K * (t / K)) := by
          have h := Nat.mul_div_le t K
          linarith [ha_anti h, hb_mono h]
      _ ≤ c ^ (t / K) * (a 0 - b 0) := hgeom _
  have hbdd : BddBelow (Set.range a) := ⟨b 0, by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i⟩ := hι
    linarith [hxa t i, hxb t i, hb_mono (Nat.zero_le t)]⟩
  have ha_to := tendsto_atTop_ciInf ha_anti hbdd
  have hb_to : Tendsto b atTop (𝓝 (⨅ t, a t)) := by
    have := ha_to.sub hspread_to
    simpa using this
  exact ⟨⨅ t, a t, fun i =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le hb_to ha_to (fun t => hxb t i) fun t => hxa t i⟩

/-- **Influence vector** (DeGroot; Golub–Jackson): under a stochastic primitive
listening matrix there is a strictly positive influence vector `π` such that
`T^t` converges entrywise to the matrix with all rows `π`, and every agent's
belief converges to the `π`-weighted average `π · p` of initial beliefs. -/
theorem influence [Nonempty ι] {T : Matrix ι ι ℝ} (hT : IsStochastic T) (hP : IsPrimitive T) :
    ∃ π : ι → ℝ, IsInfluence T π ∧ (∀ j, 0 < π j) ∧
      (∀ i j, Tendsto (fun t => (T ^ t) i j) atTop (𝓝 (π j))) ∧
      ∀ p : ι → ℝ, ∀ i, Tendsto (fun t => (T ^ t *ᵥ p) i) atTop (𝓝 (π ⬝ᵥ p)) := by
  choose π hπ using fun j => consensus hT hP (Pi.single j 1)
  have hlim : ∀ i j, Tendsto (fun t => (T ^ t) i j) atTop (𝓝 (π j)) := fun i j => by
    simpa [mulVec_single_one] using hπ j i
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hnonneg : ∀ j, 0 ≤ π j := fun j =>
    ge_of_tendsto' (hlim i₀ j) fun t => (hT.pow t).1 i₀ j
  have hsum : ∑ j, π j = 1 := by
    have h := tendsto_finsetSum univ fun j _ => hlim i₀ j
    simp_rw [(hT.pow _).2 i₀] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hstat : π ᵥ* T = π := by
    funext j
    have h1 : Tendsto (fun t => (T ^ (t + 1)) i₀ j) atTop (𝓝 (π j)) :=
      (hlim i₀ j).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun t => (T ^ (t + 1)) i₀ j) atTop (𝓝 (∑ l, π l * T l j)) := by
      simp_rw [pow_succ, Matrix.mul_apply]
      exact tendsto_finsetSum univ fun l _ => (hlim i₀ l).mul_const _
    simp only [vecMul, dotProduct]
    exact tendsto_nhds_unique h2 h1
  obtain ⟨k, hk⟩ := hP
  have hpowstat : ∀ t, π ᵥ* T ^ t = π := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← vecMul_vecMul, ih, hstat]
  have hpos : ∀ j, 0 < π j := by
    intro j
    rw [← hpowstat k]
    simp only [vecMul, dotProduct]
    obtain ⟨l, hl⟩ : ∃ l, 0 < π l := by
      by_contra h
      push Not at h
      have : ∑ j, π j = 0 := sum_eq_zero fun j _ => le_antisymm (h j) (hnonneg j)
      linarith
    exact sum_pos' (fun l _ => mul_nonneg (hnonneg l) (hk l j).le)
      ⟨l, mem_univ _, mul_pos hl (hk l j)⟩
  refine ⟨π, ⟨hnonneg, hsum, hstat⟩, hpos, hlim, fun p i => ?_⟩
  simp only [mulVec, dotProduct]
  exact tendsto_finsetSum univ fun j _ => (hlim i j).mul_const _

/-- The influence vector of a stochastic primitive matrix is unique (among
probability vectors). -/
theorem influence_unique [Nonempty ι] {T : Matrix ι ι ℝ} (hT : IsStochastic T) (hP : IsPrimitive T)
    {π π' : ι → ℝ} (h : IsInfluence T π) (h' : IsInfluence T π') : π = π' := by
  obtain ⟨ρ, -, -, hlim, -⟩ := influence hT hP
  have key : ∀ {σ : ι → ℝ}, IsInfluence T σ → σ = ρ := by
    intro σ hσ
    have hpow : ∀ t, σ ᵥ* T ^ t = σ := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, ← vecMul_vecMul, ih, hσ.2.2]
    funext j
    have h1 : Tendsto (fun t => (σ ᵥ* T ^ t) j) atTop (𝓝 (∑ l, σ l * ρ j)) := by
      simp only [vecMul, dotProduct]
      exact tendsto_finsetSum univ fun l _ => (hlim l j).const_mul _
    rw [← sum_mul, hσ.2.1, one_mul] at h1
    simp_rw [hpow] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  rw [key h, key h']

/-- Row-normalization of a nonnegative weight matrix. -/
def normalize (g : Matrix ι ι ℝ) : Matrix ι ι ℝ := fun i j => g i j / ∑ l, g i l

omit [DecidableEq ι] in
theorem isStochastic_normalize {g : Matrix ι ι ℝ} (hg : ∀ i j, 0 ≤ g i j)
    (hd : ∀ i, 0 < ∑ l, g i l) : IsStochastic (normalize g) := by
  refine ⟨fun i j => div_nonneg (hg i j) (hd i).le, fun i => ?_⟩
  simp only [normalize, ← Finset.sum_div]
  exact div_self (hd i).ne'

omit [DecidableEq ι] in
/-- **Degree centrality** (Golub–Jackson, undirected case): for a symmetric
weight matrix with positive weighted degrees, the degree-proportional vector is
an influence vector of the row-normalized listening matrix. (Nonnegativity of
`g` is not needed for this identity; it is needed for `normalize g` to be
stochastic, `isStochastic_normalize`.) -/
theorem influence_degree {g : Matrix ι ι ℝ} (hsym : gᵀ = g)
    (hd : ∀ i, 0 < ∑ l, g i l) [Nonempty ι] :
    IsInfluence (normalize g) fun i => (∑ l, g i l) / ∑ m, ∑ l, g m l := by
  have hD : 0 < ∑ m, ∑ l, g m l := sum_pos (fun m _ => hd m) univ_nonempty
  refine ⟨fun i => div_nonneg (hd i).le hD.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hD.ne']
  · funext j
    simp only [vecMul, dotProduct, normalize]
    have : ∀ i, (∑ l, g i l) / (∑ m, ∑ l, g m l) * (g i j / ∑ l, g i l)
        = g i j / ∑ m, ∑ l, g m l := fun i => by
      field_simp [(hd i).ne']
    simp_rw [this, ← Finset.sum_div]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    have := congrFun (congrFun hsym j) i
    simpa [transpose_apply] using this

/-- **Degree-weighted consensus**: in a primitive undirected network, beliefs
converge to the degree-weighted average of initial beliefs. -/
theorem consensus_degree {g : Matrix ι ι ℝ} (hg : ∀ i j, 0 ≤ g i j) (hsym : gᵀ = g)
    (hd : ∀ i, 0 < ∑ l, g i l) (hP : IsPrimitive (normalize g)) (p : ι → ℝ) (i : ι) :
    Tendsto (fun t => (normalize g ^ t *ᵥ p) i) atTop
      (𝓝 ((∑ j, (∑ l, g j l) * p j) / ∑ m, ∑ l, g m l)) := by
  have : Nonempty ι := ⟨i⟩
  have hT := isStochastic_normalize hg hd
  obtain ⟨π, hπ, -, -, hconv⟩ := influence hT hP
  have := influence_unique hT hP hπ (influence_degree hsym hd)
  convert hconv p i using 2
  rw [this]
  simp only [dotProduct]
  rw [Finset.sum_div]
  exact sum_congr rfl fun j _ => by ring

/-- A matrix with all entries positive is primitive. -/
theorem primitive_of_pos {T : Matrix ι ι ℝ} (h : ∀ i j, 0 < T i j) : IsPrimitive T :=
  ⟨1, by simpa using h⟩

/-- Non-vacuity: two agents who weigh each other equally. -/
def half : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

theorem half_stochastic : IsStochastic half :=
  ⟨fun _ _ => by norm_num [half], fun _ => by norm_num [half, Fin.sum_univ_two]⟩

theorem half_primitive : IsPrimitive half := primitive_of_pos fun _ _ => by norm_num [half]

/-- `half` is the row-normalized complete graph with self-loops (all weights `1`),
a non-vacuity witness for `consensus_degree`. -/
theorem normalize_ones : normalize (fun _ _ : Fin 2 => (1 : ℝ)) = half := by
  funext i j; norm_num [normalize, half, Fin.sum_univ_two]

/-- Two agents who listen only to each other. -/
def swap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem swap_stochastic : IsStochastic swap := by
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
    simp [swap, Fin.sum_univ_two]

theorem swap_influence : IsInfluence swap ![1 / 2, 1 / 2] := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · funext j; fin_cases j <;> simp [swap, vecMul, dotProduct, Fin.sum_univ_two]

theorem swap_sq : swap ^ 2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swap, sq, Matrix.mul_apply, Fin.sum_univ_two]

theorem swap_not_primitive : ¬ IsPrimitive swap := by
  rintro ⟨k, hk⟩
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h := hk 0 1
    rw [← two_mul, pow_mul, swap_sq, one_pow] at h
    simp at h
  · have h := hk 0 0
    rw [pow_succ, pow_mul, swap_sq, one_pow, one_mul] at h
    simp [swap] at h

/-- **Primitivity is needed**: under `swap`, beliefs from `(1, 0)` oscillate
and never converge. -/
theorem swap_not_converge :
    ¬ ∃ L : ℝ, Tendsto (fun t => (swap ^ t *ᵥ ![1, 0]) 0) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have he : ∀ m, (swap ^ (2 * m) *ᵥ ![(1 : ℝ), 0]) 0 = 1 := fun m => by
    rw [pow_mul, swap_sq, one_pow]; simp
  have ho : ∀ m, (swap ^ (2 * m + 1) *ᵥ ![(1 : ℝ), 0]) 0 = 0 := fun m => by
    rw [pow_succ, pow_mul, swap_sq, one_pow, one_mul]; simp [swap, mulVec, dotProduct]
  have h1 : Tendsto (fun m => (swap ^ (2 * m) *ᵥ ![(1 : ℝ), 0]) 0) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_mono (fun m => show m ≤ 2 * m by omega) tendsto_id)
  have h0 : Tendsto (fun m => (swap ^ (2 * m + 1) *ᵥ ![(1 : ℝ), 0]) 0) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_mono (fun m => show m ≤ 2 * m + 1 by omega) tendsto_id)
  simp_rw [he] at h1
  simp_rw [ho] at h0
  have e1 := tendsto_nhds_unique tendsto_const_nhds h1
  have e0 := tendsto_nhds_unique tendsto_const_nhds h0
  linarith

end DeGroot

end Econ
