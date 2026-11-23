/-
# Nash's bargaining solution: the axiomatic characterization

Nash (1950); MWG §22.E, Osborne–Rubinstein, *Bargaining and
Markets*, Ch. 2. A **bargaining problem** is a compact convex set `S ⊆ ℝ²` of feasible utility
pairs with a disagreement point `d ∈ S`, such that some feasible point is strictly better than
`d` for both players. A **bargaining solution** picks a feasible point for every problem.

The **Nash solution** maximizes the Nash product `(s₁ − d₁)(s₂ − d₂)` over feasible points with
`s ≥ d`.

Nash's axioms on a solution `f`:
* **weak Pareto efficiency** (`IsWeakPareto`): no feasible point is strictly better for both;
* **symmetry**: in a symmetric problem the two players get the same utility;
* **invariance to positive affine transformations** of either player's utility;
* **independence of irrelevant alternatives** (IIA): shrinking the feasible set, keeping `d`
  and the solution, does not change the solution.

Main results:
* `exists_nashSolution`: every problem has a Nash solution, and it is strictly better than
  `d` for both players.
* `nash_bargaining_theorem` (Nash 1950): a solution satisfying the four axioms picks a Nash
  solution in every problem.
* `nashSolution_unique`: the Nash solution is unique; `eq_nashSol_of_axioms`: so the four
  axioms pin down the rule `nashSol`.
* `nashSol_axioms`: conversely, `nashSol` satisfies all four axioms.
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

open Set

/-- A two-player **bargaining problem**. -/
structure BargProblem where
  /-- Feasible utility pairs. -/
  S : Set (ℝ × ℝ)
  /-- Disagreement point. -/
  d : ℝ × ℝ
  compact : IsCompact S
  convex : Convex ℝ S
  d_mem : d ∈ S
  exists_gt : ∃ s ∈ S, d.1 < s.1 ∧ d.2 < s.2

/-- The **Nash product** of `s` relative to `d`. -/
def nashProduct (d s : ℝ × ℝ) : ℝ := (s.1 - d.1) * (s.2 - d.2)

/-- `n` is a **Nash solution** of `P`: it maximizes the Nash product among feasible points
that are individually rational (weakly better than `d` for both players). -/
def IsNashSolution (P : BargProblem) (n : ℝ × ℝ) : Prop :=
  n ∈ P.S ∧ P.d.1 ≤ n.1 ∧ P.d.2 ≤ n.2 ∧
    ∀ s ∈ P.S, P.d.1 ≤ s.1 → P.d.2 ≤ s.2 → nashProduct P.d s ≤ nashProduct P.d n

/-- **A Nash solution exists**, and it is strictly better than `d` for both players. -/
theorem exists_nashSolution (P : BargProblem) :
    ∃ n, IsNashSolution P n ∧ P.d.1 < n.1 ∧ P.d.2 < n.2 := by
  set K := P.S ∩ {s | P.d.1 ≤ s.1 ∧ P.d.2 ≤ s.2}
  have hK : IsCompact K := P.compact.inter_right
    ((isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_const
      continuous_snd))
  have hKne : K.Nonempty := ⟨P.d, P.d_mem, le_rfl, le_rfl⟩
  have hcont : Continuous (nashProduct P.d) :=
    (continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)
  obtain ⟨n, hnK, hmax⟩ := hK.exists_isMaxOn hKne hcont.continuousOn
  obtain ⟨s, hs, hs1, hs2⟩ := P.exists_gt
  have hpos : 0 < nashProduct P.d n :=
    lt_of_lt_of_le (mul_pos (sub_pos.2 hs1) (sub_pos.2 hs2))
      (hmax ⟨hs, hs1.le, hs2.le⟩)
  have h1 := hnK.2.1
  have h2 := hnK.2.2
  refine ⟨n, ⟨hnK.1, h1, h2, fun s hs h1 h2 => hmax ⟨hs, h1, h2⟩⟩, ?_, ?_⟩
  · by_contra h
    have : n.1 = P.d.1 := le_antisymm (not_lt.1 h) h1
    simp [nashProduct, this] at hpos
  · by_contra h
    have : n.2 = P.d.2 := le_antisymm (not_lt.1 h) h2
    simp [nashProduct, this] at hpos

/-- The positive affine transformation `s ↦ (a₁ s₁ + b₁, a₂ s₂ + b₂)`. -/
def affMap (a₁ a₂ b₁ b₂ : ℝ) (s : ℝ × ℝ) : ℝ × ℝ := (a₁ * s.1 + b₁, a₂ * s.2 + b₂)

lemma continuous_affMap (a₁ a₂ b₁ b₂ : ℝ) : Continuous (affMap a₁ a₂ b₁ b₂) :=
  ((continuous_const.mul continuous_fst).add continuous_const).prodMk
    ((continuous_const.mul continuous_snd).add continuous_const)

lemma convex_image_affMap {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) (a₁ a₂ b₁ b₂ : ℝ) :
    Convex ℝ (affMap a₁ a₂ b₁ b₂ '' S) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ θ η hθ hη hθη
  refine ⟨θ • u + η • v, hS hu hv hθ hη hθη, ?_⟩
  ext
  · simp only [affMap, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-b₁) * hθη
  · simp only [affMap, Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-b₂) * hθη

/-- The image of a bargaining problem under a positive affine transformation. -/
def BargProblem.affine (P : BargProblem) (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    BargProblem where
  S := affMap a₁ a₂ b₁ b₂ '' P.S
  d := affMap a₁ a₂ b₁ b₂ P.d
  compact := P.compact.image (continuous_affMap a₁ a₂ b₁ b₂)
  convex := convex_image_affMap P.convex a₁ a₂ b₁ b₂
  d_mem := mem_image_of_mem _ P.d_mem
  exists_gt := by
    obtain ⟨s, hs, h1, h2⟩ := P.exists_gt
    exact ⟨_, mem_image_of_mem _ hs, by simp only [affMap]; nlinarith,
      by simp only [affMap]; nlinarith⟩

/-- A **symmetric** bargaining problem. -/
def BargProblem.IsSymmetric (P : BargProblem) : Prop :=
  P.d.1 = P.d.2 ∧ ∀ s ∈ P.S, (s.2, s.1) ∈ P.S

/-- A **bargaining solution**: a rule picking an outcome for every problem. -/
abbrev BargSolution := BargProblem → ℝ × ℝ

/-- Feasibility and **weak Pareto efficiency**. -/
def IsWeakPareto (f : BargSolution) : Prop :=
  ∀ P, f P ∈ P.S ∧ ¬ ∃ s ∈ P.S, (f P).1 < s.1 ∧ (f P).2 < s.2

/-- **Symmetry.** -/
def IsSymmetricSol (f : BargSolution) : Prop := ∀ P, P.IsSymmetric → (f P).1 = (f P).2

/-- **Invariance to positive affine transformations** of utilities. -/
def IsAffineInvariant (f : BargSolution) : Prop :=
  ∀ P a₁ a₂ b₁ b₂ (ha₁ : 0 < a₁) (ha₂ : 0 < a₂),
    f (P.affine a₁ a₂ b₁ b₂ ha₁ ha₂) = affMap a₁ a₂ b₁ b₂ (f P)

/-- **Independence of irrelevant alternatives.** -/
def IsIIA (f : BargSolution) : Prop :=
  ∀ P Q : BargProblem, P.d = Q.d → P.S ⊆ Q.S → f Q ∈ P.S → f P = f Q

/-- In a problem with `d = 0` whose Nash product is maximized at `(1, 1)`, every feasible
point satisfies `s₁ + s₂ ≤ 2` (the tangent line of `s₁ s₂ = 1` at `(1, 1)`). -/
lemma sum_le_two_of_max {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) (h11 : ((1 : ℝ), (1 : ℝ)) ∈ S)
    (hmax : ∀ z ∈ S, 0 ≤ z.1 → 0 ≤ z.2 → z.1 * z.2 ≤ 1) : ∀ s ∈ S, s.1 + s.2 ≤ 2 := by
  intro s hs
  by_contra hgt
  push Not at hgt
  set g := s.1 + s.2 - 2
  set K := |s.1 - 1| + |s.2 - 1| + 1
  have hK : 1 ≤ K := by simp only [K]; linarith [abs_nonneg (s.1 - 1), abs_nonneg (s.2 - 1)]
  have hg : 0 < g := by simp only [g]; linarith
  have hgK : g ≤ K := by
    simp only [g, K]; linarith [le_abs_self (s.1 - 1), le_abs_self (s.2 - 1)]
  set ε := g / (2 * K ^ 2)
  have hε : 0 < ε := by positivity
  have hεK : ε * K ≤ 1 / 2 := by
    simp only [ε]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hε1 : ε ≤ 1 := by nlinarith
  set z : ℝ × ℝ := (1 - ε) • ((1 : ℝ), (1 : ℝ)) + ε • s
  have hz : z ∈ S := hS h11 hs (by linarith) hε.le (by ring)
  have hz1 : z.1 = 1 + ε * (s.1 - 1) := by simp [z]; ring
  have hz2 : z.2 = 1 + ε * (s.2 - 1) := by simp [z]; ring
  have hb1 : |ε * (s.1 - 1)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hε]
    calc ε * |s.1 - 1| ≤ ε * K := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          simp only [K]; linarith [abs_nonneg (s.2 - 1)]
      _ ≤ 1 / 2 := hεK
  have hb2 : |ε * (s.2 - 1)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hε]
    calc ε * |s.2 - 1| ≤ ε * K := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          simp only [K]; linarith [abs_nonneg (s.1 - 1)]
      _ ≤ 1 / 2 := hεK
  have hz1p : 0 ≤ z.1 := by rw [hz1]; linarith [neg_abs_le (ε * (s.1 - 1))]
  have hz2p : 0 ≤ z.2 := by rw [hz2]; linarith [neg_abs_le (ε * (s.2 - 1))]
  have := hmax z hz hz1p hz2p
  rw [hz1, hz2] at this
  -- `z₁ z₂ − 1 = ε (g + ε (s₁ − 1)(s₂ − 1)) ≥ ε g / 2 > 0`.
  have hprod : |(s.1 - 1) * (s.2 - 1)| ≤ K ^ 2 := by
    rw [abs_mul]
    have h1 : |s.1 - 1| ≤ K := by simp only [K]; linarith [abs_nonneg (s.2 - 1)]
    have h2 : |s.2 - 1| ≤ K := by simp only [K]; linarith [abs_nonneg (s.1 - 1)]
    nlinarith [abs_nonneg (s.1 - 1), abs_nonneg (s.2 - 1)]
  have hεK2 : ε * K ^ 2 = g / 2 := by simp only [ε]; field_simp
  have key : ε * ((s.1 - 1) * (s.2 - 1)) ≥ -(g / 2) := by
    have := neg_abs_le ((s.1 - 1) * (s.2 - 1))
    nlinarith
  nlinarith

/-- **Nash's bargaining theorem** (Nash 1950; MWG §22.E). A bargaining solution that is
weakly Pareto efficient, symmetric, invariant to positive affine transformations and
independent of irrelevant alternatives selects a Nash solution in every bargaining
problem. -/
theorem nash_bargaining_theorem (f : BargSolution) (hPE : IsWeakPareto f)
    (hSym : IsSymmetricSol f) (hAff : IsAffineInvariant f) (hIIA : IsIIA f) (P : BargProblem) :
    IsNashSolution P (f P) := by
  obtain ⟨n, hn, hn1, hn2⟩ := exists_nashSolution P
  -- Normalize: `d ↦ 0`, `n ↦ (1, 1)`.
  set a₁ := 1 / (n.1 - P.d.1)
  set a₂ := 1 / (n.2 - P.d.2)
  have ha₁ : 0 < a₁ := by simp only [a₁]; exact one_div_pos.2 (sub_pos.2 hn1)
  have ha₂ : 0 < a₂ := by simp only [a₂]; exact one_div_pos.2 (sub_pos.2 hn2)
  set b₁ := -a₁ * P.d.1
  set b₂ := -a₂ * P.d.2
  set L := affMap a₁ a₂ b₁ b₂
  have hL : ∀ s : ℝ × ℝ, L s = ((s.1 - P.d.1) / (n.1 - P.d.1), (s.2 - P.d.2) / (n.2 - P.d.2)) :=
    fun s => by
      simp only [L, affMap, a₁, a₂, b₁, b₂]
      ext <;> simp only <;> field_simp <;> ring
  set P' := P.affine a₁ a₂ b₁ b₂ ha₁ ha₂
  have hd' : P'.d = (0, 0) := by
    show L P.d = (0, 0); rw [hL]; simp
  have hn' : L n = (1, 1) := by
    rw [hL]; ext <;> simp only <;> field_simp
  have h11 : ((1 : ℝ), (1 : ℝ)) ∈ P'.S := hn' ▸ mem_image_of_mem L hn.1
  -- In `P'`, `(1, 1)` maximizes `z₁ z₂` among `z ≥ 0`.
  have hmax' : ∀ z ∈ P'.S, 0 ≤ z.1 → 0 ≤ z.2 → z.1 * z.2 ≤ 1 := by
    rintro _ ⟨u, hu, rfl⟩ hz1 hz2
    change 0 ≤ (L u).1 at hz1
    change 0 ≤ (L u).2 at hz2
    change (L u).1 * (L u).2 ≤ 1
    rw [hL] at hz1 hz2 ⊢
    simp only at hz1 hz2 ⊢
    have hp1 : 0 < n.1 - P.d.1 := sub_pos.2 hn1
    have hp2 : 0 < n.2 - P.d.2 := sub_pos.2 hn2
    have hu1 : P.d.1 ≤ u.1 := by
      have := (div_nonneg_iff.1 hz1); rcases this with h | h
      · linarith [h.1]
      · linarith [h.2]
    have hu2 : P.d.2 ≤ u.2 := by
      have := (div_nonneg_iff.1 hz2); rcases this with h | h
      · linarith [h.1]
      · linarith [h.2]
    have := hn.2.2.2 u hu hu1 hu2
    simp only [nashProduct] at this
    rw [div_mul_div_comm, div_le_one (by positivity)]
    exact this
  have hsum := sum_le_two_of_max P'.convex h11 hmax'
  -- A bounding symmetric problem `T ⊇ S'`.
  obtain ⟨M, hM0, hM⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ P'.S, -M ≤ s.1 ∧ -M ≤ s.2 := by
    obtain ⟨m₁, hm₁⟩ := (P'.compact.image continuous_fst).bddBelow
    obtain ⟨m₂, hm₂⟩ := (P'.compact.image continuous_snd).bddBelow
    refine ⟨|m₁| + |m₂|, by positivity, fun s hs => ⟨?_, ?_⟩⟩
    · linarith [hm₁ (mem_image_of_mem Prod.fst hs), neg_abs_le m₁, abs_nonneg m₂]
    · linarith [hm₂ (mem_image_of_mem Prod.snd hs), neg_abs_le m₂, abs_nonneg m₁]
  let TS : Set (ℝ × ℝ) := {s | s.1 + s.2 ≤ 2 ∧ -M ≤ s.1 ∧ -M ≤ s.2}
  have hTcl : IsClosed TS :=
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const).inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const continuous_snd))
  have hTbdd : TS ⊆ Icc (-M, -M) (2 + M, 2 + M) := fun s hs => by
    obtain ⟨h1, h2, h3⟩ := hs
    exact ⟨⟨h2, h3⟩, ⟨by linarith, by linarith⟩⟩
  let T : BargProblem :=
    { S := TS
      d := P'.d
      compact := (isCompact_Icc.of_isClosed_subset hTcl hTbdd)
      convex := by
        intro x hx y hy θ η hθ hη hθη
        obtain ⟨hx1, hx2, hx3⟩ := hx
        obtain ⟨hy1, hy2, hy3⟩ := hy
        simp only [TS, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
      d_mem := by rw [hd']; exact ⟨by norm_num, by linarith, by linarith⟩
      exists_gt := ⟨(1, 1), ⟨by norm_num, by linarith, by linarith⟩, by rw [hd']; norm_num,
        by rw [hd']; norm_num⟩ }
  -- `f T = (1, 1)` by symmetry and weak Pareto efficiency.
  have hTsym : T.IsSymmetric := ⟨by simp [T, hd'], fun s ⟨h1, h2, h3⟩ =>
    ⟨by simp only; linarith, h3, h2⟩⟩
  have hfT : f T = (1, 1) := by
    obtain ⟨hmem, hnd⟩ := hPE T
    have heq := hSym T hTsym
    obtain ⟨h1, -, -⟩ := hmem
    have hle : (f T).1 ≤ 1 := by linarith
    have hge : 1 ≤ (f T).1 := by
      by_contra hlt
      push Not at hlt
      exact hnd ⟨(1, 1), ⟨by norm_num, by linarith, by linarith⟩, hlt, by rw [← heq]; exact hlt⟩
    ext
    · exact le_antisymm hle hge
    · rw [← heq]; exact le_antisymm hle hge
  -- IIA: `S' ⊆ T` and `(1, 1) ∈ S'`.
  have hfP' : f P' = (1, 1) := by
    rw [← hfT]
    refine hIIA P' T rfl (fun s hs => ⟨hsum s hs, (hM s hs).1, (hM s hs).2⟩) ?_
    rw [hfT]; exact h11
  -- Invariance: `L (f P) = (1, 1) = L n`, so `f P = n`.
  have hLf : L (f P) = L n := by
    rw [hn', ← hfP']; exact (hAff P a₁ a₂ b₁ b₂ ha₁ ha₂).symm
  have : f P = n := by
    rw [hL, hL] at hLf
    simp only [Prod.mk.injEq] at hLf
    have hp1 : n.1 - P.d.1 ≠ 0 := (sub_pos.2 hn1).ne'
    have hp2 : n.2 - P.d.2 ≠ 0 := (sub_pos.2 hn2).ne'
    rw [div_left_inj₀ hp1, div_left_inj₀ hp2] at hLf
    ext
    · linarith [hLf.1]
    · linarith [hLf.2]
  rw [this]; exact hn

/-- The Nash product at a Nash solution is strictly positive. -/
lemma IsNashSolution.nashProduct_pos {P : BargProblem} {n : ℝ × ℝ} (hn : IsNashSolution P n) :
    0 < nashProduct P.d n := by
  obtain ⟨s, hs, hs1, hs2⟩ := P.exists_gt
  exact lt_of_lt_of_le (mul_pos (sub_pos.2 hs1) (sub_pos.2 hs2))
    (hn.2.2.2 s hs hs1.le hs2.le)

/-- **The Nash solution is unique** (the Nash product is strictly quasi-concave on the
individually rational part of `S`, and `S` is convex). -/
theorem nashSolution_unique {P : BargProblem} {n m : ℝ × ℝ} (hn : IsNashSolution P n)
    (hm : IsNashSolution P m) : n = m := by
  have pn := hn.nashProduct_pos
  have pm := hm.nashProduct_pos
  have hle1 := hn.2.2.2 m hm.1 hm.2.1 hm.2.2.1
  have hle2 := hm.2.2.2 n hn.1 hn.2.1 hn.2.2.1
  simp only [nashProduct] at pn pm hle1 hle2
  set a₁ := n.1 - P.d.1 with ha₁
  set a₂ := n.2 - P.d.2 with ha₂
  set b₁ := m.1 - P.d.1 with hb₁
  set b₂ := m.2 - P.d.2 with hb₂
  have hp : a₁ * a₂ = b₁ * b₂ := le_antisymm hle2 hle1
  have a1 : 0 < a₁ := by
    rcases lt_or_eq_of_le hn.2.1 with h | h
    · simp only [ha₁]; linarith
    · simp only [ha₁, ← h, sub_self, zero_mul] at pn; exact absurd pn (lt_irrefl 0)
  have a2 : 0 < a₂ := pos_of_mul_pos_right pn a1.le
  have b1 : 0 < b₁ := by
    rcases lt_or_eq_of_le hm.2.1 with h | h
    · simp only [hb₁]; linarith
    · simp only [hb₁, ← h, sub_self, zero_mul] at pm; exact absurd pm (lt_irrefl 0)
  have b2 : 0 < b₂ := pos_of_mul_pos_right pm b1.le
  -- The midpoint is feasible and individually rational.
  set z : ℝ × ℝ := (1 / 2 : ℝ) • n + (1 / 2 : ℝ) • m
  have hz : z ∈ P.S := P.convex hn.1 hm.1 (by norm_num) (by norm_num) (by norm_num)
  have hz1 : z.1 - P.d.1 = (a₁ + b₁) / 2 := by simp only [z, a₁, b₁]; simp; ring
  have hz2 : z.2 - P.d.2 = (a₂ + b₂) / 2 := by simp only [z, a₂, b₂]; simp; ring
  have hzle := hn.2.2.2 z hz (by linarith) (by linarith)
  simp only [nashProduct, hz1, hz2, ← ha₁, ← ha₂] at hzle
  -- `(a₁ + b₁)(a₂ + b₂) ≤ 4 a₁ a₂` forces `a₁ b₂ = a₂ b₁`, hence `a = b`.
  have hs : a₁ * b₂ + a₂ * b₁ ≤ 2 * (a₁ * a₂) := by nlinarith
  have hx : 0 ≤ a₁ * b₂ + a₂ * b₁ := by positivity
  have hsq : (a₁ * b₂ + a₂ * b₁) ^ 2 ≤ (2 * (a₁ * a₂)) ^ 2 := pow_le_pow_left₀ hx hs 2
  have hxy : (a₁ * b₂) * (a₂ * b₁) = (a₁ * a₂) * (a₁ * a₂) := by
    rw [show (a₁ * b₂) * (a₂ * b₁) = (a₁ * a₂) * (b₁ * b₂) by ring, ← hp]
  have h0 : (a₁ * b₂ - a₂ * b₁) ^ 2 ≤ 0 := by nlinarith
  have heq : a₁ * b₂ = a₂ * b₁ := by
    have := le_antisymm h0 (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  have e2 : b₂ = a₂ := by
    have : a₁ * b₂ = a₁ * a₂ := by nlinarith
    exact mul_left_cancel₀ a1.ne' this
  have e1 : b₁ = a₁ := by
    rw [e2] at hp
    exact (mul_right_cancel₀ a2.ne' hp).symm
  ext
  · linarith [ha₁, hb₁]
  · linarith [ha₂, hb₂]

/-- **The Nash bargaining solution**, as a rule. -/
noncomputable def nashSol : BargSolution := fun P => (exists_nashSolution P).choose

theorem nashSol_spec (P : BargProblem) : IsNashSolution P (nashSol P) :=
  (exists_nashSolution P).choose_spec.1

/-- A solution satisfies Nash's axioms iff it is the Nash solution (uniqueness form of
Nash's theorem). -/
theorem eq_nashSol_of_axioms (f : BargSolution) (hPE : IsWeakPareto f)
    (hSym : IsSymmetricSol f) (hAff : IsAffineInvariant f) (hIIA : IsIIA f) : f = nashSol :=
  funext fun P => nashSolution_unique (nash_bargaining_theorem f hPE hSym hAff hIIA P)
    (nashSol_spec P)

/-- **The Nash solution satisfies the four axioms** (the converse half of Nash's theorem). -/
theorem nashSol_axioms :
    IsWeakPareto nashSol ∧ IsSymmetricSol nashSol ∧ IsAffineInvariant nashSol ∧
      IsIIA nashSol := by
  refine ⟨fun P => ?_, fun P hP => ?_, fun P a₁ a₂ b₁ b₂ ha₁ ha₂ => ?_, fun P Q hd hPQ hQ => ?_⟩
  · -- Weak Pareto: a strictly better point has a strictly larger Nash product.
    have hn := nashSol_spec P
    refine ⟨hn.1, fun ⟨s, hs, h1, h2⟩ => ?_⟩
    have := hn.2.2.2 s hs (by linarith [hn.2.1]) (by linarith [hn.2.2.1])
    simp only [nashProduct] at this
    have e1 : 0 ≤ (nashSol P).1 - P.d.1 := sub_nonneg.2 hn.2.1
    have e2 : 0 ≤ (nashSol P).2 - P.d.2 := sub_nonneg.2 hn.2.2.1
    linarith [mul_lt_mul'' (sub_lt_sub_right h1 P.d.1) (sub_lt_sub_right h2 P.d.2) e1 e2]
  · -- Symmetry: the swapped Nash solution is again a Nash solution.
    have hn := nashSol_spec P
    obtain ⟨hd, hS⟩ := hP
    have hsw : IsNashSolution P ((nashSol P).2, (nashSol P).1) := by
      refine ⟨hS _ hn.1, by simp only; rw [hd]; exact hn.2.2.1,
        by simp only; rw [← hd]; exact hn.2.1, fun s hs h1 h2 => ?_⟩
      have := hn.2.2.2 (s.2, s.1) (hS s hs) (by simp only; rw [hd]; exact h2)
        (by simp only; rw [← hd]; exact h1)
      simp only [nashProduct, hd] at this ⊢
      linarith
    have := congrArg Prod.fst (nashSolution_unique hn hsw)
    exact this
  · -- Invariance: the Nash product is scaled by `a₁ a₂ > 0`.
    have hn := nashSol_spec P
    apply nashSolution_unique (nashSol_spec _)
    have hprod : ∀ s, nashProduct (affMap a₁ a₂ b₁ b₂ P.d) (affMap a₁ a₂ b₁ b₂ s) =
        a₁ * a₂ * nashProduct P.d s := fun s => by simp only [nashProduct, affMap]; ring
    refine ⟨mem_image_of_mem _ hn.1, ?_, ?_, ?_⟩
    · show a₁ * P.d.1 + b₁ ≤ a₁ * (nashSol P).1 + b₁; nlinarith [hn.2.1]
    · show a₂ * P.d.2 + b₂ ≤ a₂ * (nashSol P).2 + b₂; nlinarith [hn.2.2.1]
    · rintro _ ⟨u, hu, rfl⟩ h1 h2
      change a₁ * P.d.1 + b₁ ≤ a₁ * u.1 + b₁ at h1
      change a₂ * P.d.2 + b₂ ≤ a₂ * u.2 + b₂ at h2
      show nashProduct (affMap a₁ a₂ b₁ b₂ P.d) _ ≤ nashProduct (affMap a₁ a₂ b₁ b₂ P.d) _
      rw [hprod, hprod]
      have := hn.2.2.2 u hu (le_of_mul_le_mul_left (by linarith) ha₁)
        (le_of_mul_le_mul_left (by linarith) ha₂)
      exact mul_le_mul_of_nonneg_left this (by positivity)
  · -- IIA: the maximizer over the larger set, if feasible in the smaller, maximizes there.
    have hn := nashSol_spec Q
    apply nashSolution_unique (nashSol_spec P)
    refine ⟨hQ, by rw [hd]; exact hn.2.1, by rw [hd]; exact hn.2.2.1, fun s hs h1 h2 => ?_⟩
    rw [hd] at h1 h2 ⊢
    exact hn.2.2.2 s (hPQ hs) h1 h2

/-- Witness that `BargProblem` is inhabited: the symmetric triangle
`{s ≥ 0, s₁ + s₂ ≤ 2}` with `d = 0`, whose Nash solution is `(1, 1)`. -/
example : ∃ P : BargProblem, IsNashSolution P (1, 1) := by
  let S : Set (ℝ × ℝ) := {s | 0 ≤ s.1 ∧ 0 ≤ s.2 ∧ s.1 + s.2 ≤ 2}
  have hcl : IsClosed S :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hsub : S ⊆ Icc (0, 0) (2, 2) := fun s ⟨h1, h2, h3⟩ =>
    ⟨⟨h1, h2⟩, ⟨by linarith, by linarith⟩⟩
  have hcv : Convex ℝ S := by
    intro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ θ η hθ hη hθη
    simp only [S, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    refine ⟨by positivity, by positivity, by nlinarith⟩
  let P : BargProblem :=
    { S := S
      d := (0, 0)
      compact := isCompact_Icc.of_isClosed_subset hcl hsub
      convex := hcv
      d_mem := ⟨le_rfl, le_rfl, by norm_num⟩
      exists_gt := ⟨(1, 1), ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩ }
  refine ⟨P, ?_⟩
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, ?_⟩
  rintro s ⟨-, -, h⟩ h1 h2
  simp only [P, nashProduct, sub_zero]
  nlinarith [sq_nonneg (s.1 - s.2)]

end Econ
