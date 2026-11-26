/-
# Approximate equilibria of large finite economies without convexity

**The economics.** A finite economy with non-convex preferences may have no
Walrasian equilibrium. Starr (1969), using the Shapley–Folkman lemma, showed
that it nevertheless has an *approximate* one whose error does not grow with
the number of agents, so per capita it vanishes in large economies. This is
the finite-economy counterpart of Aumann's (1966) continuum existence theorem
(`GE/AumannExistence.lean`), and a micro-to-macro bridge (PLAN §B2): the exact
continuum equilibrium is mirrored by approximate equilibria of large finite
economies at the same prices (no convergence statement is formalized).

**Results.**
* `exists_counts`, `exists_assign`: rounding convex weights to integer group
  sizes and assigning agents to groups of those sizes.
* `exists_approxEquilibrium_replica`: finitely many types with continuous,
  strongly monotone (not necessarily convex) preferences and endowments `≫ 0`.
  There are prices `p ≫ 0` and a constant `C` such that for every `n`, the
  economy with `n` agents of each type has an allocation in which every agent
  consumes a demanded bundle at `p` and aggregate excess demand is at most `C`
  in every good. The prices and `C` do not depend on `n`.
* Witness (`sqReplica_*`): utility `x₀² + x₁²`, endowment `(1, 1)`; the theorem
  applies for every `n`, while for every **odd** `n` there is no exact
  equilibrium at any prices (`sqReplica_odd_no_equilibrium`, via
  `positivePrices_of_mem_demand_uSq` and the corner characterization
  `mem_demand_uSq`).

**Scope.** This is a replica analogue of Starr's theorem (the economy grows by
copying a fixed finite list of types), proved by Carathéodory and integer
rounding; no Shapley–Folkman lemma is needed. Starr's theorem holds for
arbitrary finite economies, with a bound depending on the number of goods and a
measure of non-convexity of preferences, independent of the number of agents
**and of types** (Shapley–Folkman leaves at most `L` agents off their demand).
Here `C` grows with the number of types `|T|` (like `|T| (L + 1)`), so the
theorem says nothing about economies with many distinct one-agent types; the
general form is not formalized. The equilibrium notion: every agent optimizes
exactly and aggregate excess demand is at most `C` in each good, so the
allocation need not be feasible; per agent the error is `C / (n |T|)`.
Starr's quasi-equilibrium is instead feasible with at most `L` agents off
their demand; the two forms differ only in where the error is put.
-/
module

public import EconLean.GE.AumannExistence

@[expose] public section

noncomputable section

namespace Econ

namespace ApproxEquilibrium

open Finset

/-- **Integer rounding of convex weights.** For weights `w₀, …, w_M ≥ 0`
summing to `1` and any `n`, there are counts `cₖ ∈ ℕ` summing to `n` with
`|cₖ - n wₖ| ≤ M + 1`. (Round down all but the last weight and give the
remainder to the last.) -/
theorem exists_counts {M : ℕ} (w : Fin (M + 1) → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (n : ℕ) :
    ∃ cnt : Fin (M + 1) → ℕ, ∑ k, cnt k = n ∧ ∀ k, |(cnt k : ℝ) - n * w k| ≤ M + 1 := by
  set fl : Fin M → ℕ := fun k => ⌊(n : ℝ) * w k.castSucc⌋₊ with hfl
  have hfl_le : ∀ k, (fl k : ℝ) ≤ n * w k.castSucc := fun k =>
    Nat.floor_le (mul_nonneg n.cast_nonneg (hw0 _))
  have hfl_gt : ∀ k, (n : ℝ) * w k.castSucc - 1 < fl k := fun k => by
    have := Nat.lt_floor_add_one ((n : ℝ) * w k.castSucc)
    simp only [hfl]; linarith
  have hsum1 : ∑ k : Fin M, w k.castSucc + w (Fin.last M) = 1 := by
    rw [← hw1, Fin.sum_univ_castSucc]
  have hsumle : ((∑ k, fl k : ℕ) : ℝ) ≤ n := by
    push_cast
    calc ∑ k, (fl k : ℝ) ≤ ∑ k : Fin M, (n : ℝ) * w k.castSucc :=
          Finset.sum_le_sum fun k _ => hfl_le k
      _ = n * ∑ k : Fin M, w k.castSucc := by rw [Finset.mul_sum]
      _ ≤ n * 1 := by
          apply mul_le_mul_of_nonneg_left _ n.cast_nonneg
          linarith [hw0 (Fin.last M)]
      _ = n := mul_one _
  have hsumleN : ∑ k, fl k ≤ n := by exact_mod_cast hsumle
  refine ⟨Fin.snoc fl (n - ∑ k, fl k), ?_, fun k => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega
  · induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      rw [Nat.cast_sub hsumleN]
      push_cast
      have hlast : (n : ℝ) * w (Fin.last M) = n - ∑ k : Fin M, (n : ℝ) * w k.castSucc := by
        rw [← Finset.mul_sum]
        have : w (Fin.last M) = 1 - ∑ k : Fin M, w k.castSucc := by linarith
        rw [this]; ring
      rw [hlast]
      have h1 : ∑ k : Fin M, (fl k : ℝ) ≤ ∑ k : Fin M, (n : ℝ) * w k.castSucc :=
        Finset.sum_le_sum fun k _ => hfl_le k
      have h2 : ∑ k : Fin M, ((n : ℝ) * w k.castSucc - 1) ≤ ∑ k : Fin M, (fl k : ℝ) :=
        Finset.sum_le_sum fun k _ => (hfl_gt k).le
      rw [Finset.sum_sub_distrib] at h2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at h2
      rw [abs_le]
      constructor <;> linarith
    | cast k =>
      simp only [Fin.snoc_castSucc]
      rw [abs_le]
      have := hfl_le k
      have := hfl_gt k
      constructor <;> linarith

/-- **Assigning agents to groups of prescribed sizes.** If `∑ₖ cₖ = n`, the
agents `Fin n` can be mapped to groups so that group `k` has `cₖ` members;
hence any sum over agents of a group-dependent quantity is `∑ₖ cₖ gₖ`. -/
theorem exists_assign {N n : ℕ} (cnt : Fin N → ℕ) (h : ∑ k, cnt k = n) {V : Type*}
    [AddCommMonoid V] (g : Fin N → V) :
    ∃ f : Fin n → Fin N, ∑ j, g (f j) = ∑ k, cnt k • g k := by
  let e : Fin n ≃ (k : Fin N) × Fin (cnt k) := (finCongr h.symm).trans finSigmaFinEquiv.symm
  refine ⟨fun j => (e j).1, ?_⟩
  rw [e.sum_comp (fun s => g s.1), Fintype.sum_sigma]
  simp

/-- **Approximate equilibria of replica economies without convexity**
(a replica analogue of Starr 1969, proved by Carathéodory and rounding; the
finite shadow of Aumann 1966).
Finitely many types `t` have continuous, strongly monotone utilities `uₜ`
(**not** assumed quasiconcave) and endowments `ωₜ ≫ 0` (written
`PositivePrices (ω t)`, i.e. every coordinate positive). Then there are prices
`p ≫ 0` and a constant `C` such that for **every** replica size `n`, the
economy with `n` agents of each type (agents `T × Fin n`) has an allocation in
which **every agent consumes a demanded bundle** at prices `p`, and aggregate
excess demand is at most `C` in every good. `C` does not depend on `n`, so per
capita excess demand is `O(1/n)`.

Proof: take the convexified equilibrium (`exists_convexifiedEquilibrium`, unit
masses), write each mean bundle `x̄ₜ` as a convex combination of `L + 1`
demanded bundles (Carathéodory), and give each of them to a group of agents of
size `nwₖ` rounded to an integer (error at most `L + 1` agents per bundle). -/
theorem exists_approxEquilibrium_replica {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {T : Type*} [Fintype T] [Nonempty T] {u : T → (ι → ℝ) → ℝ}
    (hu : ∀ t, Continuous (u t)) (hmono : ∀ t, StronglyMonotone (prefOf (u t)))
    {ω : T → ι → ℝ} (hω : ∀ t, PositivePrices (ω t)) :
    ∃ (p : ι → ℝ) (C : ℝ), PositivePrices p ∧ ∀ n : ℕ, ∃ x : T × Fin n → ι → ℝ,
      (∀ a, x a ∈ demand (prefOf (u a.1)) p (cost p (ω a.1))) ∧
      ∀ i, |∑ a : T × Fin n, x a i - ∑ a : T × Fin n, ω a.1 i| ≤ C := by
  classical
  obtain ⟨p, xbar, hp, hx, hclear⟩ :=
    AumannExistence.exists_convexifiedEquilibrium (fun _ => (1 : ℝ)) (fun _ => one_pos) hu hmono hω
  simp only [one_smul] at hclear
  have hne : ∀ t, (demand (prefOf (u t)) p (cost p (ω t))).Nonempty := fun t => by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hx t
    rw [h, convexHull_empty] at this
    exact this
  set M := Module.finrank ℝ (ι → ℝ) with hM
  choose w z hw0 hw1 hz hwz using fun t => exists_fin_convexComb (hne t) (hx t)
  set C : ℝ := ∑ t, ∑ k, ∑ i, ((M : ℝ) + 1) * |z t k i| with hC
  refine ⟨p, C, hp, fun n => ?_⟩
  choose cnt hcnt hcntb using fun t => exists_counts (w t) (hw0 t) (hw1 t) n
  choose f hf using fun t => exists_assign (cnt t) (hcnt t) (z t)
  refine ⟨fun a => z a.1 (f a.1 a.2), fun a => hz a.1 _, fun i => ?_⟩
  have h1 : ∑ a : T × Fin n, z a.1 (f a.1 a.2) i = ∑ t, ∑ k, (cnt t k : ℝ) * z t k i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := congrFun (hf t) i
    simp only [Finset.sum_apply, nsmul_eq_mul] at this
    exact this
  have h2 : ∑ a : T × Fin n, ω a.1 i = ∑ t, ∑ k, (n : ℝ) * w t k * z t k i := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcl := congrFun hclear i
    simp only [Finset.sum_apply] at hcl
    have hx' : ∀ t, xbar t i = ∑ k, w t k * z t k i := fun t => by
      rw [← hwz t]; simp [Finset.sum_apply]
    rw [← Finset.mul_sum, ← hcl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hx' t, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, ← Finset.sum_sub_distrib]
  calc |∑ t, (∑ k, (cnt t k : ℝ) * z t k i - ∑ k, (n : ℝ) * w t k * z t k i)|
      ≤ ∑ t, |∑ k, (cnt t k : ℝ) * z t k i - ∑ k, (n : ℝ) * w t k * z t k i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, ∑ k, ((M : ℝ) + 1) * |z t k i| := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [show (cnt t k : ℝ) * z t k i - n * w t k * z t k i =
          ((cnt t k : ℝ) - n * w t k) * z t k i by ring, abs_mul]
        exact mul_le_mul_of_nonneg_right (hcntb t k) (abs_nonneg _)
    _ ≤ C := by
        refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun k _ => ?_
        exact Finset.single_le_sum (f := fun i => ((M : ℝ) + 1) * |z t k i|)
          (fun i _ => mul_nonneg (by positivity) (abs_nonneg _)) (Finset.mem_univ i)

/-! ### Witness: specialisation utility `x₀² + x₁²` -/

open Continuum.ContinuumEconomy in
/-- The replicas of the one-type economy with utility `x₀² + x₁²` (not
quasiconcave) and endowment `(1, 1)` have approximate equilibria at a common
price, with aggregate excess demand bounded uniformly in the number of agents. -/
theorem sqReplica_exists_approxEquilibrium :
    ∃ (p : Fin 2 → ℝ) (C : ℝ), PositivePrices p ∧ ∀ n : ℕ, ∃ x : Fin 1 × Fin n → Fin 2 → ℝ,
      (∀ a, x a ∈ demand (prefOf uSq) p (cost p one2)) ∧
      ∀ i, |∑ a : Fin 1 × Fin n, x a i - ∑ _a : Fin 1 × Fin n, one2 i| ≤ C :=
  exists_approxEquilibrium_replica (T := Fin 1) (u := fun _ => uSq) (ω := fun _ => one2)
    (fun _ => continuous_uSq) (fun _ => stronglyMonotone_uSq) (fun _ _ => by simp [one2])

open Continuum.ContinuumEconomy in
/-- A consumer with utility `x₀² + x₁²` has a demand only at **strictly positive
prices**: if some `pᵢ ≤ 0`, adding good `i` is free and utility is unbounded. -/
theorem positivePrices_of_mem_demand_uSq {p : Fin 2 → ℝ} {w : ℝ} {d : Fin 2 → ℝ}
    (hd : d ∈ demand (prefOf uSq) p w) : PositivePrices p := by
  classical
  intro i
  by_contra hpi
  replace hpi := not_lt.1 hpi
  obtain ⟨⟨hd0, hdw⟩, hopt⟩ := hd
  set t : ℝ := uSq d + 1 with ht
  have hu0 : 0 ≤ uSq d := by unfold uSq; positivity
  set y : Fin 2 → ℝ := d + t • Pi.single i 1 with hy
  have hy0 : 0 ≤ y := by
    intro j
    have : (0 : ℝ) ≤ (Pi.single i (1 : ℝ) : Fin 2 → ℝ) j := by
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hd0 j]
  have hcy : cost p y ≤ w := by
    rw [hy, cost_add_right, cost_smul_right, AumannExistence.cost_single]
    nlinarith
  have hyi : y i = d i + t := by simp [hy]
  have hle : y i ^ 2 ≤ uSq y := by
    unfold uSq; fin_cases i <;> simp <;> positivity
  have h1 : uSq y ≤ uSq d := hopt y ⟨hy0, hcy⟩
  have hdi : (0 : ℝ) ≤ d i := hd0 i
  have h2 : t ≤ y i := by rw [hyi]; linarith
  nlinarith

open Continuum.ContinuumEconomy in
/-- **Demand of the specialisation utility.** At wealth `p₀ + p₁` (the value of
`(1, 1)`), every demanded bundle is a corner: `(w / p₀, 0)` with `p₀ ≤ p₁`, or
`(0, w / p₁)` with `p₁ ≤ p₀`. -/
theorem mem_demand_uSq {p : Fin 2 → ℝ} {d : Fin 2 → ℝ}
    (hd : d ∈ demand (prefOf uSq) p (cost p one2)) :
    (d 1 = 0 ∧ d 0 = (p 0 + p 1) / p 0 ∧ p 0 ≤ p 1) ∨
      (d 0 = 0 ∧ d 1 = (p 0 + p 1) / p 1 ∧ p 1 ≤ p 0) := by
  have hp := positivePrices_of_mem_demand_uSq hd
  obtain ⟨⟨hd0, hdw⟩, hopt⟩ := hd
  have h0 := hp 0; have h1 := hp 1
  have hw : cost p one2 = p 0 + p 1 := by simp [cost, one2, Fin.sum_univ_two]
  have hc : cost p d = p 0 * d 0 + p 1 * d 1 := by simp [cost, Fin.sum_univ_two]
  rw [hw] at hdw hopt
  rw [hc] at hdw
  set a := (p 0 + p 1) / p 0 with ha
  set b := (p 0 + p 1) / p 1 with hb
  have hpa : p 0 * a = p 0 + p 1 := by rw [ha]; field_simp
  have hpb : p 1 * b = p 0 + p 1 := by rw [hb]; field_simp
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hA := hopt ![a, 0] ⟨fun j => by fin_cases j <;> simp [ha0.le],
    by simp [cost, Fin.sum_univ_two]; linarith⟩
  have hB := hopt ![0, b] ⟨fun j => by fin_cases j <;> simp [hb0.le],
    by simp [cost, Fin.sum_univ_two]; linarith⟩
  change uSq ![a, 0] ≤ uSq d at hA
  change uSq ![0, b] ≤ uSq d at hB
  simp only [uSq, Matrix.cons_val_zero, Matrix.cons_val_one] at hA hB
  norm_num at hA hB
  have hx0 : (0 : ℝ) ≤ d 0 := hd0 0
  have hx1 : (0 : ℝ) ≤ d 1 := hd0 1
  -- coordinates in units of the corners
  have hda : d 0 ≤ a := by
    rw [ha, le_div_iff₀ h0]; nlinarith
  have hdb : d 1 ≤ b := by
    rw [hb, le_div_iff₀ h1]; nlinarith
  -- `d₀ / a + d₁ / b ≤ 1`
  have hsum : d 0 * b + d 1 * a ≤ a * b := by
    have e1 : p 0 * p 1 * (d 0 * b + d 1 * a) = (p 0 + p 1) * (p 0 * d 0 + p 1 * d 1) := by
      linear_combination (d 0 * p 0) * hpb + (d 1 * p 1) * hpa
    have e2 : p 0 * p 1 * (a * b) = (p 0 + p 1) * (p 0 + p 1) := by
      linear_combination (p 1 * b) * hpa + (p 0 + p 1) * hpb
    have hpp : 0 < p 0 * p 1 := mul_pos h0 h1
    have : p 0 * p 1 * (d 0 * b + d 1 * a) ≤ p 0 * p 1 * (a * b) := by
      rw [e1, e2]; exact mul_le_mul_of_nonneg_left hdw (by linarith)
    exact le_of_mul_le_mul_left this hpp
  by_cases hd1 : d 1 = 0
  · left
    rw [hd1] at hA hB
    norm_num at hA hB
    refine ⟨hd1, ?_, ?_⟩
    · nlinarith
    · have hab : b ≤ a := by nlinarith
      rw [ha, hb] at hab
      rw [div_le_div_iff_of_pos_left (by linarith) h1 h0] at hab
      exact hab
  by_cases hd0' : d 0 = 0
  · right
    rw [hd0'] at hA hB
    norm_num at hA hB
    refine ⟨hd0', ?_, ?_⟩
    · nlinarith
    · have hab : a ≤ b := by nlinarith
      rw [ha, hb] at hab
      rw [div_le_div_iff_of_pos_left (by linarith) h0 h1] at hab
      exact hab
  · exfalso
    have hpos0 : 0 < d 0 := lt_of_le_of_ne hx0 (Ne.symm hd0')
    have hpos1 : 0 < d 1 := lt_of_le_of_ne hx1 (Ne.symm hd1)
    -- `d₀² < d₀ a` and `d₁² < d₁ b` unless at a corner
    have hlt0 : d 0 < a := by
      rcases hda.lt_or_eq with h | h
      · exact h
      · exfalso; rw [h] at hsum; nlinarith
    have s0 : d 0 ^ 2 < d 0 * a := by nlinarith
    have s1 : d 1 ^ 2 ≤ d 1 * b := by nlinarith
    -- `d₀ a + d₁ b ≤ max(a², b²)` from `d₀/a + d₁/b ≤ 1`
    rcases le_total a b with hab | hab
    · have : d 0 * a + d 1 * b ≤ b ^ 2 := by nlinarith
      nlinarith
    · have : d 0 * a + d 1 * b ≤ a ^ 2 := by nlinarith
      nlinarith

open Continuum.ContinuumEconomy in
/-- ... but **exact** equilibria fail for every **odd** number of agents, at any
prices: demand exists only at positive prices; at `p₀ ≠ p₁` every agent
demands the same corner, so one good is not consumed at all, and at `p₀ = p₁`
every agent consumes `0` or `2` units of good `0`, whose total is even and
cannot be `n`. -/
theorem sqReplica_odd_no_equilibrium {n : ℕ} (hn : Odd n) (p : Fin 2 → ℝ)
    (x : Fin 1 × Fin n → Fin 2 → ℝ) (hx : ∀ a, x a ∈ demand (prefOf uSq) p (cost p one2)) :
    ∑ a, x a ≠ ∑ _a : Fin 1 × Fin n, one2 := by
  classical
  intro h
  have hn0 : 0 < n := hn.pos
  have hsum : ∀ i, ∑ a, x a i = n := fun i => by
    have := congrFun h i
    simpa [Finset.sum_apply, one2] using this
  obtain ⟨a₀⟩ : Nonempty (Fin 1 × Fin n) := ⟨(0, ⟨0, hn0⟩)⟩
  have hp := positivePrices_of_mem_demand_uSq (hx a₀)
  have h0 := hp 0; have h1 := hp 1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rcases lt_trichotomy (p 0) (p 1) with hlt | heq | hgt
  · -- every agent at the corner `(w/p₀, 0)`
    have : ∀ a, x a 1 = 0 := fun a => by
      rcases mem_demand_uSq (hx a) with h' | h'
      · exact h'.1
      · exact absurd h'.2.2 (not_le.2 hlt)
    have := hsum 1
    simp only [*, Finset.sum_const_zero] at this
    linarith
  · -- every agent consumes `0` or `2` of good `0`
    have hval : ∀ a, x a 0 = 2 * (if x a 1 = 0 then 1 else 0 : ℕ) := fun a => by
      rcases mem_demand_uSq (hx a) with h' | h'
      · rw [ite_eq_left h'.1, h'.2.1, ← heq]; field_simp; norm_num
      · have hne : x a 1 ≠ 0 := by
          rw [h'.2.1, ← heq]; field_simp; norm_num
        rw [ite_eq_right hne, h'.1]; norm_num
    have h' := hsum 0
    simp only [hval] at h'
    rw [← Finset.mul_sum] at h'
    have hcast : (n : ℝ) = ((2 * ∑ a : Fin 1 × Fin n, (if x a 1 = 0 then 1 else 0 : ℕ) : ℕ) : ℝ) := by
      push_cast at h' ⊢; linarith
    have hnat : n = 2 * ∑ a : Fin 1 × Fin n, (if x a 1 = 0 then 1 else 0 : ℕ) := by exact_mod_cast hcast
    exact Nat.not_even_iff_odd.2 hn ⟨_, by rw [hnat]; ring⟩
  · have : ∀ a, x a 0 = 0 := fun a => by
      rcases mem_demand_uSq (hx a) with h' | h'
      · exact absurd h'.2.2 (not_le.2 hgt)
      · exact h'.1
    have := hsum 0
    simp only [*, Finset.sum_const_zero] at this
    linarith

end ApproxEquilibrium

end Econ
