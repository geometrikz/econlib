/-
# Replica economies and equal treatment in the core (Debreu–Scarf)

PLAN.md §1 (M4). MWG §18.B (the replica economy and its equal-treatment
proposition; the limit theorem is the next proposition there); Debreu & Scarf (1963).

The `r`-fold **replica** of an economy with consumer types `I` has `r`
identical copies of every type: consumer `(i, q)` (`q < r`) has type `i`'s
utility `uᵢ` and endowment `ωᵢ`.

**Equal treatment** (`replica_inCore_equalTreatment`): if every `uᵢ` is
continuous, strictly quasiconcave and strongly monotone, every core allocation
of the replica gives all consumers of the same type the same bundle.

Proof (MWG 18.B.3). Suppose consumers of type `i₀` are treated unequally. In
each type pick a worst-off member and form the coalition of these `|I|`
consumers. Give each the average bundle `x̄ᵢ` of its type. This is feasible for
the coalition (feasibility of the whole allocation averages to it). By
quasiconcavity everyone weakly gains; by strict quasiconcavity type `i₀`
strictly gains. Take a `θ`-fraction of `x̄ᵢ₀` and split it equally among all
`|I|` members: for small `θ` type `i₀` still strictly gains (continuity), and
the others now strictly gain (strong monotonicity; `x̄ᵢ₀ ≠ 0` because its
members are nonnegative and not all equal). So the coalition blocks.

Strict convexity is needed: `linear_replica_unequal_core` is a core allocation
of a replica with linear utilities that treats two identical consumers
differently. Content starts at `r ≥ 2` (`r ≤ 1` is trivial). Continuity is
assumed on all of `ℝ^ι` for convenience; only the orthant is used.

This is the first step of the Debreu–Scarf core convergence theorem; the limit
statement (allocations in the core of every replica are Walrasian) is
`walrasian_of_mem_core_replicas` in `GE/DebreuScarf.lean`.
-/
module

public import EconLean.GE.ExistenceRegular

@[expose] public section

namespace Econ

open Finset Filter Topology

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι]

/-- The **`r`-fold replica** of the economy with type utilities `u` and type
endowments `ω`. -/
def replica (u : I → (ι → ℝ) → ℝ) (ω : I → ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (r : ℕ) :
    ExchangeEconomy (I × Fin r) ι where
  pref a := prefOf (u a.1)
  endow a := ω a.1
  endow_nonneg a := hω a.1

omit [Fintype ι] in
/-- Upper level sets of a strictly quasiconcave utility, intersected with the
orthant, are convex. -/
theorem StrictlyQuasiconcave.convex_upper {u : (ι → ℝ) → ℝ} (hsq : StrictlyQuasiconcave u)
    (m : ℝ) : Convex ℝ {y : ι → ℝ | 0 ≤ y ∧ m ≤ u y} := by
  intro y hy z hz a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg ha (hy.1 k)) (mul_nonneg hb (hz.1 k))
  · rcases ha.eq_or_lt with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      subst ha0; subst hb1; simpa using hz.2
    rcases hb.eq_or_lt with hb0 | hb0
    · have ha1 : a = 1 := by linarith
      subst hb0; subst ha1; simpa using hy.2
    by_cases hyz : y = z
    · subst hyz
      rw [← add_smul, hab, one_smul]; exact hy.2
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := hsq y z hy.1 hz.1 hyz a ha0 (by linarith)
    exact le_trans (le_min hy.2 hz.2) this.le

section EqualTreatment

variable {u : I → (ι → ℝ) → ℝ} {ω : I → ι → ℝ} {hω : ∀ i, 0 ≤ ω i} {r : ℕ}

omit [Fintype ι] in
/-- Averages of bundles that are each at least `m` are at least `m`
(quasiconcavity, finite form). -/
theorem StrictlyQuasiconcave.le_average {v : (ι → ℝ) → ℝ} (hsq : StrictlyQuasiconcave v)
    {J : Type*} (s : Finset J) (hs : s.Nonempty) (z : J → ι → ℝ) (hz : ∀ j ∈ s, 0 ≤ z j)
    {m : ℝ} (hm : ∀ j ∈ s, m ≤ v (z j)) :
    0 ≤ (s.card : ℝ)⁻¹ • ∑ j ∈ s, z j ∧ m ≤ v ((s.card : ℝ)⁻¹ • ∑ j ∈ s, z j) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have := (hsq.convex_upper m).sum_mem (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.2 hc.le) (by simp [hc.ne']) (fun j hj => ⟨hz j hj, hm j hj⟩)
  rwa [← smul_sum] at this

omit [Fintype ι] in
/-- **Strict form**: if the bundles are not all equal, the average is strictly
better than the worst of them. -/
theorem StrictlyQuasiconcave.lt_average {v : (ι → ℝ) → ℝ} (hsq : StrictlyQuasiconcave v)
    {J : Type*} [DecidableEq J] (s : Finset J) (z : J → ι → ℝ) (hz : ∀ j ∈ s, 0 ≤ z j)
    {m : ℝ} (hm : ∀ j ∈ s, m ≤ v (z j)) (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    m < v ((s.card : ℝ)⁻¹ • ∑ j ∈ s, z j) := by
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  set A := (s.card : ℝ)⁻¹ • ∑ j ∈ s, z j with hA
  obtain ⟨j1, hj1, hj1A⟩ : ∃ j1 ∈ s, z j1 ≠ A := by
    by_contra h
    push Not at h
    exact hjk ((h j hj).trans (h k hk).symm)
  have hs2 : 1 < s.card := by
    by_contra h
    push Not at h
    have := Finset.card_le_one.1 h j hj k hk
    exact hjk (this ▸ rfl)
  set s' := s.erase j1 with hs'
  have hs'ne : s'.Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hj1]; omega
  have hcard' : (s'.card : ℝ) = s.card - 1 := by
    rw [Finset.card_erase_of_mem hj1, Nat.cast_sub (by omega)]; simp
  have hn : (2 : ℝ) ≤ s.card := by exact_mod_cast hs2
  set B := (s'.card : ℝ)⁻¹ • ∑ j ∈ s', z j with hB
  obtain ⟨hB0, hBm⟩ := hsq.le_average s' hs'ne z (fun j hj => hz j (Finset.mem_of_mem_erase hj))
    (fun j hj => hm j (Finset.mem_of_mem_erase hj))
  set t : ℝ := (s.card : ℝ)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 (by linarith)
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hsplit : A = t • z j1 + (1 - t) • B := by
    have hsum : ∑ j ∈ s, z j = z j1 + ∑ j ∈ s', z j := (add_sum_erase s z hj1).symm
    rw [hA, hB, hsum, hcard', smul_smul, smul_add]
    congr 1
    congr 1
    rw [ht]; field_simp
    rw [div_self (by linarith)]
  have hB1 : z j1 ≠ B := by
    intro h
    apply hj1A
    rw [hsplit, ← h, ← add_smul]; simp
  have := hsq (z j1) B (hz j1 hj1) hB0 hB1 t ht0 ht1
  rw [← hsplit] at this
  exact lt_of_le_of_lt (le_min (hm j1 hj1) hBm) this

omit [Fintype ι] in
theorem P_prefOf_of_lt {v : (ι → ℝ) → ℝ} {a b : ι → ℝ} (h : v b < v a) : P (prefOf v) a b :=
  ⟨h.le, not_le.2 h⟩

omit [Fintype ι] in
theorem lt_of_P_prefOf {v : (ι → ℝ) → ℝ} {a b : ι → ℝ} (h : P (prefOf v) a b) : v b < v a :=
  lt_of_not_ge h.2

/-- **Equal treatment in the core of a replica economy** (MWG §18.B,
Debreu–Scarf). With continuous, strictly quasiconcave, strongly monotone
utilities, every core allocation of the `r`-replica gives all consumers of the
same type the same bundle. -/
theorem replica_inCore_equalTreatment (hu : ∀ i, Continuous (u i))
    (hsq : ∀ i, StrictlyQuasiconcave (u i)) (hmono : ∀ i, StronglyMonotone (prefOf (u i)))
    {x : Allocation (I × Fin r) ι} (hx : (replica u ω hω r).InCore x) (i : I) (q q' : Fin r) :
    x (i, q) = x (i, q') := by
  by_contra hne
  obtain ⟨hfeas, hblock⟩ := hx
  have hx0 : ∀ a, 0 ≤ x a := hfeas.1
  have : Nonempty (Fin r) := ⟨q⟩
  have : Nonempty I := ⟨i⟩
  have hr : (0 : ℝ) < r := by exact_mod_cast Fin.pos q
  have hcard : ((univ : Finset (Fin r)).card : ℝ) = r := by simp
  choose qmin hqmin using fun j : I =>
    exists_min_image univ (fun q => u j (x (j, q))) univ_nonempty
  set xbar : I → ι → ℝ := fun j => ((univ : Finset (Fin r)).card : ℝ)⁻¹ • ∑ q, x (j, q)
    with hxbar
  have hbar : ∀ j, 0 ≤ xbar j ∧ u j (x (j, qmin j)) ≤ u j (xbar j) := fun j =>
    (hsq j).le_average univ univ_nonempty (fun q => x (j, q)) (fun _ _ => hx0 _)
      (fun q _ => (hqmin j).2 q (mem_univ q))
  have hstrict : u i (x (i, qmin i)) < u i (xbar i) :=
    (hsq i).lt_average univ (fun q => x (i, q)) (fun _ _ => hx0 _)
      (fun q _ => (hqmin i).2 q (mem_univ q)) ⟨q, mem_univ q, q', mem_univ q', hne⟩
  have hbar_ne : xbar i ≠ 0 := by
    intro h0
    have hsum0 : ∑ q, x (i, q) = 0 := by
      have h1 : ((univ : Finset (Fin r)).card : ℝ)⁻¹ • ∑ q, x (i, q) = 0 := h0
      rw [hcard] at h1
      exact (smul_eq_zero.1 h1).resolve_left (inv_ne_zero hr.ne')
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hx0 (i, q))).1 hsum0
    exact hne ((hall q (mem_univ q)).trans (hall q' (mem_univ q')).symm)
  set n : ℝ := (Fintype.card I : ℝ) with hn_def
  have hn : 1 ≤ n := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.2 ⟨i⟩
    rw [hn_def]; exact_mod_cast this
  set c : ℝ → ℝ := fun θ => 1 + θ / n - θ with hc
  have hcont : Continuous fun θ => u i (c θ • xbar i) := (hu i).comp (by fun_prop)
  have hc0 : u i (c 0 • xbar i) = u i (xbar i) := by simp [hc]
  obtain ⟨θ, hθu, hθ0, hθ1⟩ : ∃ θ, u i (x (i, qmin i)) < u i (c θ • xbar i) ∧ 0 < θ ∧ θ < 1 := by
    have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), u i (x (i, qmin i)) < u i (c θ • xbar i) :=
      (hcont.tendsto 0).eventually (lt_mem_nhds (by rw [hc0]; exact hstrict))
    obtain ⟨θ, h1, h2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos))).exists
    exact ⟨θ, h1, h2.1, h2.2⟩
  have hcθ : 0 < c θ := by
    have : θ / n ≥ 0 := div_nonneg hθ0.le (by linarith)
    simp only [hc]; linarith
  set y : I → ι → ℝ := fun j => xbar j + (θ / n) • xbar i - if j = i then θ • xbar i else 0
    with hy
  have hyi : y i = c θ • xbar i := by
    simp only [hy, ↓reduceIte, hc, add_smul, sub_smul, one_smul]
  have hyj : ∀ j, j ≠ i → y j = xbar j + (θ / n) • xbar i := fun j hj => by
    simp [hy, hj]
  have hshare : 0 ≤ (θ / n) • xbar i :=
    smul_nonneg (div_nonneg hθ0.le (by linarith)) (hbar i).1
  have hy0 : ∀ j, 0 ≤ y j := fun j => by
    by_cases hj : j = i
    · subst hj; rw [hyi]; exact smul_nonneg hcθ.le (hbar j).1
    · rw [hyj j hj]; exact add_nonneg (hbar j).1 hshare
  -- Feasibility for the coalition.
  have hxsum : ∑ j, xbar j = ∑ j, ω j := by
    have htot : ∑ a, x a = ∑ a : I × Fin r, ω a.1 := hfeas.2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at htot
    simp only [sum_const, card_univ, Fintype.card_fin] at htot
    have h1 : ∑ j, xbar j = (r : ℝ)⁻¹ • ∑ j, ∑ q, x (j, q) := by
      simp only [hxbar, hcard, smul_sum]
    rw [h1, htot, ← smul_sum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hr.ne',
      one_smul]
  have hysum : ∑ j, y j = ∑ j, ω j := by
    simp only [hy, sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const,
      card_univ]
    rw [hxsum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← hn_def,
      mul_div_cancel₀ _ (by linarith : n ≠ 0)]
    abel
  -- The blocking coalition: one worst-off member of each type.
  have hinj : Function.Injective fun j : I => (j, qmin j) := fun j k h => congrArg Prod.fst h
  apply hblock (univ.image fun j => (j, qmin j))
  refine ⟨univ_nonempty.image _, fun a => y a.1, fun a _ => hy0 a.1, ?_, ?_⟩
  · simp only [sum_image (fun j _ k _ h => hinj h)]
    simpa [replica] using hysum
  · intro a ha
    obtain ⟨j, -, rfl⟩ := mem_image.1 ha
    show P (prefOf (u j)) (y j) (x (j, qmin j))
    by_cases hj : j = i
    · subst hj; rw [hyi]; exact P_prefOf_of_lt hθu
    · rw [hyj j hj]
      have hle : xbar j ≤ xbar j + (θ / n) • xbar i := le_add_of_nonneg_right hshare
      have hne' : xbar j ≠ xbar j + (θ / n) • xbar i := by
        intro h
        have : (θ / n) • xbar i = 0 := by
          have := congrArg (fun v => v - xbar j) h; simpa using this.symm
        exact hbar_ne ((smul_eq_zero.1 this).resolve_left
          (div_pos hθ0 (by linarith)).ne')
      have := lt_of_P_prefOf (hmono j _ _ (hbar j).1 hle hne')
      exact P_prefOf_of_lt (lt_of_le_of_lt (hbar j).2 this)

end EqualTreatment


namespace GEExamples

/-- Type endowments for the witness: type `i` owns one unit of good `i`. -/
def unitEndow (i : Fin 2) : Fin 2 → ℝ := fun k => if i = k then 1 else 0

theorem unitEndow_nonneg (i : Fin 2) : 0 ≤ unitEndow i := fun k => by
  simp only [unitEndow, Pi.zero_apply]; split_ifs <;> norm_num

/-- **Witness.** The twofold replica of the two-type square-root economy has a
core allocation (a Walrasian one), and by equal treatment it treats both
copies of each type alike. -/
theorem replica_sqrt_core_equalTreatment :
    ∃ x : Allocation (Fin 2 × Fin 2) (Fin 2),
      (replica (fun _ => uSqrt) unitEndow unitEndow_nonneg 2).InCore x ∧
      ∀ i q q', x (i, q) = x (i, q') := by
  obtain ⟨p, x, -, heq⟩ :=
    (replica (fun _ => uSqrt) unitEndow unitEndow_nonneg 2).exists_walrasianEquilibrium_of_preferences_of_totalEndowment
      (u := fun _ => uSqrt) (fun _ => rfl) (fun _ => continuous_uSqrt)
      (fun _ => strictlyQuasiconcave_uSqrt) (fun _ => stronglyMonotone_uSqrt) (fun k => by
        simp only [ExchangeEconomy.totalEndowment, replica, Finset.sum_apply]
        rw [Fintype.sum_prod_type]
        fin_cases k <;> simp [unitEndow, Fin.sum_univ_two])
  have hcore := heq.inCore
  exact ⟨x, hcore, replica_inCore_equalTreatment (fun _ => continuous_uSqrt)
    (fun _ => strictlyQuasiconcave_uSqrt) (fun _ => stronglyMonotone_uSqrt) hcore⟩

/-- **Strict convexity is needed.** One type with linear utility `x₀ + x₁`
owning `(1, 1)`, replicated twice. The allocation `(2, 0)`, `(0, 2)` is in the
core but treats the two identical consumers differently. -/
theorem linear_replica_unequal_core :
    (replica (fun (_ : Fin 1) (x : Fin 2 → ℝ) => x 0 + x 1) (fun _ _ => 1)
      (fun _ _ => zero_le_one) 2).InCore
      (fun a => if a.2 = 0 then ![2, 0] else ![0, 2]) ∧
    (fun a : Fin 1 × Fin 2 => if a.2 = 0 then (![2, 0] : Fin 2 → ℝ) else ![0, 2]) (0, 0) ≠
      (fun a : Fin 1 × Fin 2 => if a.2 = 0 then (![2, 0] : Fin 2 → ℝ) else ![0, 2]) (0, 1) := by
  refine ⟨⟨⟨fun a => ?_, ?_⟩, fun S ⟨hS, y, _, hsum, hbetter⟩ => ?_⟩, ?_⟩
  · intro k; dsimp only; split_ifs <;> fin_cases k <;> simp
  · funext k
    simp only [ExchangeEconomy.totalEndowment, replica, Finset.sum_apply]
    rw [Fintype.sum_prod_type]
    fin_cases k <;> simp [Fin.sum_univ_two]
  · have hval : ∀ a : Fin 1 × Fin 2,
        ((if a.2 = 0 then ![2, 0] else ![0, 2] : Fin 2 → ℝ) 0 +
          (if a.2 = 0 then ![2, 0] else ![0, 2] : Fin 2 → ℝ) 1) = 2 := fun a => by
      split_ifs <;> norm_num
    have hlt : ∑ a ∈ S, (2 : ℝ) < ∑ a ∈ S, (y a 0 + y a 1) :=
      Finset.sum_lt_sum_of_nonempty hS fun a ha => by
        have := lt_of_P_prefOf (hbetter a ha)
        have h2 := hval a
        simp only at this
        linarith
    have h0 := congrFun hsum 0
    have h1 := congrFun hsum 1
    simp only [Finset.sum_apply, replica] at h0 h1
    rw [Finset.sum_add_distrib, h0, h1] at hlt
    simp only [Finset.sum_const, nsmul_eq_mul] at hlt
    linarith
  · simp

end GEExamples

end Econ
