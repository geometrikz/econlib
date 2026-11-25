/-
# Debreu–Scarf: allocations in the core of every replica are Walrasian

PLAN.md §1 (M4). MWG §18.B (the core convergence proposition after equal
treatment); Debreu & Scarf (1963).

Let `x*` assign bundle `x*ᵢ` to each type `i`. If the replicated allocation
(every copy of type `i` gets `x*ᵢ`) is in the core of the `r`-replica for
**every** `r ≥ 1`, then `x*` is a Walrasian equilibrium allocation: there are
prices `p ≥ 0`, `p ≠ 0`, at which every `x*ᵢ` is in type `i`'s demand at
wealth `p · ωᵢ` (`walrasian_of_mem_core_replicas`). Together with equal
treatment (`GE/Replica.lean`) this is the Debreu–Scarf core convergence
theorem: the only allocations that survive in the core of arbitrarily large
replicas are Walrasian.

Proof (MWG 18.B).
1. Let `Sᵢ = {x − ωᵢ : x ≥ 0, x ≻ᵢ x*ᵢ}` (convex) and let `V` be the set of
   convex combinations `∑ᵢ aᵢ zᵢ` with `zᵢ ∈ Sᵢ`. `V` is convex.
2. `0 ∉ V`. Otherwise `∑ aᵢ zᵢ = 0`. For large `r` put `kᵢ = ⌈aᵢ r⌉` copies of
   type `i` into a coalition of the `r`-replica and give each
   `ωᵢ + tᵢ zᵢ` with `tᵢ = aᵢ r / kᵢ → 1`. By continuity these bundles are
   still strictly preferred to `x*ᵢ`, and `∑ᵢ kᵢ tᵢ zᵢ = r ∑ᵢ aᵢ zᵢ = 0`, so the
   coalition blocks.
3. Separate `0` from `V`: `p ≠ 0` with `p · v ≥ 0` on `V`. So `x ≻ᵢ x*ᵢ`
   implies `p · x ≥ p · ωᵢ`. Strong monotonicity and feasibility give
   `p · x*ᵢ = p · ωᵢ` and `p ≥ 0`; with `ωᵢ ≫ 0` wealth is positive and the
   usual cheaper-point argument puts `x*ᵢ` in demand.

Hypotheses: continuous, strictly quasiconcave, strongly monotone utilities and
strictly positive type endowments, as in MWG. Strict convexity is needed only
for equal treatment, which justifies restricting to allocations that treat
copies alike; for such allocations the proof uses only convexity of the
improving-trade sets. Continuity is assumed on all of `ℝ^ι` for convenience;
only the orthant is used. `mem_core_replicas_iff_walrasian` packages both
directions.
-/
module

public import EconLean.GE.Replica
public import EconLean.Foundations.SupportingHyperplane

@[expose] public section

namespace Econ

open Finset Filter Topology

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι]

/-! ### Rational approximation -/

/-- `a r / ⌈a r⌉ → 1` for `a > 0`. -/
theorem tendsto_div_ceil (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℕ => a * r / ⌈a * r⌉₊) atTop (𝓝 1) := by
  have hlow : Tendsto (fun r : ℕ => 1 - 1 / (a * r + 1)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℕ => a * (r : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1
        (Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop)
    have h3 : Tendsto (fun r : ℕ => 1 / (a * r + 1)) atTop (𝓝 0) := by
      simp only [one_div]; exact h1.inv_tendsto_atTop
    simpa using h3.const_sub (1 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with r hr
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have har : 0 < a * r := by positivity
    have hc : (⌈a * r⌉₊ : ℝ) < a * r + 1 := Nat.ceil_lt_add_one har.le
    have hc0 : 0 < (⌈a * r⌉₊ : ℝ) := lt_of_lt_of_le har (Nat.le_ceil _)
    rw [le_div_iff₀ hc0]
    have : 1 - 1 / (a * r + 1) = a * r / (a * r + 1) := by field_simp; ring
    rw [this, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with r hr
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have har : 0 < a * r := by positivity
    have hc0 : 0 < (⌈a * r⌉₊ : ℝ) := lt_of_lt_of_le har (Nat.le_ceil _)
    rw [div_le_one hc0]
    exact Nat.le_ceil _


omit [Fintype I] [DecidableEq I] [Fintype ι] in
/-- Strict upper level sets of a strictly quasiconcave utility in the orthant
are convex. -/
theorem StrictlyQuasiconcave.convex_strictUpper {v : (ι → ℝ) → ℝ}
    (hsq : StrictlyQuasiconcave v) (m : ℝ) : Convex ℝ {y : ι → ℝ | 0 ≤ y ∧ m < v y} := by
  intro y hy z hz a b ha hb hab
  refine ⟨fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
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
    exact lt_of_lt_of_le (lt_min hy.2 hz.2) this.le

/-- The set `Sᵢ = {x − ωᵢ : x ≥ 0, uᵢ(x) > uᵢ(x*ᵢ)}` of net trades type `i`
strictly prefers. -/
def betterTrades (v : (ι → ℝ) → ℝ) (w xs : ι → ℝ) : Set (ι → ℝ) :=
  {z | 0 ≤ z + w ∧ v xs < v (z + w)}

omit [Fintype ι] in
theorem convex_betterTrades {v : (ι → ℝ) → ℝ} (hsq : StrictlyQuasiconcave v) (w xs : ι → ℝ) :
    Convex ℝ (betterTrades v w xs) := by
  have := (hsq.convex_strictUpper (v xs)).translate_preimage_right w
  convert this using 1
  ext z; simp [betterTrades, add_comm]

/-- Convex combinations `∑ᵢ aᵢ zᵢ` with one net trade `zᵢ` from each `Sᵢ`. -/
def mixedTrades (S : I → Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | ∃ a : I → ℝ, ∃ z : I → ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧ (∀ i, z i ∈ S i) ∧
    v = ∑ i, a i • z i}

omit [DecidableEq I] [Fintype ι] in
theorem convex_mixedTrades {S : I → Set (ι → ℝ)} (hS : ∀ i, Convex ℝ (S i))
    (hne : ∀ i, (S i).Nonempty) : Convex ℝ (mixedTrades S) := by
  rintro _ ⟨a, z, ha0, ha1, hz, rfl⟩ _ ⟨b, z', hb0, hb1, hz', rfl⟩ s t hs ht hst
  set c : I → ℝ := fun i => s * a i + t * b i with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => add_nonneg (mul_nonneg hs (ha0 i)) (mul_nonneg ht (hb0 i))
  let w : I → ι → ℝ := fun i =>
    if c i = 0 then (hne i).some else ((c i)⁻¹ * (s * a i)) • z i + ((c i)⁻¹ * (t * b i)) • z' i
  refine ⟨c, w, hc0, ?_, fun i => ?_, ?_⟩
  · simp only [hc, sum_add_distrib, ← mul_sum, ha1, hb1, mul_one, hst]
  · by_cases h : c i = 0
    · simp only [w, h, ↓reduceIte]; exact (hne i).some_mem
    · simp only [w, h, ↓reduceIte]
      refine hS i (hz i) (hz' i) (mul_nonneg (inv_nonneg.2 (hc0 i)) (mul_nonneg hs (ha0 i)))
        (mul_nonneg (inv_nonneg.2 (hc0 i)) (mul_nonneg ht (hb0 i))) ?_
      rw [← mul_add]; exact inv_mul_cancel₀ h
  · simp only [smul_sum, smul_smul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : c i = 0
    · have h1 : s * a i = 0 := by
        have := mul_nonneg hs (ha0 i); have := mul_nonneg ht (hb0 i); simp only [hc] at h; linarith
      have h2 : t * b i = 0 := by
        have := mul_nonneg hs (ha0 i); have := mul_nonneg ht (hb0 i); simp only [hc] at h; linarith
      simp [h, h1, h2]
    · simp only [w, h, ↓reduceIte, smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ h, one_mul]


omit [Fintype I] [DecidableEq I] in
/-- Strong monotonicity makes every good costly: if some bundle is demanded at
prices `p ≥ 0`, then `p ≫ 0` (a free good would be added for nothing). -/
theorem positivePrices_of_mem_demand [DecidableEq ι] {v : (ι → ℝ) → ℝ}
    (hmono : StronglyMonotone (prefOf v)) {p x : ι → ℝ} {w : ℝ} (hp : 0 ≤ p)
    (hx : x ∈ demand (prefOf v) p w) : PositivePrices p := by
  intro k
  refine lt_of_le_of_ne (hp k) fun h0 => ?_
  have hle : x ≤ x + Pi.single k 1 := le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one)
  have hne : x ≠ x + Pi.single k 1 := fun h => by
    have := congrFun (add_eq_left.1 h.symm) k
    simp at this
  have hlt := lt_of_P_prefOf (hmono x _ hx.1.1 hle hne)
  have hc : cost p (x + Pi.single k 1) = cost p x := by
    simp [cost, mul_add, sum_add_distrib, Pi.single_apply, ← h0]
  have := hx.2 _ ⟨add_nonneg hx.1.1 (Pi.single_nonneg.2 zero_le_one), hc ▸ hx.1.2⟩
  exact absurd this (not_le.2 hlt)

section CoreLimit

variable {u : I → (ι → ℝ) → ℝ} {ω : I → ι → ℝ} {hω : ∀ i, 0 ≤ ω i}

omit [DecidableEq I] [Fintype ι] in
/-- **Step 2: no convex combination of improving trades is zero.** If the
replicated allocation is in the core of every replica, `0 ∉ V`. -/
theorem zero_notMem_mixedTrades (hu : ∀ i, Continuous (u i)) {xs : I → ι → ℝ}
    (hcore : ∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) :
    (0 : ι → ℝ) ∉ mixedTrades fun i => betterTrades (u i) (ω i) (xs i) := by
  rintro ⟨a, z, ha0, ha1, hz, h0⟩
  set T : I → ℕ → ℝ := fun i r => a i * r / ⌈a i * r⌉₊ with hT
  have hev : ∀ i, ∀ᶠ r : ℕ in atTop, 0 < a i → u i (xs i) < u i (ω i + T i r • z i) := by
    intro i
    by_cases hai : 0 < a i
    · have ht := tendsto_div_ceil (a i) hai
      have hc : Tendsto (fun r => u i (ω i + T i r • z i)) atTop
          (𝓝 (u i (ω i + (1 : ℝ) • z i))) :=
        ((hu i).tendsto _).comp (tendsto_const_nhds.add (ht.smul_const (z i)))
      rw [one_smul, add_comm] at hc
      filter_upwards [hc.eventually (lt_mem_nhds (hz i).2)] with r hr _
      exact hr
    · exact Eventually.of_forall fun r h => absurd h hai
  obtain ⟨r, hr1, hP⟩ := ((eventually_ge_atTop 1).and (eventually_all.2 hev)).exists
  have hr : 0 < r := hr1
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set k : I → ℕ := fun i => ⌈a i * r⌉₊ with hk
  have hale : ∀ i, a i ≤ 1 := fun i => ha1 ▸ single_le_sum (fun j _ => ha0 j) (mem_univ i)
  have hkr : ∀ i, k i ≤ r := fun i => Nat.ceil_le.2 (by
    have := hale i; have := ha0 i; nlinarith)
  have hkpos : ∀ i, 0 < k i → 0 < a i := fun i h => by
    by_contra hn
    have : a i = 0 := le_antisymm (not_lt.1 hn) (ha0 i)
    simp [hk, this] at h
  have hkT : ∀ i, (k i : ℝ) * T i r = a i * r := fun i => by
    by_cases h : k i = 0
    · have h1 : a i * r ≤ 0 := Nat.ceil_eq_zero.1 h
      have : a i = 0 := by
        have := ha0 i
        by_contra hne
        have : 0 < a i := lt_of_le_of_ne this (Ne.symm hne)
        nlinarith
      simp [this, hT]
    · have hk0 : (k i : ℝ) ≠ 0 := by exact_mod_cast h
      have hki : (k i : ℝ) = (⌈a i * r⌉₊ : ℝ) := rfl
      simp only [hT]
      rw [← hki]; field_simp
  have hT01 : ∀ i, 0 ≤ T i r ∧ T i r ≤ 1 := fun i =>
    ⟨div_nonneg (mul_nonneg (ha0 i) hrR.le) (Nat.cast_nonneg _),
      div_le_one_of_le₀ (Nat.le_ceil _) (Nat.cast_nonneg _)⟩
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have : ∑ i, a i ≤ 0 := sum_nonpos fun i _ => hn i
    linarith
  apply (hcore r hr).2 (univ.filter fun b : I × Fin r => b.2.val < k b.1)
  refine ⟨⟨(i0, ⟨0, hr⟩), ?_⟩, fun b => ω b.1 + T b.1 r • z b.1, fun b _ => ?_, ?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and]
    exact Nat.ceil_pos.2 (mul_pos hi0 hrR)
  · have h1 := (hz b.1).1
    have h2 := hω b.1
    have hid : ω b.1 + T b.1 r • z b.1 = (1 - T b.1 r) • ω b.1 + T b.1 r • (z b.1 + ω b.1) := by
      module
    show 0 ≤ ω b.1 + T b.1 r • z b.1
    rw [hid]
    exact add_nonneg (smul_nonneg (by linarith [(hT01 b.1).2]) h2) (smul_nonneg (hT01 b.1).1 h1)
  · show ∑ b ∈ univ.filter (fun b : I × Fin r => b.2.val < k b.1), (ω b.1 + T b.1 r • z b.1) =
      ∑ b ∈ univ.filter (fun b : I × Fin r => b.2.val < k b.1), ω b.1
    rw [sum_add_distrib, add_eq_left]
    calc ∑ b ∈ univ.filter (fun b : I × Fin r => b.2.val < k b.1), T b.1 r • z b.1
        = ∑ i, (k i : ℝ) • (T i r • z i) := by
          rw [sum_filter, Fintype.sum_prod_type]
          refine sum_congr rfl fun i _ => ?_
          rw [← sum_filter]
          simp only
          rw [sum_const, Fin.card_filter_val_lt, min_eq_right (hkr i), Nat.cast_smul_eq_nsmul]
      _ = (r : ℝ) • ∑ i, a i • z i := by
          rw [smul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [smul_smul, hkT, smul_smul, mul_comm]
      _ = 0 := by rw [← h0, smul_zero]
  · intro b hb
    have hb' := (mem_filter.1 hb).2
    exact P_prefOf_of_lt (hP b.1 (hkpos _ (by omega)))

/-- **Debreu–Scarf core convergence** (MWG §18.B). Suppose every type has a
continuous, strictly quasiconcave, strongly monotone utility and a strictly
positive endowment. If the allocation giving each copy of type `i` the bundle
`x*ᵢ` is in the core of the `r`-replica for every `r ≥ 1`, then there are
prices `p ≫ 0` at which each `x*ᵢ` is utility-maximizing in type `i`'s budget
set at wealth `p · ωᵢ`. -/
theorem walrasian_of_mem_core_replicas [Nonempty I] [Nonempty ι] (hu : ∀ i, Continuous (u i))
    (hsq : ∀ i, StrictlyQuasiconcave (u i)) (hmono : ∀ i, StronglyMonotone (prefOf (u i)))
    (hωpos : ∀ i, PositivePrices (ω i)) {xs : I → ι → ℝ}
    (hcore : ∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) :
    ∃ p : ι → ℝ, PositivePrices p ∧ ∀ i, xs i ∈ demand (prefOf (u i)) p (cost p (ω i)) := by
  classical
  suffices h : ∃ p : ι → ℝ, 0 ≤ p ∧ ∀ i, xs i ∈ demand (prefOf (u i)) p (cost p (ω i)) by
    obtain ⟨p, hp, hd⟩ := h
    obtain ⟨i1⟩ := ‹Nonempty I›
    exact ⟨p, positivePrices_of_mem_demand (hmono i1) hp (hd i1), hd⟩
  -- Feasibility, from the 1-replica.
  have hfeas := (hcore 1 one_pos).1
  have hxs0 : ∀ i, 0 ≤ xs i := fun i => hfeas.1 (i, 0)
  have hsumx : ∑ i, xs i = ∑ i, ω i := by
    have h := hfeas.2
    simp only [ExchangeEconomy.totalEndowment, replica, Fintype.sum_prod_type,
      Fin.sum_univ_one] at h
    exact h
  -- The improving trades are nonempty: add one unit of everything.
  have hone : ∀ i, xs i + (fun _ => 1) - ω i ∈ betterTrades (u i) (ω i) (xs i) := fun i => by
    refine ⟨?_, ?_⟩
    · simp only [sub_add_cancel]
      exact add_nonneg (hxs0 i) fun _ => zero_le_one
    · simp only [sub_add_cancel]
      refine lt_of_P_prefOf (hmono i _ _ (hxs0 i) (le_add_of_nonneg_right fun _ => zero_le_one)
        fun h => ?_)
      have := congrFun (add_eq_left.1 h.symm) (Classical.arbitrary ι)
      simp at this
  have hconv := convex_mixedTrades (fun i => convex_betterTrades (hsq i) (ω i) (xs i))
    fun i => ⟨_, hone i⟩
  have h0 := zero_notMem_mixedTrades (hω := hω) hu hcore
  obtain ⟨p, hp0, hp⟩ := exists_price_support hconv fun h => h0 (interior_subset h)
  -- Anything strictly better than `x*ᵢ` costs at least `p · ωᵢ`.
  have hbetter : ∀ i x, 0 ≤ x → u i (xs i) < u i x → cost p (ω i) ≤ cost p x := by
    intro i x hx hlt
    have hmem : x - ω i ∈ mixedTrades fun i => betterTrades (u i) (ω i) (xs i) := by
      refine ⟨Pi.single i 1, fun j => if j = i then x - ω i else xs j + (fun _ => 1) - ω j,
        fun j => ?_, by simp, fun j => ?_, ?_⟩
      · by_cases h : j = i
        · subst h; simp
        · simp [h]
      · by_cases h : j = i
        · subst h; simp only [↓reduceIte]; exact ⟨by simpa using hx, by simpa using hlt⟩
        · simp only [h, ↓reduceIte]; exact hone j
      · rw [Fintype.sum_eq_single i fun j hj => by simp [hj]]
        simp
    have := hp _ hmem
    simp only [cost, Pi.zero_apply, mul_zero, sum_const_zero, Pi.sub_apply, mul_sub,
      sum_sub_distrib] at this
    simp only [cost]; linarith
  -- `p · x*ᵢ ≥ p · ωᵢ` (approach `x*ᵢ` from above).
  have hge : ∀ i, cost p (ω i) ≤ cost p (xs i) := by
    intro i
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set M : ℝ := ∑ k, |p k| + 1 with hM
    have hM0 : 0 < M := by
      have := sum_nonneg fun k (_ : k ∈ univ) => abs_nonneg (p k); linarith
    have h := hbetter i (xs i + (ε / M) • (fun _ => 1))
      (add_nonneg (hxs0 i) (smul_nonneg (by positivity) fun _ => zero_le_one))
      (lt_of_P_prefOf (hmono i _ _ (hxs0 i)
        (le_add_of_nonneg_right (smul_nonneg (by positivity) fun _ => zero_le_one)) fun h => by
          have := congrFun (add_eq_left.1 h.symm) (Classical.arbitrary ι)
          simp at this; rcases this with h | h <;> linarith))
    have hcost : cost p (xs i + (ε / M) • (fun _ => 1)) ≤ cost p (xs i) + ε := by
      simp only [cost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, mul_add,
        sum_add_distrib]
      have : ∑ k, p k * (ε / M) ≤ ε := by
        rw [← sum_mul]
        have h1 : ∑ k, p k ≤ M := by
          have := sum_le_sum fun k (_ : k ∈ univ) => le_abs_self (p k)
          linarith
        calc (∑ k, p k) * (ε / M) ≤ M * (ε / M) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = ε := by field_simp
      linarith
    linarith
  -- Feasibility forces equality.
  have heq : ∀ i, cost p (xs i) = cost p (ω i) := by
    have htot : ∑ i, cost p (xs i) = ∑ i, cost p (ω i) := by
      rw [← cost_sum, ← cost_sum, hsumx]
    have := (sum_eq_sum_iff_of_le fun i (_ : i ∈ univ) => hge i).1 htot.symm
    exact fun i => (this i (mem_univ i)).symm
  -- Prices are nonnegative.
  obtain ⟨i1⟩ := ‹Nonempty I›
  have hpnn : 0 ≤ p := by
    intro k
    have h := hbetter i1 (xs i1 + Pi.single k 1)
      (add_nonneg (hxs0 i1) (Pi.single_nonneg.2 zero_le_one))
      (lt_of_P_prefOf (hmono i1 _ _ (hxs0 i1)
        (le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one)) fun h => by
          have := congrFun (add_eq_left.1 h.symm) k
          simp at this))
    have hc : cost p (xs i1 + Pi.single k 1) = cost p (xs i1) + p k := by
      simp [cost, mul_add, sum_add_distrib, Pi.single_apply]
    rw [hc, heq] at h
    simp only [Pi.zero_apply]; linarith
  refine ⟨p, hpnn, fun i => ⟨⟨hxs0 i, (heq i).le⟩, fun y hy => ?_⟩⟩
  -- Cheaper-point argument.
  show u i y ≤ u i (xs i)
  by_contra hlt
  push Not at hlt
  have hw : 0 < cost p (ω i) := by
    obtain ⟨k, hk⟩ : ∃ k, p k ≠ 0 := by
      by_contra h; push Not at h; exact hp0 (funext h)
    have hpk : 0 < p k := lt_of_le_of_ne (hpnn k) (Ne.symm hk)
    exact sum_pos' (fun j _ => mul_nonneg (hpnn j) (hωpos i j).le)
      ⟨k, mem_univ k, mul_pos hpk (hωpos i k)⟩
  have hcont : Tendsto (fun t : ℝ => u i (t • y)) (𝓝[<] 1) (𝓝 (u i ((1 : ℝ) • y))) :=
    (((hu i).tendsto _).comp ((tendsto_id.smul_const y))).mono_left nhdsWithin_le_nhds
  rw [one_smul] at hcont
  obtain ⟨t, ht, ht1⟩ := ((hcont.eventually (lt_mem_nhds hlt)).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))).exists
  have h := hbetter i (t • y) (smul_nonneg ht1.1.le hy.1) ht
  have hct : cost p (t • y) = t * cost p y := by simp [cost, mul_sum, mul_left_comm]
  rw [hct] at h
  have := hy.2
  nlinarith [ht1.1, ht1.2]

omit [DecidableEq I] in
/-- A type allocation that is Walrasian at `p` (each `x*ᵢ` demanded, markets
clear) is Walrasian in every replica. -/
theorem replica_isWalrasianEquilibrium {p : ι → ℝ} {xs : I → ι → ℝ}
    (hd : ∀ i, xs i ∈ demand (prefOf (u i)) p (cost p (ω i))) (hsum : ∑ i, xs i = ∑ i, ω i)
    (r : ℕ) : (replica u ω hω r).IsWalrasianEquilibrium p fun a => xs a.1 := by
  refine ⟨fun a => hd a.1, ?_⟩
  simp only [ExchangeEconomy.totalEndowment, replica, Fintype.sum_prod_type, sum_const,
    card_univ, Fintype.card_fin, ← smul_sum, hsum]

/-- **Debreu–Scarf, equilibrium form.** Under the hypotheses of
`walrasian_of_mem_core_replicas`, the replicated allocation is a Walrasian
equilibrium of every replica, at prices `p ≫ 0`. -/
theorem isWalrasianEquilibrium_of_mem_core_replicas [Nonempty I] [Nonempty ι]
    (hu : ∀ i, Continuous (u i)) (hsq : ∀ i, StrictlyQuasiconcave (u i))
    (hmono : ∀ i, StronglyMonotone (prefOf (u i))) (hωpos : ∀ i, PositivePrices (ω i))
    {xs : I → ι → ℝ} (hcore : ∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) :
    ∃ p : ι → ℝ, PositivePrices p ∧
      ∀ r, (replica u ω hω r).IsWalrasianEquilibrium p fun a => xs a.1 := by
  obtain ⟨p, hpos, hd⟩ := walrasian_of_mem_core_replicas hu hsq hmono hωpos hcore
  have hfeas := (hcore 1 one_pos).1
  have hsumx : ∑ i, xs i = ∑ i, ω i := by
    have h := hfeas.2
    simp only [ExchangeEconomy.totalEndowment, replica, Fintype.sum_prod_type,
      Fin.sum_univ_one] at h
    exact h
  exact ⟨p, hpos, replica_isWalrasianEquilibrium hd hsumx⟩

/-- **Debreu–Scarf characterization.** For an allocation that treats all copies
of a type alike, being in the core of every replica is equivalent to being a
Walrasian equilibrium allocation (at strictly positive prices) of every
replica. Combined with equal treatment (`replica_inCore_equalTreatment`), the
allocations that survive in the cores of all replicas are exactly the
Walrasian ones. -/
theorem mem_core_replicas_iff_walrasian [Nonempty I] [Nonempty ι] (hu : ∀ i, Continuous (u i))
    (hsq : ∀ i, StrictlyQuasiconcave (u i)) (hmono : ∀ i, StronglyMonotone (prefOf (u i)))
    (hωpos : ∀ i, PositivePrices (ω i)) {xs : I → ι → ℝ} :
    (∀ r, 0 < r → (replica u ω hω r).InCore fun a => xs a.1) ↔
      ∃ p : ι → ℝ, PositivePrices p ∧
        ∀ r, (replica u ω hω r).IsWalrasianEquilibrium p fun a => xs a.1 :=
  ⟨isWalrasianEquilibrium_of_mem_core_replicas hu hsq hmono hωpos,
    fun ⟨_, _, h⟩ r _ => (h r).inCore⟩

end CoreLimit


namespace GEExamples

/-- Type `i` owns one unit of good `i` and half a unit of the other. -/
noncomputable def halfEndow (i : Fin 2) : Fin 2 → ℝ := fun k => if i = k then 1 else 1 / 2

theorem halfEndow_pos (i : Fin 2) : PositivePrices (halfEndow i) := fun k => by
  simp only [halfEndow]; split_ifs <;> norm_num

/-- **Witness.** In the two-type square-root economy with endowments
`halfEndow` (strictly positive), a Walrasian allocation is in the core of every
replica, so the core hypothesis is satisfiable (the other hypotheses are
`continuous_uSqrt`, `strictlyQuasiconcave_uSqrt`, `stronglyMonotone_uSqrt`,
`halfEndow_pos`). -/
theorem sqrt_core_all_replicas :
    ∃ xs : Fin 2 → Fin 2 → ℝ, ∀ r, 0 < r →
      (replica (fun _ => uSqrt) halfEndow (fun i => fun k => (halfEndow_pos i k).le) r).InCore
        fun a => xs a.1 := by
  obtain ⟨p, x, -, heq⟩ :=
    (replica (fun _ => uSqrt) halfEndow (fun i => fun k => (halfEndow_pos i k).le) 1
      ).exists_walrasianEquilibrium_of_preferences_of_totalEndowment
      (u := fun _ => uSqrt) (fun _ => rfl) (fun _ => continuous_uSqrt)
      (fun _ => strictlyQuasiconcave_uSqrt) (fun _ => stronglyMonotone_uSqrt) (fun k => by
        simp only [ExchangeEconomy.totalEndowment, replica, Finset.sum_apply]
        rw [Fintype.sum_prod_type]
        fin_cases k <;> simp [halfEndow, Fin.sum_univ_two] <;> norm_num)
  refine ⟨fun i => x (i, 0), fun r _ => (replica_isWalrasianEquilibrium (fun i => heq.1 (i, 0))
    ?_ r).inCore⟩
  have h := heq.2
  simp only [ExchangeEconomy.totalEndowment, replica, Fintype.sum_prod_type,
    Fin.sum_univ_one] at h
  exact h

end GEExamples

end Econ
