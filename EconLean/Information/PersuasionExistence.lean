/-
# Existence of an optimal persuasion signal

Reference: E. Kamenica and M. Gentzkow (2011), "Bayesian Persuasion",
*AER* 101(6), Corollary 1 and the discussion after it; their Proposition 4
bounds the number of messages.

**Result.** If the sender's value `v̂` is upper semicontinuous on the simplex
`Δ(Ω)` (which KG obtain from sender-preferred tie-breaking), then the value
`V μ₀` of persuasion is attained by some splitting (`exists_optimal_splitting`)
and hence by some signal with at most `|Ω| + 2` messages
(`exists_optimal_signal`).

**Proof.**
1. *Carathéodory reduction* (`exists_small`): the point
   `(μ₀, Σ τ_k v̂(ν_k)) = Σ τ_k (ν_k, v̂ ν_k)` lies in the convex hull of the
   finitely many points `(ν_k, v̂ ν_k) ∈ ℝ^Ω × ℝ`; by Carathéodory it is a
   convex combination of affinely independent ones, so of at most
   `dim + 1 = |Ω| + 2` of them. Padding with zero weights gives a splitting
   with exactly `N = |Ω| + 2` posteriors and the same value.
2. *Compactness*: splittings with `N` posteriors form a compact set of pairs
   `(τ, ν)`, on which `Σ τ_k v̂(ν_k)` is upper semicontinuous (`uscOn_mul`:
   a nonnegative continuous weight times an u.s.c. function is u.s.c.;
   no lower bound on `v̂` is needed). It attains its maximum, which by step 1
   is `V μ₀`.

KG's sharper bound `|Ω|` uses that the relevant points lie on the boundary of
the convex hull; it is not formalized here.
-/
module

public import EconLean.Information.Persuasion
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

namespace Econ

namespace Persuasion

open Finset Filter Topology

variable {Ω : Type*} [Fintype Ω]

/-- The simplex is compact. -/
theorem isCompact_beliefs : IsCompact (beliefs Ω) := by
  have hcl : IsClosed (beliefs Ω) := by
    have e : beliefs Ω = (⋂ ω, {μ : Ω → ℝ | 0 ≤ μ ω}) ∩ {μ | ∑ ω, μ ω = 1} := by
      ext μ; simp [beliefs]
    rw [e]
    exact (isClosed_iInter fun ω => isClosed_le continuous_const (continuous_apply ω)).inter
      (isClosed_eq (continuous_finsetSum _ fun ω _ => continuous_apply ω) continuous_const)
  have hsub : beliefs Ω ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 := by
    intro μ hμ ω _
    refine ⟨hμ.1 ω, ?_⟩
    rw [← hμ.2]
    exact single_le_sum (f := μ) (fun j _ => hμ.1 j) (mem_univ ω)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

/-- A nonnegative continuous weight times an upper semicontinuous function is
upper semicontinuous. -/
theorem uscOn_mul {α E : Type*} [TopologicalSpace α] [TopologicalSpace E] {X : Set α}
    {S : Set E} {v : E → ℝ} {g : α → ℝ} {h : α → E} (hv : UpperSemicontinuousOn v S)
    (hg : Continuous g) (hh : Continuous h) (hg0 : ∀ p ∈ X, 0 ≤ g p)
    (hhS : ∀ p ∈ X, h p ∈ S) : UpperSemicontinuousOn (fun p => g p * v (h p)) X := by
  intro p₀ hp₀ y hy
  set t₀ := g p₀
  set a := v (h p₀)
  have hd : 0 < y - t₀ * a := by simp only [t₀, a] at hy ⊢; linarith
  set ε := min 1 ((y - t₀ * a) / (2 * (t₀ + |a| + 1))) with hε
  have ht0 : 0 ≤ t₀ := hg0 p₀ hp₀
  have hden : 0 < 2 * (t₀ + |a| + 1) := by positivity
  have hε0 : 0 < ε := lt_min one_pos (div_pos hd hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (t₀ + |a| + 1) ≤ (y - t₀ * a) / 2 := by
    have := min_le_right 1 ((y - t₀ * a) / (2 * (t₀ + |a| + 1)))
    rw [← hε, le_div_iff₀ hden] at this
    linarith
  -- `v ∘ h` is eventually below `a + ε`
  have h1 : ∀ᶠ p in 𝓝[X] p₀, v (h p) < a + ε :=
    (hh.continuousWithinAt.tendsto_nhdsWithin fun p hp => hhS p hp).eventually
      (hv (h p₀) (hhS p₀ hp₀) (a + ε) (by linarith))
  -- `g` is eventually within `ε` of `t₀`
  have h2 : ∀ᶠ p in 𝓝[X] p₀, |g p - t₀| < ε :=
    nhdsWithin_le_nhds (Filter.mem_of_superset
      (hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (g p₀) hε0))
      fun x hx => by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  filter_upwards [h1, h2, self_mem_nhdsWithin] with p hp1 hp2 hpX
  have hgp : 0 ≤ g p := hg0 p hpX
  have hb1 : g p * v (h p) ≤ g p * (a + ε) := mul_le_mul_of_nonneg_left hp1.le hgp
  have hb2 : (g p - t₀) * (a + ε) ≤ ε * (|a| + 1) := by
    calc (g p - t₀) * (a + ε) ≤ |(g p - t₀) * (a + ε)| := le_abs_self _
      _ = |g p - t₀| * |a + ε| := abs_mul _ _
      _ ≤ ε * (|a| + 1) := by
        refine mul_le_mul hp2.le ?_ (abs_nonneg _) hε0.le
        calc |a + ε| ≤ |a| + |ε| := abs_add_le _ _
          _ ≤ |a| + 1 := by rw [abs_of_pos hε0]; linarith
  have : g p * (a + ε) = t₀ * a + t₀ * ε + (g p - t₀) * (a + ε) := by ring
  nlinarith

/-- The number of posteriors needed: `|Ω| + 2`. -/
abbrev N (Ω : Type*) [Fintype Ω] : ℕ := Fintype.card Ω + 2

/-- Splittings with exactly `N` posteriors, as pairs `(τ, ν)`. -/
def bounded (μ₀ : Ω → ℝ) : Set ((Fin (N Ω) → ℝ) × (Fin (N Ω) → Ω → ℝ)) :=
  {p | (∀ k, 0 ≤ p.1 k) ∧ ∑ k, p.1 k = 1 ∧ (∀ k, p.2 k ∈ beliefs Ω) ∧
    ∀ ω, ∑ k, p.1 k * p.2 k ω = μ₀ ω}

/-- The splitting given by a point of `bounded μ₀`. -/
def toSplitting {μ₀ : Ω → ℝ} {p : (Fin (N Ω) → ℝ) × (Fin (N Ω) → Ω → ℝ)}
    (hp : p ∈ bounded μ₀) : Splitting μ₀ where
  K := N Ω
  τ := p.1
  ν := p.2
  τ_nonneg := hp.1
  τ_sum := hp.2.1
  ν_mem := hp.2.2.1
  mean := hp.2.2.2

/-- Value of a point of `bounded μ₀`. -/
noncomputable def bValue (v : (Ω → ℝ) → ℝ) (p : (Fin (N Ω) → ℝ) × (Fin (N Ω) → Ω → ℝ)) : ℝ :=
  ∑ k, p.1 k * v (p.2 k)

theorem isCompact_bounded (μ₀ : Ω → ℝ) : IsCompact (bounded μ₀) := by
  have hcl : IsClosed (bounded μ₀) := by
    have e : bounded μ₀ = (⋂ k, {p : (Fin (N Ω) → ℝ) × (Fin (N Ω) → Ω → ℝ) | 0 ≤ p.1 k}) ∩
        {p | ∑ k, p.1 k = 1} ∩ (⋂ k, {p | p.2 k ∈ beliefs Ω}) ∩
        ⋂ ω, {p | ∑ k, p.1 k * p.2 k ω = μ₀ ω} := by
      ext p; simp [bounded, and_assoc]
    rw [e]
    have c1 : ∀ k, Continuous fun p : (Fin (N Ω) → ℝ) × (Fin (N Ω) → Ω → ℝ) => p.1 k :=
      fun k => (continuous_apply k).comp continuous_fst
    have c2 : ∀ k, Continuous fun p : (Fin (N Ω) → ℝ) × (Fin (N Ω) → Ω → ℝ) => p.2 k :=
      fun k => (continuous_apply k).comp continuous_snd
    refine (((isClosed_iInter fun k => isClosed_le continuous_const (c1 k)).inter
      (isClosed_eq (continuous_finsetSum _ fun k _ => c1 k) continuous_const)).inter
      (isClosed_iInter fun k => isCompact_beliefs.isClosed.preimage (c2 k))).inter
      (isClosed_iInter fun ω => isClosed_eq (continuous_finsetSum _ fun k _ =>
        (c1 k).mul ((continuous_apply ω).comp (c2 k))) continuous_const)
  have hsub : bounded μ₀ ⊆ (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) ×ˢ
      Set.pi Set.univ fun _ => beliefs Ω := by
    intro p hp
    refine ⟨fun k _ => ⟨hp.1 k, ?_⟩, fun k _ => hp.2.2.1 k⟩
    rw [← hp.2.1]
    exact single_le_sum (f := p.1) (fun j _ => hp.1 j) (mem_univ k)
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).prod
    (isCompact_univ_pi fun _ => isCompact_beliefs)).of_isClosed_subset hcl hsub

/-- Sum over `Fin n` of a function extended by zero along an embedding. -/
theorem sum_extend {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ↪ Fin n) (w : ι → ℝ)
    (H : Fin n → ℝ) :
    ∑ j, Function.extend e w 0 j * H j = ∑ i, w i * H (e i) := by
  classical
  rw [← sum_subset (subset_univ (univ.map e)), sum_map]
  · exact sum_congr rfl fun i _ => by rw [e.injective.extend_apply]
  · intro j _ hj
    have : ¬ ∃ i, e i = j := by
      rintro ⟨i, rfl⟩; exact hj (mem_map_of_mem _ (mem_univ i))
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, zero_mul]

/-- **Carathéodory reduction.** Every splitting's value is achieved by a
splitting with exactly `|Ω| + 2` posteriors. -/
theorem exists_small {v : (Ω → ℝ) → ℝ} {μ₀ : Ω → ℝ} (s : Splitting μ₀) :
    ∃ p ∈ bounded μ₀, bValue v p = s.value v := by
  classical
  set P : Fin s.K → (Ω → ℝ) × ℝ := fun k => (s.ν k, v (s.ν k))
  have hx : ∑ k, s.τ k • P k ∈ convexHull ℝ (Set.range P) :=
    (convex_convexHull ℝ _).sum_mem (fun k _ => s.τ_nonneg k) s.τ_sum
      fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩
  obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  -- at most `|Ω| + 2` points
  have hcard : Fintype.card ι ≤ N Ω := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ ((Ω → ℝ) × ℝ) := Submodule.finrank_le _
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self] at h2
    unfold N; omega
  have hzP : ∀ i, (z i).1 ∈ beliefs Ω ∧ (z i).2 = v (z i).1 := by
    intro i
    obtain ⟨k, hk⟩ := hz ⟨i, rfl⟩
    rw [← hk]
    exact ⟨s.ν_mem k, rfl⟩
  -- the first and second coordinates of the Carathéodory combination
  have hfst : ∀ ω, ∑ i, w i * (z i).1 ω = μ₀ ω := by
    intro ω
    have := congrArg (fun q => q.1 ω) hwz
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      P] at this
    rw [this, s.mean ω]
  have hsnd : ∑ i, w i * (z i).2 = s.value v := by
    have := congrArg Prod.snd hwz
    simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, P] at this
    rw [this]; rfl
  -- pad to `N` posteriors
  let e : ι ↪ Fin (N Ω) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  let τ' : Fin (N Ω) → ℝ := Function.extend e w 0
  let ν' : Fin (N Ω) → Ω → ℝ := Function.extend e (fun i => (z i).1) fun _ => μ₀
  have hν'e : ∀ i, ν' (e i) = (z i).1 := fun i => e.injective.extend_apply _ _ i
  have hτ0 : ∀ j, 0 ≤ τ' j := by
    intro j
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      simp only [τ', e.injective.extend_apply]; exact (hw i).le
    · simp only [τ', Function.extend_apply' _ _ _ h, Pi.zero_apply, le_refl]
  have hν'mem : ∀ j, ν' j ∈ beliefs Ω := by
    intro j
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h; rw [hν'e]; exact (hzP i).1
    · simp only [ν', Function.extend_apply' _ _ _ h]
      -- `μ₀` is a belief: it is a convex combination of posteriors
      refine ⟨fun ω => ?_, ?_⟩
      · rw [← s.mean ω]
        exact sum_nonneg fun k _ => mul_nonneg (s.τ_nonneg k) ((s.ν_mem k).1 ω)
      · simp_rw [← s.mean, sum_comm (γ := Ω), ← mul_sum, (s.ν_mem _).2, mul_one, s.τ_sum]
  refine ⟨(τ', ν'), ⟨hτ0, ?_, hν'mem, fun ω => ?_⟩, ?_⟩
  · have := sum_extend e w (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hw1]
  · show ∑ k, τ' k * ν' k ω = μ₀ ω
    rw [sum_extend e w (fun j => ν' j ω)]
    simp only [hν'e]
    exact hfst ω
  · show ∑ k, τ' k * v (ν' k) = s.value v
    rw [sum_extend e w (fun j => v (ν' j))]
    simp only [hν'e]
    rw [← hsnd]
    exact sum_congr rfl fun i _ => by rw [(hzP i).2]

/-- **Existence of an optimal splitting** (KG Corollary 1 with attainment):
if `v̂` is upper semicontinuous on `Δ(Ω)` and `μ₀` is a belief, some splitting
attains `V μ₀`, and it can be taken with `|Ω| + 2` posteriors. -/
theorem exists_optimal_splitting {v : (Ω → ℝ) → ℝ} (hv : UpperSemicontinuousOn v (beliefs Ω))
    {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    ∃ s : Splitting μ₀, s.K = Fintype.card Ω + 2 ∧ s.value v = V v μ₀ ∧
      ∀ s' : Splitting μ₀, s'.value v ≤ s.value v := by
  -- `v` is bounded above on the compact simplex
  obtain ⟨B, hB⟩ : ∃ B, ∀ μ ∈ beliefs Ω, v μ ≤ B := by
    have hbdd := hv.bddAbove_of_isCompact isCompact_beliefs
    obtain ⟨B, hB⟩ := hbdd
    exact ⟨B, fun μ hμ => hB ⟨μ, hμ, rfl⟩⟩
  have hne : (bounded μ₀).Nonempty := by
    obtain ⟨p, hp, -⟩ := exists_small (v := v) (trivialSplitting h₀)
    exact ⟨p, hp⟩
  have husc : UpperSemicontinuousOn (bValue v) (bounded μ₀) := by
    unfold bValue
    refine upperSemicontinuousOn_sum fun k _ => ?_
    exact uscOn_mul hv ((continuous_apply k).comp continuous_fst)
      ((continuous_apply k).comp continuous_snd) (fun p hp => hp.1 k) (fun p hp => hp.2.2.1 k)
  obtain ⟨p, hp, hmax⟩ := husc.exists_isMaxOn hne (isCompact_bounded μ₀)
  have hall : ∀ s' : Splitting μ₀, s'.value v ≤ (toSplitting hp).value v := by
    intro s'
    obtain ⟨q, hq, hqv⟩ := exists_small (v := v) s'
    rw [← hqv]
    exact hmax hq
  refine ⟨toSplitting hp, rfl, le_antisymm (value_le_V hB _) ?_, hall⟩
  exact csSup_le ⟨_, ⟨trivialSplitting h₀, rfl⟩⟩ (by rintro _ ⟨s', rfl⟩; exact hall s')

/-- **Existence of an optimal signal** with `|Ω| + 2` messages. -/
theorem exists_optimal_signal {v : (Ω → ℝ) → ℝ} (hv : UpperSemicontinuousOn v (beliefs Ω))
    {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    ∃ σ : Signal Ω (Fin (Fintype.card Ω + 2)), signalValue v μ₀ σ = V v μ₀ := by
  obtain ⟨s, hK, hs, -⟩ := exists_optimal_splitting hv h₀
  obtain ⟨K, τ, ν, h1, h2, h3, h4⟩ := s
  subst hK
  exact ⟨Splitting.toSignal ⟨_, τ, ν, h1, h2, h3, h4⟩, by rw [Splitting.value_toSignal]; exact hs⟩

/-- **The prosecutor has an optimal signal**: `convict` is upper
semicontinuous (the judge breaks ties toward conviction). -/
theorem convict_usc : UpperSemicontinuousOn convict (beliefs (Fin 2)) := by
  intro μ _ y hy
  have hcl : IsClosed {μ : Fin 2 → ℝ | 1 / 2 ≤ μ 1} := isClosed_le continuous_const
    (continuous_apply 1)
  unfold convict at hy ⊢
  by_cases h : 1 / 2 ≤ μ 1
  · rw [ite_eq_left h] at hy
    exact Eventually.of_forall fun μ' => by dsimp only; split_ifs <;> linarith
  · rw [ite_eq_right h] at hy
    have : ∀ᶠ μ' in 𝓝[beliefs (Fin 2)] μ, μ' ∈ {μ : Fin 2 → ℝ | 1 / 2 ≤ μ 1}ᶜ :=
      nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds h)
    filter_upwards [this] with μ' hμ'
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hμ'
    rw [ite_eq_right hμ']; exact hy

/-- **The prosecutor's optimal signal exists** with at most four messages and
achieves `3/5`. -/
theorem prosecutor_exists_optimal :
    ∃ σ : Signal (Fin 2) (Fin (Fintype.card (Fin 2) + 2)), signalValue convict prior σ = 3 / 5 := by
  obtain ⟨σ, hσ⟩ := exists_optimal_signal convict_usc prior_mem
  exact ⟨σ, hσ.trans prosecutor_V.1⟩

end Persuasion

end Econ
