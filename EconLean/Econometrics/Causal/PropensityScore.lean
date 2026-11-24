/-
# The propensity score theorem

Rosenbaum and Rubin, "The central role of the propensity score in observational
studies for causal effects", *Biometrika* (1983), Thm 1–3; Imbens and Rubin
(2015), §12.3.

**The results.** Let covariates `X` take finitely many values and let `b(X)` be a
coarsening of `X` on whose fibres the propensity score `e(x) = P(D = 1 | X = x)`
is constant (a *balancing score* in Rosenbaum–Rubin's sense: `e` is a function
of `b`).

* **Balancing** (Rosenbaum–Rubin Thm 1–2): the propensity score given `b(X)` equals
  `e(x)` on every fibre (`armProb_coarsen`), so the treatment probability depends
  on `X` only through `b(X)`.
* **Unconfoundedness passes to balancing scores** (Rosenbaum–Rubin Thm 3): if
  outcomes are mean-unconfounded given `X`, they are mean-unconfounded given
  `b(X)` (`meanUnconfounded_coarsen`). In particular adjusting for the
  one-dimensional propensity score alone suffices (`rosenbaum_rubin`).
* **Overlap passes to balancing scores** (`overlap_coarsen`), so the adjustment
  formula applies with `e(X)` in place of `X`.

Only the "if" direction of Rosenbaum–Rubin Thm 2 (a function of a balancing
score's fibres) is formalised.

**Encoding.** As in `Unconfoundedness.lean`, unconfoundedness is conditional mean
independence on cells of positive probability. The propensity score is valued in
its (finite) range, a subtype of `ℝ`.
-/
module

public import EconLean.Econometrics.Causal.Unconfoundedness

@[expose] public section

namespace Econ.Causal

open MeasureTheory

variable {Ω κ β : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β]

omit [MeasurableSpace Ω] [IsFiniteMeasure μ] [Fintype κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma cell_comp_eq (X : Ω → κ) (D : Ω → Bool) (g : κ → β) (c : β) (d : Bool) [Fintype κ] :
    cell (g ∘ X) D c d = ⋃ x ∈ Finset.univ.filter (fun x => g x = c), cell X D x d := by
  ext ω; simp [cell]

omit [MeasurableSpace Ω] [IsFiniteMeasure μ] [Fintype κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma stratum_comp_eq (X : Ω → κ) (g : κ → β) (c : β) [Fintype κ] :
    stratum (g ∘ X) c = ⋃ x ∈ Finset.univ.filter (fun x => g x = c), stratum X x := by
  ext ω; simp [stratum]

omit [Fintype κ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [DecidableEq β] in
lemma measureReal_cell_add {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X) (hD : Measurable D) (x : κ) :
    μ.real (cell X D x true) + μ.real (cell X D x false) = μ.real (stratum X x) := by
  rw [← measureReal_union _ (measurableSet_cell hX hD x false)]
  · congr 1; ext ω; cases h : D ω <;> simp [cell, stratum, h]
  · rw [Set.disjoint_left]; intro ω h1 h2; simp only [cell, Set.mem_ofPred_eq] at h1 h2
    rw [h1.2] at h2; exact Bool.noConfusion h2.2

omit [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
lemma measureReal_cell_le (X : Ω → κ) (D : Ω → Bool) (x : κ) (d : Bool) :
    μ.real (cell X D x d) ≤ μ.real (stratum X x) :=
  measureReal_mono (fun ω h => h.1)

omit [Fintype κ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
/-- Equal propensity scores give proportional cells: `P(x, d) P(x') = P(x', d) P(x)`. -/
lemma cell_cross {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X) (hD : Measurable D)
    {x x' : κ} (he : μ.real (stratum X x) ≠ 0 → μ.real (stratum X x') ≠ 0 →
      propensity μ X D x = propensity μ X D x') (d : Bool) :
    μ.real (cell X D x d) * μ.real (stratum X x') = μ.real (cell X D x' d) * μ.real (stratum X x) := by
  by_cases h0 : μ.real (stratum X x) = 0
  · have : μ.real (cell X D x d) = 0 :=
      le_antisymm (h0 ▸ measureReal_cell_le X D x d) measureReal_nonneg
    rw [this, h0]; ring
  by_cases h0' : μ.real (stratum X x') = 0
  · have : μ.real (cell X D x' d) = 0 :=
      le_antisymm (h0' ▸ measureReal_cell_le X D x' d) measureReal_nonneg
    rw [this, h0']; ring
  have hp := he h0 h0'
  simp only [propensity, armProb] at hp
  have ht : μ.real (cell X D x true) * μ.real (stratum X x')
      = μ.real (cell X D x' true) * μ.real (stratum X x) := by
    field_simp at hp; linarith
  cases d
  · have a := measureReal_cell_add (μ := μ) hX hD x
    have a' := measureReal_cell_add (μ := μ) hX hD x'
    have e1 : μ.real (cell X D x false) = μ.real (stratum X x) - μ.real (cell X D x true) := by
      linarith
    have e2 : μ.real (cell X D x' false) = μ.real (stratum X x') - μ.real (cell X D x' true) := by
      linarith
    rw [e1, e2]; linarith
  · exact ht

omit [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
/-- `∫_{X=x, D=d} Y = P(X=x, D=d) E[Y | X=x]` under mean unconfoundedness of `Y`. -/
lemma setIntegral_cell {X : Ω → κ} {D : Ω → Bool} {Y : Ω → ℝ} {d : Bool}
    (hY : ∀ x, μ.real (cell X D x d) ≠ 0 →
      condMean μ Y (cell X D x d) = condMean μ Y (stratum X x)) (x : κ) :
    ∫ ω in cell X D x d, Y ω ∂μ = μ.real (cell X D x d) * condMean μ Y (stratum X x) := by
  rw [setIntegral_eq_mul_condMean]
  by_cases h : μ.real (cell X D x d) = 0
  · rw [h, zero_mul, zero_mul]
  · rw [hY x h]

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- The core identity: mean unconfoundedness of one outcome passes from `X` to a
balancing score `g(X)`. -/
lemma condMean_coarsen {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X) (hD : Measurable D)
    {g : κ → β} (hg : ∀ x x', g x = g x' → μ.real (stratum X x) ≠ 0 →
      μ.real (stratum X x') ≠ 0 → propensity μ X D x = propensity μ X D x')
    {Y : Ω → ℝ} (hYi : Integrable Y μ) {d : Bool}
    (hY : ∀ x, μ.real (cell X D x d) ≠ 0 →
      condMean μ Y (cell X D x d) = condMean μ Y (stratum X x))
    (c : β) (hc : μ.real (cell (g ∘ X) D c d) ≠ 0) :
    condMean μ Y (cell (g ∘ X) D c d) = condMean μ Y (stratum (g ∘ X) c) := by
  set F := Finset.univ.filter (fun x => g x = c)
  have hcm : ∀ x, MeasurableSet (cell X D x d) := fun x => measurableSet_cell hX hD x d
  have hsm : ∀ x, MeasurableSet (stratum X x) := measurableSet_stratum hX
  have hdc : Set.PairwiseDisjoint (↑F) fun x => cell X D x d := by
    intro x _ x' _ hxx'; rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2; exact hxx' (h1.1.symm.trans h2.1)
  have hds : Set.PairwiseDisjoint (↑F) fun x => stratum X x := by
    intro x _ x' _ hxx'; rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2; exact hxx' ((show X ω = x from h1).symm.trans h2)
  have hIc : ∫ ω in cell (g ∘ X) D c d, Y ω ∂μ = ∑ x ∈ F, ∫ ω in cell X D x d, Y ω ∂μ := by
    rw [cell_comp_eq, integral_biUnion_finset _ (fun x _ => hcm x) hdc
      (fun x _ => hYi.integrableOn)]
  have hIs : ∫ ω in stratum (g ∘ X) c, Y ω ∂μ = ∑ x ∈ F, ∫ ω in stratum X x, Y ω ∂μ := by
    rw [stratum_comp_eq, integral_biUnion_finset _ (fun x _ => hsm x) hds
      (fun x _ => hYi.integrableOn)]
  have hPc : μ.real (cell (g ∘ X) D c d) = ∑ x ∈ F, μ.real (cell X D x d) := by
    rw [cell_comp_eq, measureReal_biUnion_finset hdc (fun x _ => hcm x)]
  have hPs : μ.real (stratum (g ∘ X) c) = ∑ x ∈ F, μ.real (stratum X x) := by
    rw [stratum_comp_eq, measureReal_biUnion_finset hds (fun x _ => hsm x)]
  have hS : μ.real (stratum (g ∘ X) c) ≠ 0 := by
    intro h0; apply hc
    exact le_antisymm (h0 ▸ measureReal_cell_le (g ∘ X) D c d) measureReal_nonneg
  -- cross-multiplied form of the claim
  have key : (∫ ω in cell (g ∘ X) D c d, Y ω ∂μ) * μ.real (stratum (g ∘ X) c)
      = (∫ ω in stratum (g ∘ X) c, Y ω ∂μ) * μ.real (cell (g ∘ X) D c d) := by
    rw [hIc, hIs, hPc, hPs, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [setIntegral_cell hY, setIntegral_eq_mul_condMean]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun x' hx' => ?_
    have hxx : g x = g x' := by
      simp only [F, Finset.mem_filter] at hx hx'; rw [hx.2, hx'.2]
    have := cell_cross (μ := μ) hX hD (x := x) (x' := x')
      (fun h1 h2 => hg x x' hxx h1 h2) d
    linear_combination (condMean μ Y (stratum X x)) * this
  simp only [condMean]
  field_simp
  linarith [key]

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- **Unconfoundedness given a balancing score** (Rosenbaum–Rubin 1983, Thm 3): if
outcomes are mean-unconfounded given `X` and the propensity score is constant on
the fibres of `g`, they are mean-unconfounded given `g(X)`. -/
theorem meanUnconfounded_coarsen {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X)
    (hD : Measurable D) {g : κ → β}
    (hg : ∀ x x', g x = g x' → μ.real (stratum X x) ≠ 0 →
      μ.real (stratum X x') ≠ 0 → propensity μ X D x = propensity μ X D x')
    {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ)
    (hunc : MeanUnconfounded μ X D Y₀ Y₁) : MeanUnconfounded μ (g ∘ X) D Y₀ Y₁ := by
  intro c d hc
  exact ⟨condMean_coarsen hX hD hg h₀ (fun x hx => (hunc x d hx).1) c hc,
    condMean_coarsen hX hD hg h₁ (fun x hx => (hunc x d hx).2) c hc⟩

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- **Balancing** (Rosenbaum–Rubin 1983, Thm 1–2): on a fibre of a balancing score
with positive probability, the treatment probability given `g(X)` equals the
propensity score of any covariate value in the fibre with positive probability. -/
theorem armProb_coarsen {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X) (hD : Measurable D)
    {g : κ → β} (hg : ∀ x x', g x = g x' → μ.real (stratum X x) ≠ 0 →
      μ.real (stratum X x') ≠ 0 → propensity μ X D x = propensity μ X D x')
    {x : κ} (hx : μ.real (stratum X x) ≠ 0) (d : Bool) :
    armProb μ (g ∘ X) D (g x) d = armProb μ X D x d := by
  have h1 := condMean_coarsen (μ := μ) (d := d) hX hD hg (integrable_const (1 : ℝ))
    (fun x' _ => by
      rw [condMean_const _ ‹_›, condMean_const]
      intro h0; apply ‹μ.real (cell X D x' d) ≠ 0›
      exact le_antisymm (h0 ▸ measureReal_cell_le X D x' d) measureReal_nonneg)
  -- compute directly from the partition sums
  set F := Finset.univ.filter (fun x' => g x' = g x)
  have hcm : ∀ x', MeasurableSet (cell X D x' d) := fun x => measurableSet_cell hX hD x d
  have hsm : ∀ x', MeasurableSet (stratum X x') := measurableSet_stratum hX
  have hdc : Set.PairwiseDisjoint (↑F) fun x' => cell X D x' d := by
    intro a _ a' _ haa; rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2; exact haa (h1.1.symm.trans h2.1)
  have hds : Set.PairwiseDisjoint (↑F) fun x' => stratum X x' := by
    intro a _ a' _ haa; rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2; exact haa ((show X ω = a from h1).symm.trans h2)
  have hPc : μ.real (cell (g ∘ X) D (g x) d) = ∑ x' ∈ F, μ.real (cell X D x' d) := by
    rw [cell_comp_eq, measureReal_biUnion_finset hdc (fun x' _ => hcm x')]
  have hPs : μ.real (stratum (g ∘ X) (g x)) = ∑ x' ∈ F, μ.real (stratum X x') := by
    rw [stratum_comp_eq, measureReal_biUnion_finset hds (fun x' _ => hsm x')]
  have hcross : μ.real (cell (g ∘ X) D (g x) d) * μ.real (stratum X x)
      = μ.real (cell X D x d) * μ.real (stratum (g ∘ X) (g x)) := by
    rw [hPc, hPs, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    have hxx : g x' = g x := (Finset.mem_filter.mp hx').2
    have := cell_cross (μ := μ) hX hD (x := x') (x' := x) (fun h1 h2 => hg x' x hxx h1 h2) d
    linarith
  have hS : μ.real (stratum (g ∘ X) (g x)) ≠ 0 := by
    intro h0
    have hle : μ.real (stratum X x) ≤ μ.real (stratum (g ∘ X) (g x)) :=
      measureReal_mono (fun ω (h : X ω = x) => show g (X ω) = g x by rw [h])
    exact hx (le_antisymm (h0 ▸ hle) measureReal_nonneg)
  clear h1
  simp only [armProb]
  field_simp
  linarith [hcross]


omit [MeasurableSpace κ] [MeasurableSingletonClass κ] [Fintype β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [DecidableEq β] in
/-- **Overlap passes to any coarsening**, in particular to the propensity score:
if every cell of a non-null stratum of `X` has positive probability, the same
holds for `g(X)`. -/
theorem overlap_coarsen {X : Ω → κ} {D : Ω → Bool} (g : κ → β) (h : Overlap μ X D) :
    Overlap μ (g ∘ X) D := by
  classical
  intro c b hc
  obtain ⟨x, hx, hxs⟩ : ∃ x, g x = c ∧ μ.real (stratum X x) ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    apply hc
    rw [stratum_comp_eq]
    refine le_antisymm ((measureReal_biUnion_finset_le _ _).trans (le_of_eq ?_)) measureReal_nonneg
    exact Finset.sum_eq_zero fun x hx' => hne x (Finset.mem_filter.mp hx').2
  refine lt_of_lt_of_le (h x b hxs) (measureReal_mono ?_)
  rw [cell_comp_eq]
  exact Set.subset_iUnion₂ (s := fun x (_ : x ∈ Finset.univ.filter (fun x => g x = c)) =>
    cell X D x b) x (by simp [hx])
/-- The propensity score as a random variable, valued in its finite range. -/
noncomputable def pscore (μ : Measure Ω) (X : Ω → κ) (D : Ω → Bool) :
    κ → Set.range (propensity μ X D) :=
  fun x => ⟨propensity μ X D x, x, rfl⟩

/-- **The propensity score theorem** (Rosenbaum–Rubin 1983, Thm 3; Imbens–Rubin
§12.3): if potential outcomes are mean-unconfounded given covariates `X`, they
are mean-unconfounded given the propensity score `e(X)` alone, and `e(X)` balances:
`P(D = d | e(X) = e(x)) = P(D = d | X = x)`. -/
theorem rosenbaum_rubin {X : Ω → κ} {D : Ω → Bool} (hX : Measurable X) (hD : Measurable D)
    {Y₀ Y₁ : Ω → ℝ} (h₀ : Integrable Y₀ μ) (h₁ : Integrable Y₁ μ)
    (hunc : MeanUnconfounded μ X D Y₀ Y₁) :
    letI : Fintype (Set.range (propensity μ X D)) := Fintype.ofFinite _
    MeanUnconfounded μ (pscore μ X D ∘ X) D Y₀ Y₁ ∧
      ∀ x, μ.real (stratum X x) ≠ 0 → ∀ d,
        armProb μ (pscore μ X D ∘ X) D (pscore μ X D x) d = armProb μ X D x d := by
  let _ : Fintype (Set.range (propensity μ X D)) := Fintype.ofFinite _
  classical
  have hg : ∀ x x', pscore μ X D x = pscore μ X D x' → μ.real (stratum X x) ≠ 0 →
      μ.real (stratum X x') ≠ 0 → propensity μ X D x = propensity μ X D x' :=
    fun x x' h _ _ => congrArg Subtype.val h
  exact ⟨meanUnconfounded_coarsen hX hD hg h₀ h₁ hunc,
    fun x hx d => armProb_coarsen hX hD hg hx d⟩

end Econ.Causal
