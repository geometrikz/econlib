/-
# Non-vacuity witnesses for the causal identification theorems

A theorem whose hypotheses can never hold is vacuously true. For each headline
result we exhibit a concrete population where every hypothesis holds and the
conclusion is informative.

* **Randomized experiment / LATE.** `Ω = Bool × Fin 3` with the product of two
  uniform distributions: the first coordinate is the instrument `Z` (a fair
  coin), the second is the unit's *type*: `0` complier, `1` always-taker,
  `2` never-taker. Independence of `Z` and the type holds because `μ` is a
  product measure. Compliers have effect `2`, others effect `0`, so the LATE is
  `2`, while the ATE is `2/3`: the Wald ratio identifies the complier effect,
  not the ATE.
-/
module

public import EconLean.Econometrics.Causal.LATE
public import EconLean.Econometrics.Causal.Unconfoundedness
public import EconLean.Econometrics.Causal.DiD
public import Mathlib.Probability.UniformOn

@[expose] public section

namespace Econ.Causal.Witness

open MeasureTheory ProbabilityTheory

/-- Sample space: (instrument, type). -/
abbrev Ω := Bool × Fin 3

/-- Product of uniform distributions: a fair-coin instrument independent of a
uniformly drawn type. -/
noncomputable def μ : Measure Ω := (uniformOn Set.univ).prod (uniformOn Set.univ)

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- The IV model: type `0` complies, `1` always takes, `2` never takes.
Untreated outcome `0`; treated outcome `2` for compliers and `0` otherwise. -/
def M : IVModel Ω where
  Z := fun ω => ω.1
  D₀ := fun ω => decide (ω.2 = 1)
  D₁ := fun ω => decide (ω.2 ≠ 2)
  Y₀ := fun _ => 0
  Y₁ := fun ω => if ω.2 = 0 then 2 else 0

lemma measurable : M.Measurable' :=
  ⟨measurable_of_finite _, measurable_of_finite _, measurable_of_finite _,
    measurable_of_finite _, measurable_of_finite _⟩

lemma independent : M.Independent μ :=
  (indepFun_prod (μ := (uniformOn Set.univ : Measure Bool))
    (ν := (uniformOn Set.univ : Measure (Fin 3))) (X := id)
    (Y := fun t : Fin 3 => ((0 : ℝ), (if t = 0 then (2 : ℝ) else 0), decide (t = 1),
      decide (t ≠ 2)))
    measurable_id (measurable_of_finite _)).symm

lemma monotone : M.Monotone μ :=
  Filter.Eventually.of_forall fun ω h => by
    obtain ⟨z, t⟩ := ω
    fin_cases t <;> simp_all [M]

lemma zEq_real (b : Bool) : μ.real (M.zEq b) = 1 / 2 := by
  have : M.zEq b = ({b} : Set Bool) ×ˢ (Set.univ : Set (Fin 3)) := by
    ext ω; simp [IVModel.zEq, M]
  rw [this, measureReal_def, μ, Measure.prod_prod, uniformOn_univ, uniformOn_univ]
  simp [Fintype.card_bool]

lemma compliers_eq : M.compliers = (Set.univ : Set Bool) ×ˢ ({0} : Set (Fin 3)) := by
  ext ⟨z, t⟩
  fin_cases t <;> simp [IVModel.compliers, M]

lemma compliers_real : μ.real M.compliers = 1 / 3 := by
  rw [compliers_eq, measureReal_def, μ, Measure.prod_prod, uniformOn_univ, uniformOn_univ,
    Measure.count_univ]
  simp

/-- All hypotheses of the LATE theorem hold in this model, and the LATE is `2`. -/
theorem late_witness :
    M.Measurable' ∧ M.Independent μ ∧ M.Monotone μ ∧ 0 < μ.real (M.zEq true) ∧
      0 < μ.real (M.zEq false) ∧ Integrable M.Y₀ μ ∧ Integrable M.Y₁ μ ∧
      M.firstStage μ ≠ 0 ∧ M.late μ = 2 ∧ M.wald μ = 2 := by
  have hz₁ : 0 < μ.real (M.zEq true) := by rw [zEq_real]; norm_num
  have hz₀ : 0 < μ.real (M.zEq false) := by rw [zEq_real]; norm_num
  have hfs : M.firstStage μ = 1 / 3 := by
    rw [IVModel.firstStage_eq measurable independent monotone hz₁ hz₀, compliers_real]
  have hlate : M.late μ = 2 := by
    rw [IVModel.late]
    have hc : MeasurableSet M.compliers := IVModel.measurableSet_compliers measurable
    rw [condMean_congr hc (Y₂ := fun _ => 2) fun ω h => by
      rw [compliers_eq] at h
      obtain ⟨z, t⟩ := ω
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h
      simp [M, h.2]]
    exact condMean_const _ (by rw [compliers_real]; norm_num)
  refine ⟨measurable, independent, monotone, hz₁, hz₀, integrable_const _, Integrable.of_finite,
    by rw [hfs]; norm_num, hlate, ?_⟩
  rw [IVModel.wald_eq_late measurable independent monotone (integrable_const _)
    Integrable.of_finite hz₁ hz₀ (by rw [hfs]; norm_num), hlate]

/-- **Randomized experiment witness.** Use the coin as the treatment
(`D = Z`) and the unit's type to drive the potential outcomes. Every hypothesis
of `diffInMeans_eq_ate` holds, so the difference in means is the ATE. -/
theorem randomized_witness :
    let D : Ω → Bool := fun ω => ω.1
    let Y₀ : Ω → ℝ := fun _ => 0
    let Y₁ : Ω → ℝ := fun ω => if ω.2 = 0 then 2 else 0
    Measurable D ∧ Measurable Y₀ ∧ Measurable Y₁ ∧ Integrable Y₀ μ ∧ Integrable Y₁ μ ∧
      IndepFun (fun ω => (Y₀ ω, Y₁ ω)) D μ ∧ 0 < μ.real (treated D) ∧
      0 < μ.real (untreated D) ∧ diffInMeans μ D Y₀ Y₁ = ate μ Y₀ Y₁ := by
  intro D Y₀ Y₁
  have hind : IndepFun (fun ω => (Y₀ ω, Y₁ ω)) D μ :=
    (indepFun_prod (μ := (uniformOn Set.univ : Measure Bool))
      (ν := (uniformOn Set.univ : Measure (Fin 3))) (X := id)
      (Y := fun t : Fin 3 => ((0 : ℝ), (if t = 0 then (2 : ℝ) else 0)))
      measurable_id (measurable_of_finite _)).symm
  have h₁ : 0 < μ.real (treated D) := by
    have : μ.real (treated D) = 1 / 2 := zEq_real true
    rw [this]; norm_num
  have h₀ : 0 < μ.real (untreated D) := by
    have : μ.real (untreated D) = 1 / 2 := zEq_real false
    rw [this]; norm_num
  exact ⟨measurable_of_finite _, measurable_of_finite _, measurable_of_finite _,
    Integrable.of_finite, Integrable.of_finite, hind, h₁, h₀,
    diffInMeans_eq_ate (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) Integrable.of_finite Integrable.of_finite hind h₁ h₀⟩

/-! ### Selection on observables with confounding

Reuse `Ω = Bool × Fin 3`: the first coordinate is now a binary covariate `X`,
the second an idiosyncratic draw. Units with `X = 0` are treated when the draw
is `0` (propensity `1/3`); units with `X = 1` are treated when it is not `0`
(propensity `2/3`). Outcomes depend on `X`: `Y₀ = 1{X}`, `Y₁ = 1{X} + 1`.
Treatment is confounded by `X` (both the propensity and `Y₀` vary with `X`),
yet unconfoundedness given `X` and overlap hold. -/

/-- Covariate. -/
def Xc : Ω → Bool := fun ω => ω.1

/-- Treatment, confounded by the covariate. -/
def Dc : Ω → Bool := fun ω => if ω.1 then decide (ω.2 ≠ 0) else decide (ω.2 = 0)

/-- Untreated outcome. -/
def Y₀c : Ω → ℝ := fun ω => ind ω.1

/-- Treated outcome. -/
def Y₁c : Ω → ℝ := fun ω => ind ω.1 + 1

lemma point_real (a : Bool) (t : Fin 3) : μ.real ({a} ×ˢ {t}) = 1 / 6 := by
  rw [measureReal_def, μ, Measure.prod_prod, uniformOn_univ, uniformOn_univ]
  simp; norm_num

lemma stratum_real (a : Bool) : μ.real (stratum Xc a) = 1 / 2 := zEq_real a

lemma cell_pos (a b : Bool) : 0 < μ.real (cell Xc Dc a b) := by
  -- each cell contains a point of mass `1/6`
  obtain ⟨t, ht⟩ : ∃ t : Fin 3, ({a} ×ˢ {t} : Set Ω) ⊆ cell Xc Dc a b := by
    cases a <;> cases b
    · exact ⟨1, by rintro ⟨x, u⟩ ⟨hx, hu⟩; simp_all [cell, Xc, Dc]⟩
    · exact ⟨0, by rintro ⟨x, u⟩ ⟨hx, hu⟩; simp_all [cell, Xc, Dc]⟩
    · exact ⟨0, by rintro ⟨x, u⟩ ⟨hx, hu⟩; simp_all [cell, Xc, Dc]⟩
    · exact ⟨1, by rintro ⟨x, u⟩ ⟨hx, hu⟩; simp_all [cell, Xc, Dc]⟩
  calc (0 : ℝ) < 1 / 6 := by norm_num
    _ = μ.real ({a} ×ˢ {t}) := (point_real a t).symm
    _ ≤ μ.real (cell Xc Dc a b) := measureReal_mono ht

lemma condMean_cov {f : Bool → ℝ} {s : Set Ω} (a : Bool) (hs : MeasurableSet s)
    (hsub : s ⊆ stratum Xc a) (hpos : μ.real s ≠ 0) :
    condMean μ (fun ω => f ω.1) s = f a := by
  rw [condMean_congr hs (Y₂ := fun _ => f a) fun ω h => by
    have : ω.1 = a := hsub h
    simp [this]]
  exact condMean_const _ hpos

/-- **Unconfoundedness witness.** Mean unconfoundedness and overlap hold, while
treatment is confounded by `X`: the propensity score and the untreated outcome
both vary with `X`. -/
theorem unconfounded_witness :
    MeanUnconfounded μ Xc Dc Y₀c Y₁c ∧ Overlap μ Xc Dc ∧
      propensity μ Xc Dc false = 1 / 3 ∧ propensity μ Xc Dc true = 2 / 3 ∧
      Y₀c (false, 0) ≠ Y₀c (true, 0) := by
  have hcellsub : ∀ a b, cell Xc Dc a b ⊆ stratum Xc a := fun a b ω h => h.1
  have hstrat : ∀ a, μ.real (stratum Xc a) ≠ 0 := fun a => by rw [stratum_real]; norm_num
  refine ⟨fun a b hc => ⟨?_, ?_⟩, fun a b _ => cell_pos a b, ?_, ?_, by simp [Y₀c]⟩
  · exact (condMean_cov (f := ind) a (Set.toFinite _).measurableSet (hcellsub a b) hc).trans
      (condMean_cov (f := ind) a (Set.toFinite _).measurableSet subset_rfl (hstrat a)).symm
  · exact (condMean_cov (f := fun x => ind x + 1) a (Set.toFinite _).measurableSet
      (hcellsub a b) hc).trans
      (condMean_cov (f := fun x => ind x + 1) a (Set.toFinite _).measurableSet subset_rfl
        (hstrat a)).symm
  · have : cell Xc Dc false true = {false} ×ˢ {0} := by
      ext ⟨x, u⟩; simp [cell, Xc, Dc]
    rw [propensity, armProb, this, point_real, stratum_real]; norm_num
  · -- `P(D = 1 | X = 1) = 1 − P(D = 0 | X = 1)` and the untreated cell is a point
    have hsplit : μ.real (stratum Xc true)
        = μ.real (cell Xc Dc true true) + μ.real (cell Xc Dc true false) := by
      rw [← measureReal_union _ ((Set.toFinite _).measurableSet)]
      · congr 1; ext ω; simp [stratum, cell]; cases Dc ω <;> simp
      · rw [Set.disjoint_left]; rintro ω ⟨_, h₁⟩ ⟨_, h₂⟩; rw [h₁] at h₂; exact absurd h₂ (by decide)
    have h0 : cell Xc Dc true false = {true} ×ˢ {0} := by
      ext ⟨x, u⟩; simp [cell, Xc, Dc]
    rw [h0, point_real, stratum_real] at hsplit
    rw [propensity, armProb, stratum_real]
    linarith

/-! ### Difference-in-differences

Group `G = ω.1` (half the population is treated). The treated group starts one
unit higher (`Y₀,pre = 1{G}`), both groups trend up by `1`, and the effect in the
post period is `2`. Parallel trends and no anticipation hold, DiD recovers the
ATT `2`, while the naive post-period comparison gives `3` because of the level
gap. -/

/-- The DiD witness population. -/
def S : DiD2x2 Ω where
  G := fun ω => ω.1
  Y0pre := fun ω => ind ω.1
  Y1pre := fun ω => ind ω.1
  Y0post := fun ω => ind ω.1 + 1
  Y1post := fun ω => ind ω.1 + 3

theorem did_witness :
    S.ParallelTrends μ ∧ S.NoAnticipation μ ∧ S.Integrable' μ ∧ S.attPost μ = 2 ∧
      S.did μ = 2 ∧
      condMean μ S.Ypost (treated S.G) - condMean μ S.Ypost (untreated S.G) = 3 := by
  have hm : Measurable S.G := measurable_of_finite _
  have hpos : ∀ a, μ.real (stratum Xc a) ≠ 0 := fun a => by rw [stratum_real]; norm_num
  -- every quantity is a conditional mean of a function of `ω.1` over a group
  have key : ∀ (f : Bool → ℝ) (a : Bool),
      condMean μ (fun ω => f ω.1) (stratum Xc a) = f a := fun f a =>
    condMean_cov a (Set.toFinite _).measurableSet subset_rfl (hpos a)
  have ht : treated S.G = stratum Xc true := rfl
  have hu : untreated S.G = stratum Xc false := rfl
  have hint : S.Integrable' μ :=
    ⟨Integrable.of_finite, Integrable.of_finite, Integrable.of_finite, Integrable.of_finite⟩
  have hpt : S.ParallelTrends μ := by
    unfold DiD2x2.ParallelTrends DiD2x2.trend
    rw [ht, hu]
    exact (key (fun x => ind x + 1 - ind x) true).trans
      ((key (fun x => ind x + 1 - ind x) false).trans (by norm_num)).symm
  have hna : S.NoAnticipation μ := rfl
  have hatt : S.attPost μ = 2 := by
    unfold DiD2x2.attPost att
    rw [ht]
    exact (key (fun x => ind x + 3 - (ind x + 1)) true).trans (by ring)
  refine ⟨hpt, hna, hint, hatt, by rw [DiD2x2.did_eq_att hm hint hpt hna, hatt], ?_⟩
  rw [DiD2x2.Ypost, condMean_observed_treated hm, condMean_observed_untreated hm, ht, hu,
    show condMean μ S.Y1post (stratum Xc true) = ind true + 3 from key (fun x => ind x + 3) true,
    show condMean μ S.Y0post (stratum Xc false) = ind false + 1 from
      key (fun x => ind x + 1) false]
  norm_num

end Econ.Causal.Witness
