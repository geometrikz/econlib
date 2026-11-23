/-
# Instrumental variables and the LATE theorem

Imbens–Angrist (1994), "Identification and Estimation of Local Average
Treatment Effects", *Econometrica* 62(2), Theorem 1; Angrist–Imbens–Rubin
(1996); Angrist–Pischke (2009) §4.4.1, Theorem 4.4.1.

**The economics.** A binary instrument `Z` (e.g. a draft lottery) shifts a
binary treatment. Each unit has *potential treatments* `D₀, D₁` (treatment if
`Z = 0` / `Z = 1`) and *potential outcomes* `Y₀, Y₁` (outcome if untreated /
treated). Observed: `D = D_Z` and `Y = Y_D`.

Assumptions (Imbens–Angrist 1994, Conditions 1–2; Angrist–Pischke §4.4.1):
1. **Independence**: `(Y₀, Y₁, D₀, D₁) ⫫ Z`.
2. **Exclusion**: the outcome depends on `Z` only through `D`. This is built
   into the encoding: potential outcomes are indexed by `D` alone.
3. **First stage**: `E[D | Z=1] ≠ E[D | Z=0]`.
4. **Monotonicity**: `D₁ ≥ D₀` almost surely (no *defiers*).

Units split into *compliers* (`D₁ = 1, D₀ = 0`), *always-takers*,
*never-takers* (and defiers, ruled out by 4).

**Theorem (LATE).** The Wald ratio
`(E[Y | Z=1] − E[Y | Z=0]) / (E[D | Z=1] − E[D | Z=0])`
equals `E[Y₁ − Y₀ | complier]`, and the first stage equals `P(complier)`.

We also need `0 < P(Z = 1) < 1` so that the conditional means are defined.
-/
module

public import EconLean.Econometrics.Causal.PotentialOutcomes

@[expose] public section

namespace Econ.Causal

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A binary-instrument model: instrument `Z`, potential treatments `D₀ D₁`,
potential outcomes `Y₀ Y₁`. Exclusion is built in (outcomes are indexed by the
treatment only). -/
structure IVModel (Ω : Type*) where
  /-- binary instrument -/
  Z : Ω → Bool
  /-- treatment status if the instrument is off -/
  D₀ : Ω → Bool
  /-- treatment status if the instrument is on -/
  D₁ : Ω → Bool
  /-- outcome if untreated -/
  Y₀ : Ω → ℝ
  /-- outcome if treated -/
  Y₁ : Ω → ℝ

namespace IVModel

variable (M : IVModel Ω)

/-- Observed treatment `D = D_Z`. -/
def D (ω : Ω) : Bool := if M.Z ω then M.D₁ ω else M.D₀ ω

/-- Observed outcome `Y = Y_D`. -/
def Y (ω : Ω) : ℝ := if M.D ω then M.Y₁ ω else M.Y₀ ω

/-- The event "instrument equals `b`". -/
def zEq (b : Bool) : Set Ω := {ω | M.Z ω = b}

/-- Compliers: take the treatment iff the instrument is on. -/
def compliers : Set Ω := {ω | M.D₁ ω = true ∧ M.D₀ ω = false}

/-- Measurability of all primitives. -/
structure Measurable' : Prop where
  Z : Measurable M.Z
  D₀ : Measurable M.D₀
  D₁ : Measurable M.D₁
  Y₀ : Measurable M.Y₀
  Y₁ : Measurable M.Y₁

/-- The IV independence assumption: `(Y₀, Y₁, D₀, D₁) ⫫ Z`. -/
def Independent (μ : Measure Ω) : Prop :=
  IndepFun (fun ω => (M.Y₀ ω, M.Y₁ ω, M.D₀ ω, M.D₁ ω)) M.Z μ

/-- Monotonicity (no defiers): `D₀ ≤ D₁` almost surely. -/
def Monotone (μ : Measure Ω) : Prop := ∀ᵐ ω ∂μ, M.D₀ ω = true → M.D₁ ω = true

/-- The first stage `E[D | Z=1] − E[D | Z=0]`. -/
noncomputable def firstStage (μ : Measure Ω) : ℝ :=
  condMean μ (fun ω => ind (M.D ω)) (M.zEq true) - condMean μ (fun ω => ind (M.D ω)) (M.zEq false)

/-- The reduced form `E[Y | Z=1] − E[Y | Z=0]`. -/
noncomputable def reducedForm (μ : Measure Ω) : ℝ :=
  condMean μ M.Y (M.zEq true) - condMean μ M.Y (M.zEq false)

/-- The Wald estimand: reduced form over first stage. -/
noncomputable def wald (μ : Measure Ω) : ℝ := M.reducedForm μ / M.firstStage μ

/-- The local average treatment effect `E[Y₁ − Y₀ | complier]`. -/
noncomputable def late (μ : Measure Ω) : ℝ := condMean μ (fun ω => M.Y₁ ω - M.Y₀ ω) M.compliers

variable {M}

/-- Outcome that would be realised if the instrument were set to `b`:
`Y_{D_b}`. A measurable function of `(Y₀, Y₁, D₀, D₁)`. -/
def yAt (M : IVModel Ω) (b : Bool) (ω : Ω) : ℝ :=
  if (if b then M.D₁ ω else M.D₀ ω) then M.Y₁ ω else M.Y₀ ω

/-- The function of the type vector `(y₀, y₁, d₀, d₁)` giving `Y_{D_b}`. -/
def yAtFn (b : Bool) (p : ℝ × ℝ × Bool × Bool) : ℝ :=
  if (if b then p.2.2.2 else p.2.2.1) then p.2.1 else p.1

lemma measurable_yAtFn (b : Bool) : Measurable (yAtFn b) := by
  unfold yAtFn
  cases b
  · exact Measurable.ite ((measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurableSet_singleton true)) (measurable_fst.comp measurable_snd) measurable_fst
  · exact Measurable.ite ((measurable_snd.comp (measurable_snd.comp measurable_snd))
      (measurableSet_singleton true)) (measurable_fst.comp measurable_snd) measurable_fst

lemma integrable_yAt (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ)
    (hm : M.Measurable' ) (b : Bool) : Integrable (M.yAt b) μ := by
  have hset : MeasurableSet {ω | (if b then M.D₁ ω else M.D₀ ω) = true} := by
    cases b
    · exact hm.D₀ (measurableSet_singleton true)
    · exact hm.D₁ (measurableSet_singleton true)
  have : M.yAt b = Set.piecewise {ω | (if b then M.D₁ ω else M.D₀ ω) = true} M.Y₁ M.Y₀ := by
    funext ω
    simp only [yAt, Set.piecewise, Set.mem_ofPred_eq]
  rw [this]
  exact Integrable.piecewise hset.nullMeasurableSet h₁.integrableOn h₀.integrableOn

/-- On `{Z = b}` the observed outcome is `Y_{D_b}`, and independence makes its
conditional mean the unconditional mean `E[Y_{D_b}]`. -/
lemma condMean_Y_zEq [IsProbabilityMeasure μ] (hm : M.Measurable') (hind : M.Independent μ)
    {b : Bool} (hb : μ.real (M.zEq b) ≠ 0) :
    condMean μ M.Y (M.zEq b) = ∫ ω, M.yAt b ω ∂μ := by
  have hz : MeasurableSet (M.zEq b) := hm.Z (measurableSet_singleton b)
  rw [condMean_congr hz (Y₂ := M.yAt b) fun ω (h : M.Z ω = b) => by
    simp [Y, D, yAt, h]]
  have hvec : Measurable (fun ω => (M.Y₀ ω, M.Y₁ ω, M.D₀ ω, M.D₁ ω)) :=
    hm.Y₀.prodMk (hm.Y₁.prodMk (hm.D₀.prodMk hm.D₁))
  have hi : IndepFun (M.yAt b) M.Z μ := by
    have := hind.comp (φ := yAtFn b) (ψ := id) (measurable_yAtFn b) measurable_id
    convert this using 1
    · funext ω; cases b <;> rfl
    · rfl
  have hmeas : AEStronglyMeasurable (M.yAt b) μ := by
    have : M.yAt b = yAtFn b ∘ (fun ω => (M.Y₀ ω, M.Y₁ ω, M.D₀ ω, M.D₁ ω)) := by
      funext ω; cases b <;> rfl
    rw [this]
    exact ((measurable_yAtFn b).comp hvec).aestronglyMeasurable
  exact condMean_eq_integral_of_indepFun hi hmeas hm.Z hb

/-- Same for the observed treatment: `E[D | Z = b] = P(D_b = 1)`. -/
lemma condMean_D_zEq [IsProbabilityMeasure μ] (hm : M.Measurable') (hind : M.Independent μ)
    {b : Bool} (hb : μ.real (M.zEq b) ≠ 0) :
    condMean μ (fun ω => ind (M.D ω)) (M.zEq b)
      = ∫ ω, ind (if b then M.D₁ ω else M.D₀ ω) ∂μ := by
  have hz : MeasurableSet (M.zEq b) := hm.Z (measurableSet_singleton b)
  rw [condMean_congr hz (Y₂ := fun ω => ind (if b then M.D₁ ω else M.D₀ ω))
    fun ω (h : M.Z ω = b) => by simp [D, h]]
  have hvec : Measurable (fun ω => (M.Y₀ ω, M.Y₁ ω, M.D₀ ω, M.D₁ ω)) :=
    hm.Y₀.prodMk (hm.Y₁.prodMk (hm.D₀.prodMk hm.D₁))
  set g : ℝ × ℝ × Bool × Bool → ℝ := fun p => ind (if b then p.2.2.2 else p.2.2.1) with hg
  have hgm : Measurable g := by
    cases b
    · exact measurable_ind.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
    · exact measurable_ind.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hi := hind.comp (φ := g) (ψ := id) hgm measurable_id
  exact condMean_eq_integral_of_indepFun hi (hgm.comp hvec).aestronglyMeasurable hm.Z hb

/-- Under monotonicity, `Y_{D₁} − Y_{D₀} = (Y₁ − Y₀) 1{complier}` almost surely. -/
lemma yAt_sub_ae (hmono : M.Monotone μ) :
    (fun ω => M.yAt true ω - M.yAt false ω)
      =ᵐ[μ] M.compliers.indicator (fun ω => M.Y₁ ω - M.Y₀ ω) := by
  filter_upwards [hmono] with ω hω
  by_cases h1 : M.D₁ ω = true <;> by_cases h0 : M.D₀ ω = true <;>
    simp_all [yAt, compliers, Set.indicator]

/-- Under monotonicity, `1{D₁} − 1{D₀} = 1{complier}` almost surely. -/
lemma ind_sub_ae (hmono : M.Monotone μ) :
    (fun ω => ind (M.D₁ ω) - ind (M.D₀ ω)) =ᵐ[μ] M.compliers.indicator (fun _ => (1 : ℝ)) := by
  filter_upwards [hmono] with ω hω
  by_cases h1 : M.D₁ ω = true <;> by_cases h0 : M.D₀ ω = true <;>
    simp_all [ind, compliers, Set.indicator]

lemma measurableSet_compliers (hm : M.Measurable') : MeasurableSet M.compliers :=
  (hm.D₁ (measurableSet_singleton true)).inter (hm.D₀ (measurableSet_singleton false))

/-- **First stage = share of compliers** (Imbens–Angrist 1994). Under
independence and monotonicity, `E[D | Z=1] − E[D | Z=0] = P(complier)`. -/
theorem firstStage_eq [IsProbabilityMeasure μ] (hm : M.Measurable') (hind : M.Independent μ)
    (hmono : M.Monotone μ) (hz₁ : 0 < μ.real (M.zEq true)) (hz₀ : 0 < μ.real (M.zEq false)) :
    M.firstStage μ = μ.real M.compliers := by
  rw [firstStage, condMean_D_zEq hm hind hz₁.ne', condMean_D_zEq hm hind hz₀.ne']
  simp only [ite_true, Bool.false_eq_true, ite_false]
  rw [← integral_sub (integrable_ind hm.D₁) (integrable_ind hm.D₀),
    integral_congr_ae (ind_sub_ae hmono), integral_indicator (measurableSet_compliers hm),
    setIntegral_const, smul_eq_mul, mul_one]

/-- **Reduced form = complier effect × complier share.** -/
theorem reducedForm_eq [IsProbabilityMeasure μ] (hm : M.Measurable') (hind : M.Independent μ)
    (hmono : M.Monotone μ) (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ)
    (hz₁ : 0 < μ.real (M.zEq true)) (hz₀ : 0 < μ.real (M.zEq false)) :
    M.reducedForm μ = ∫ ω in M.compliers, (M.Y₁ ω - M.Y₀ ω) ∂μ := by
  rw [reducedForm, condMean_Y_zEq hm hind hz₁.ne', condMean_Y_zEq hm hind hz₀.ne',
    ← integral_sub (integrable_yAt h₀ h₁ hm true) (integrable_yAt h₀ h₁ hm false),
    integral_congr_ae (yAt_sub_ae hmono), integral_indicator (measurableSet_compliers hm)]

/-- **LATE theorem** (Imbens–Angrist 1994, Theorem 1). Under independence,
exclusion (built in), monotonicity, a nonzero first stage, and
`0 < P(Z=1) < 1`, the Wald estimand equals the average treatment effect for
compliers. -/
theorem wald_eq_late [IsProbabilityMeasure μ] (hm : M.Measurable') (hind : M.Independent μ)
    (hmono : M.Monotone μ) (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ)
    (hz₁ : 0 < μ.real (M.zEq true)) (hz₀ : 0 < μ.real (M.zEq false))
    (hfs : M.firstStage μ ≠ 0) :
    M.wald μ = M.late μ := by
  have hfs' := hfs
  rw [firstStage_eq hm hind hmono hz₁ hz₀] at hfs'
  rw [wald, reducedForm_eq hm hind hmono h₀ h₁ hz₁ hz₀, firstStage_eq hm hind hmono hz₁ hz₀,
    late, condMean, div_eq_inv_mul]

end IVModel

end Econ.Causal
