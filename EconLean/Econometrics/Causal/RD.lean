/-
# Regression discontinuity: identification

Hahn–Todd–van der Klaauw (2001), "Identification and Estimation of Treatment
Effects with a Regression-Discontinuity Design", *Econometrica* 69(1),
Theorems 1–3; Imbens–Lemieux (2008), *Journal of Econometrics* 142, §2–3;
Lee–Lemieux (2010), *Journal of Economic Literature* 48, §2.

**The economics.** Treatment depends on a running variable `X` crossing a
cutoff `c` (test score, vote share, age). We work with conditional-mean
functions of the running variable, which are the primitives in HTvdK:

* **Sharp RD.** `D = 1{X ≥ c}`. Let `m₀ x = E[Y₀ | X = x]` and
  `m₁ x = E[Y₁ | X = x]`. The observed regression function is
  `m x = E[Y | X = x] = m₁ x` for `x ≥ c` and `m₀ x` for `x < c`.
  If `m₀` and `m₁` are continuous at `c` (HTvdK Assumption (A2)), then
  `lim_{x↓c} m x − lim_{x↑c} m x = m₁ c − m₀ c = E[Y₁ − Y₀ | X = c]`.
  We also prove the *identification* form: two structures `(m₀, m₁)` and
  `(m₀', m₁')` that generate the same observed `m` have the same effect at `c`.
* **Fuzzy RD.** Crossing `c` changes the probability of treatment. With
  monotonicity there are three types at each `x`: always-takers (share `πa x`),
  never-takers (`πn x`) and compliers (`πc x`), who are treated iff `x ≥ c`.
  The observed `E[D | X = x]` and `E[Y | X = x]` are the mixtures written out in
  `FuzzyRD.meanD` and `FuzzyRD.meanY`. If all shares and type-specific mean
  potential outcomes are continuous at `c` and `πc c > 0`, the ratio of the
  jumps in `E[Y | X]` and `E[D | X]` equals the compliers' average effect at the
  cutoff (HTvdK Thm 3; Imbens–Lemieux eq. (3)).

**Documented deviation.** Conditional means given a continuous `X` are only
defined almost everywhere, so a limit "as `x → c`" of `E[Y | X = x]` needs a
chosen version. Following HTvdK we take the (continuous) conditional-mean
functions as primitives instead of deriving them from a joint distribution.
HTvdK's requirement that the running variable has positive density around `c`
is what makes these functions identified from data near `c`; in this encoding
the observed regression function is given on all of `ℝ`, so no density
condition appears. In the fuzzy design, exclusion and monotonicity (no
defiers) are built into the encoding, and the theorems do not need the type
shares to be probabilities (`FuzzyRD.IsProb` records that they are, for the
witness).
-/
module

public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace Econ.Causal.RD

open Filter Topology Set

/-! ## Sharp RD -/

/-- Observed regression function in a sharp RD: `m₁` at or above the cutoff,
`m₀` below. -/
noncomputable def sharpMean (m₀ m₁ : ℝ → ℝ) (c x : ℝ) : ℝ := if c ≤ x then m₁ x else m₀ x

/-- The right limit of the observed regression function is `m₁ c`. -/
theorem tendsto_sharpMean_right {m₀ m₁ : ℝ → ℝ} {c : ℝ} (h₁ : ContinuousAt m₁ c) :
    Tendsto (sharpMean m₀ m₁ c) (𝓝[≥] c) (𝓝 (m₁ c)) := by
  have : sharpMean m₀ m₁ c =ᶠ[𝓝[≥] c] m₁ :=
    eventually_nhdsWithin_of_forall fun x (hx : c ≤ x) => by simp [sharpMean, hx]
  exact (tendsto_congr' this).mpr (h₁.tendsto.mono_left nhdsWithin_le_nhds)

/-- The left limit of the observed regression function is `m₀ c`. -/
theorem tendsto_sharpMean_left {m₀ m₁ : ℝ → ℝ} {c : ℝ} (h₀ : ContinuousAt m₀ c) :
    Tendsto (sharpMean m₀ m₁ c) (𝓝[<] c) (𝓝 (m₀ c)) := by
  have : sharpMean m₀ m₁ c =ᶠ[𝓝[<] c] m₀ :=
    eventually_nhdsWithin_of_forall fun x (hx : x < c) => by simp [sharpMean, not_le.mpr hx]
  exact (tendsto_congr' this).mpr (h₀.tendsto.mono_left nhdsWithin_le_nhds)

/-- **Sharp RD identification** (HTvdK 2001, Theorem 1). If the conditional
means of both potential outcomes are continuous at the cutoff, the jump of the
observed regression function at `c`, `lim_{x↓c} m − lim_{x↑c} m`, equals the
average treatment effect at the cutoff `m₁ c − m₀ c`. Stated as: the right and
left limits exist and are `m₁ c` and `m₀ c`. -/
theorem sharp_rd {m₀ m₁ : ℝ → ℝ} {c : ℝ} (h₀ : ContinuousAt m₀ c) (h₁ : ContinuousAt m₁ c) :
    Tendsto (sharpMean m₀ m₁ c) (𝓝[≥] c) (𝓝 (m₁ c)) ∧
      Tendsto (sharpMean m₀ m₁ c) (𝓝[<] c) (𝓝 (m₀ c)) :=
  ⟨tendsto_sharpMean_right h₁, tendsto_sharpMean_left h₀⟩

/-- **Identification form.** Two structures with continuous conditional means
that generate the same observed regression function have the same treatment
effect at the cutoff. So `m₁ c − m₀ c` is a functional of the observed
distribution. -/
theorem sharp_rd_identified {m₀ m₁ m₀' m₁' : ℝ → ℝ} {c : ℝ} (h₀ : ContinuousAt m₀ c)
    (h₁ : ContinuousAt m₁ c) (h₀' : ContinuousAt m₀' c) (h₁' : ContinuousAt m₁' c)
    (hobs : sharpMean m₀ m₁ c = sharpMean m₀' m₁' c) :
    m₁ c - m₀ c = m₁' c - m₀' c := by
  have hr := tendsto_nhds_unique (tendsto_sharpMean_right (m₀ := m₀) h₁)
    (hobs ▸ tendsto_sharpMean_right (m₀ := m₀') h₁')
  have hl := tendsto_nhds_unique (tendsto_sharpMean_left (m₁ := m₁) h₀)
    (hobs ▸ tendsto_sharpMean_left (m₁ := m₁') h₀')
  rw [hr, hl]

/-- Without continuity there is no identification: a jump in `m₀` at the
cutoff is indistinguishable from a treatment effect. A structure with effect
`1` at the cutoff and a structure with effect `0` (whose untreated mean jumps at
the cutoff) generate the same observed regression function. -/
theorem sharp_rd_not_identified_without_continuity :
    ∃ m₀ m₁ m₀' m₁' : ℝ → ℝ, sharpMean m₀ m₁ 0 = sharpMean m₀' m₁' 0 ∧
      ContinuousAt m₀ 0 ∧ ContinuousAt m₁ 0 ∧ ContinuousAt m₁' 0 ∧
      (∀ x < 0, m₀' x = 0) ∧ (∀ x, 0 ≤ x → m₀' x = 1) ∧
      m₁ 0 - m₀ 0 = 1 ∧ m₁' 0 - m₀' 0 = 0 := by
  -- Structure 1: `m₀ = 0`, `m₁ = 1` (effect 1, both continuous).
  -- Structure 2: `m₀' = 1{x ≥ 0}` jumps at the cutoff, `m₁' = 1` (effect 0).
  refine ⟨fun _ => 0, fun _ => 1, fun x => if 0 ≤ x then 1 else 0, fun _ => 1, ?_,
    continuousAt_const, continuousAt_const, continuousAt_const,
    fun x hx => by simp [not_le.mpr hx], fun x hx => by simp [hx], by norm_num, by norm_num⟩
  funext x
  by_cases hx : 0 ≤ x <;> simp [sharpMean, hx]

/-! ## Fuzzy RD -/

/-- A fuzzy RD population described by type shares and type-specific mean
potential outcomes as functions of the running variable. Defiers are ruled out
(monotonicity). -/
structure FuzzyRD where
  /-- cutoff -/
  c : ℝ
  /-- share of always-takers at `x` -/
  πa : ℝ → ℝ
  /-- share of never-takers at `x` -/
  πn : ℝ → ℝ
  /-- share of compliers at `x` -/
  πc : ℝ → ℝ
  /-- mean treated outcome of always-takers at `x` -/
  ya : ℝ → ℝ
  /-- mean untreated outcome of never-takers at `x` -/
  yn : ℝ → ℝ
  /-- mean untreated outcome of compliers at `x` -/
  y0c : ℝ → ℝ
  /-- mean treated outcome of compliers at `x` -/
  y1c : ℝ → ℝ

namespace FuzzyRD

variable (F : FuzzyRD)

/-- `E[D | X = x]`: always-takers are treated; compliers are treated iff `x ≥ c`. -/
noncomputable def meanD (x : ℝ) : ℝ := F.πa x + if F.c ≤ x then F.πc x else 0

/-- `E[Y | X = x]`: mixture of the type-specific mean outcomes. -/
noncomputable def meanY (x : ℝ) : ℝ :=
  F.πa x * F.ya x + F.πn x * F.yn x + F.πc x * (if F.c ≤ x then F.y1c x else F.y0c x)

/-- The type shares form a probability distribution at every `x`. -/
def IsProb : Prop :=
  ∀ x, 0 ≤ F.πa x ∧ 0 ≤ F.πn x ∧ 0 ≤ F.πc x ∧ F.πa x + F.πn x + F.πc x = 1

/-- HTvdK's continuity assumptions at the cutoff: type shares and type-specific
mean potential outcomes are continuous at `c`. -/
structure Continuous' : Prop where
  πa : ContinuousAt F.πa F.c
  πn : ContinuousAt F.πn F.c
  πc : ContinuousAt F.πc F.c
  ya : ContinuousAt F.ya F.c
  yn : ContinuousAt F.yn F.c
  y0c : ContinuousAt F.y0c F.c
  y1c : ContinuousAt F.y1c F.c

variable {F}

theorem tendsto_meanD_right (hc : F.Continuous') :
    Tendsto F.meanD (𝓝[≥] F.c) (𝓝 (F.πa F.c + F.πc F.c)) := by
  have : F.meanD =ᶠ[𝓝[≥] F.c] fun x => F.πa x + F.πc x :=
    eventually_nhdsWithin_of_forall fun x (hx : F.c ≤ x) => by simp [meanD, hx]
  exact (tendsto_congr' this).mpr ((hc.πa.add hc.πc).tendsto.mono_left nhdsWithin_le_nhds)

theorem tendsto_meanD_left (hc : F.Continuous') :
    Tendsto F.meanD (𝓝[<] F.c) (𝓝 (F.πa F.c)) := by
  have : F.meanD =ᶠ[𝓝[<] F.c] F.πa :=
    eventually_nhdsWithin_of_forall fun x (hx : x < F.c) => by simp [meanD, not_le.mpr hx]
  exact (tendsto_congr' this).mpr (hc.πa.tendsto.mono_left nhdsWithin_le_nhds)

theorem tendsto_meanY_right (hc : F.Continuous') :
    Tendsto F.meanY (𝓝[≥] F.c)
      (𝓝 (F.πa F.c * F.ya F.c + F.πn F.c * F.yn F.c + F.πc F.c * F.y1c F.c)) := by
  have : F.meanY =ᶠ[𝓝[≥] F.c] fun x => F.πa x * F.ya x + F.πn x * F.yn x + F.πc x * F.y1c x :=
    eventually_nhdsWithin_of_forall fun x (hx : F.c ≤ x) => by simp [meanY, hx]
  refine (tendsto_congr' this).mpr (ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds)
  exact ((hc.πa.mul hc.ya).add (hc.πn.mul hc.yn)).add (hc.πc.mul hc.y1c)

theorem tendsto_meanY_left (hc : F.Continuous') :
    Tendsto F.meanY (𝓝[<] F.c)
      (𝓝 (F.πa F.c * F.ya F.c + F.πn F.c * F.yn F.c + F.πc F.c * F.y0c F.c)) := by
  have : F.meanY =ᶠ[𝓝[<] F.c] fun x => F.πa x * F.ya x + F.πn x * F.yn x + F.πc x * F.y0c x :=
    eventually_nhdsWithin_of_forall fun x (hx : x < F.c) => by simp [meanY, not_le.mpr hx]
  refine (tendsto_congr' this).mpr (ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds)
  exact ((hc.πa.mul hc.ya).add (hc.πn.mul hc.yn)).add (hc.πc.mul hc.y0c)

/-- **Fuzzy RD identification** (HTvdK 2001, Theorem 3; Imbens–Lemieux 2008
§3.2). Let `jumpY` and `jumpD` be the jumps (right limit minus left limit) of
the observed `E[Y | X]` and `E[D | X]` at the cutoff. Under continuity of the
type shares and type-specific means, and a positive share of compliers at the
cutoff, the limits exist, `jumpD = πc c`, and `jumpY / jumpD` equals the
compliers' average treatment effect at the cutoff. -/
theorem fuzzy_rd (hc : F.Continuous') (hπ : 0 < F.πc F.c) :
    ∃ yR yL dR dL : ℝ,
      Tendsto F.meanY (𝓝[≥] F.c) (𝓝 yR) ∧ Tendsto F.meanY (𝓝[<] F.c) (𝓝 yL) ∧
      Tendsto F.meanD (𝓝[≥] F.c) (𝓝 dR) ∧ Tendsto F.meanD (𝓝[<] F.c) (𝓝 dL) ∧
      dR - dL = F.πc F.c ∧ (yR - yL) / (dR - dL) = F.y1c F.c - F.y0c F.c := by
  refine ⟨_, _, _, _, tendsto_meanY_right hc, tendsto_meanY_left hc, tendsto_meanD_right hc,
    tendsto_meanD_left hc, by ring, ?_⟩
  rw [div_eq_iff (by simpa using hπ.ne')]
  ring

/-- The fuzzy-RD ratio does not depend on which limits are used: any limits of
the observed functions give the same ratio (limits along nontrivial filters are
unique). -/
theorem fuzzy_rd_ratio (hc : F.Continuous') (hπ : 0 < F.πc F.c) {yR yL dR dL : ℝ}
    (hyR : Tendsto F.meanY (𝓝[≥] F.c) (𝓝 yR)) (hyL : Tendsto F.meanY (𝓝[<] F.c) (𝓝 yL))
    (hdR : Tendsto F.meanD (𝓝[≥] F.c) (𝓝 dR)) (hdL : Tendsto F.meanD (𝓝[<] F.c) (𝓝 dL)) :
    (yR - yL) / (dR - dL) = F.y1c F.c - F.y0c F.c := by
  rw [tendsto_nhds_unique hyR (tendsto_meanY_right hc), tendsto_nhds_unique hyL
    (tendsto_meanY_left hc), tendsto_nhds_unique hdR (tendsto_meanD_right hc),
    tendsto_nhds_unique hdL (tendsto_meanD_left hc), div_eq_iff (by simpa using hπ.ne')]
  ring

/-- **Witness.** A fuzzy design with a quarter always-takers, a quarter
never-takers and half compliers, whose effect at the cutoff is `3`. All
hypotheses of `fuzzy_rd` hold, the shares are probabilities, and the jump ratio
equals `3`. -/
noncomputable def example₁ : FuzzyRD where
  c := 0
  πa := fun _ => 1 / 4
  πn := fun _ => 1 / 4
  πc := fun _ => 1 / 2
  ya := fun _ => 1
  yn := fun _ => 0
  y0c := fun _ => 0
  y1c := fun _ => 3

theorem example₁_witness :
    example₁.IsProb ∧ example₁.Continuous' ∧ 0 < example₁.πc example₁.c ∧
      example₁.y1c example₁.c - example₁.y0c example₁.c = 3 ∧
      ∃ yR yL dR dL : ℝ,
        Tendsto example₁.meanY (𝓝[≥] example₁.c) (𝓝 yR) ∧
        Tendsto example₁.meanY (𝓝[<] example₁.c) (𝓝 yL) ∧
        Tendsto example₁.meanD (𝓝[≥] example₁.c) (𝓝 dR) ∧
        Tendsto example₁.meanD (𝓝[<] example₁.c) (𝓝 dL) ∧
        yR - yL = 3 / 2 ∧ (yR - yL) / (dR - dL) = 3 := by
  have hc : example₁.Continuous' := ⟨continuousAt_const, continuousAt_const, continuousAt_const,
    continuousAt_const, continuousAt_const, continuousAt_const, continuousAt_const⟩
  refine ⟨fun x => by norm_num [example₁], hc, by norm_num [example₁], by norm_num [example₁],
    _, _, _, _, tendsto_meanY_right hc, tendsto_meanY_left hc, tendsto_meanD_right hc,
    tendsto_meanD_left hc, by norm_num [example₁], by norm_num [example₁]⟩

end FuzzyRD

end Econ.Causal.RD
