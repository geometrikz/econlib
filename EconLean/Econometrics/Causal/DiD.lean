/-
# Difference-in-differences: the 2×2 design

Card–Krueger (1994); Angrist–Pischke (2009) §5.2; Roth, Sant'Anna, Bilinski,
Poe (2023), "What's trending in difference-in-differences?", *Journal of
Econometrics* 235, §2 (Assumptions PT and NA, Proposition / eq. (3)).

**The economics.** Two groups (treated `G = 1`, control `G = 0`) and two
periods (pre `t = 0`, post `t = 1`). Only the treated group is treated, and only
in the post period. Each unit has potential outcomes in each period:
`Y₀ₜ` (never treated) and `Y₁ₜ` (treated from period 1 on).

* **Observed outcomes.** `Y_pre = G·Y₁,pre + (1 − G)·Y₀,pre`,
  `Y_post = G·Y₁,post + (1 − G)·Y₀,post`.
* **No anticipation (NA).** Treatment has no effect before it starts. We use the
  weakest form needed, on average among the treated:
  `E[Y₁,pre | G=1] = E[Y₀,pre | G=1]` (Roth et al. state it unit by unit).
* **Parallel trends (PT).** Absent treatment, average outcomes would have
  moved in parallel: `E[Y₀,post − Y₀,pre | G=1] = E[Y₀,post − Y₀,pre | G=0]`.
* **Target.** `ATT = E[Y₁,post − Y₀,post | G=1]`.

**Theorem.** In general, `DiD = ATT + (trend gap) + (anticipation effect)`;
under PT and NA, `DiD = ATT`.

Treatment status in the population is a random variable `G : Ω → Bool`, so this
is the "panel" (or repeated cross-section with stable composition) version.

**Junk values.** The theorems need no positivity of `P(G = 1)` or `P(G = 0)`:
the identities are algebraic. On a null group every conditional mean is Lean's
junk value `0` on both sides, so the statements stay true but say nothing; the
witness `Witness.did_witness` has both groups of probability `1/2`.
-/
module

public import EconLean.Econometrics.Causal.PotentialOutcomes

@[expose] public section

namespace Econ.Causal

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A 2×2 difference-in-differences population: group indicator and potential
outcomes in the pre and post periods. -/
structure DiD2x2 (Ω : Type*) where
  /-- treated group indicator -/
  G : Ω → Bool
  /-- untreated potential outcome, pre period -/
  Y0pre : Ω → ℝ
  /-- treated potential outcome, pre period (only differs under anticipation) -/
  Y1pre : Ω → ℝ
  /-- untreated potential outcome, post period -/
  Y0post : Ω → ℝ
  /-- treated potential outcome, post period -/
  Y1post : Ω → ℝ

namespace DiD2x2

variable (S : DiD2x2 Ω) (μ : Measure Ω)

/-- Observed pre-period outcome. -/
def Ypre : Ω → ℝ := observed S.G S.Y0pre S.Y1pre

/-- Observed post-period outcome. -/
def Ypost : Ω → ℝ := observed S.G S.Y0post S.Y1post

/-- The DiD estimand
`(E[Y_post | G=1] − E[Y_pre | G=1]) − (E[Y_post | G=0] − E[Y_pre | G=0])`. -/
noncomputable def did : ℝ :=
  (condMean μ S.Ypost (treated S.G) - condMean μ S.Ypre (treated S.G))
    - (condMean μ S.Ypost (untreated S.G) - condMean μ S.Ypre (untreated S.G))

/-- ATT in the post period. -/
noncomputable def attPost : ℝ := att μ S.G S.Y0post S.Y1post

/-- Untreated trend in a group: `E[Y₀,post − Y₀,pre | s]`. -/
noncomputable def trend (s : Set Ω) : ℝ := condMean μ (fun ω => S.Y0post ω - S.Y0pre ω) s

/-- Parallel trends. -/
def ParallelTrends : Prop := S.trend μ (treated S.G) = S.trend μ (untreated S.G)

/-- No anticipation, on average among the treated. -/
def NoAnticipation : Prop :=
  condMean μ S.Y1pre (treated S.G) = condMean μ S.Y0pre (treated S.G)

/-- Integrability of all potential outcomes. -/
structure Integrable' : Prop where
  Y0pre : Integrable S.Y0pre μ
  Y1pre : Integrable S.Y1pre μ
  Y0post : Integrable S.Y0post μ
  Y1post : Integrable S.Y1post μ

variable {S μ}

/-- **DiD bias decomposition.** With no assumptions beyond integrability:
`DiD = ATT + (trend among treated − trend among controls) − anticipation`,
where anticipation is `E[Y₁,pre − Y₀,pre | G=1]`. -/
theorem did_eq (hG : Measurable S.G) (hi : S.Integrable' μ) :
    S.did μ = S.attPost μ + (S.trend μ (treated S.G) - S.trend μ (untreated S.G))
      - (condMean μ S.Y1pre (treated S.G) - condMean μ S.Y0pre (treated S.G)) := by
  rw [did, attPost, att, trend, trend, Ypost, Ypre, condMean_observed_treated hG,
    condMean_observed_treated hG, condMean_observed_untreated hG,
    condMean_observed_untreated hG, condMean_sub _ hi.Y1post hi.Y0post,
    condMean_sub _ hi.Y0post hi.Y0pre, condMean_sub _ hi.Y0post hi.Y0pre]
  ring

/-- **DiD identifies the ATT** under parallel trends and no anticipation
(Roth et al. 2023, §2; Angrist–Pischke §5.2). -/
theorem did_eq_att (hG : Measurable S.G) (hi : S.Integrable' μ) (hpt : S.ParallelTrends μ)
    (hna : S.NoAnticipation μ) : S.did μ = S.attPost μ := by
  rw [did_eq hG hi, show S.trend μ (treated S.G) = S.trend μ (untreated S.G) from hpt,
    show condMean μ S.Y1pre (treated S.G) = condMean μ S.Y0pre (treated S.G) from hna]
  ring

end DiD2x2

end Econ.Causal
