/-
# The Myerson–Satterthwaite theorem (Bayesian bilateral trade)

MWG Prop. 23.E.1 / §23.E; Myerson & Satterthwaite (1983); Krishna, *Auction Theory*, Ch. 5.
A buyer with value `v ~ μB` and a seller with cost `c ~ μS`, independent, both distributions
supported in `[a, b]` and atomless. A direct mechanism (`TradeMechanism`) gives a trade
probability `x v c`, a buyer payment `tB v c` and a seller receipt `tS v c`. Interim
quantities average over the other trader's type:

* buyer: `QB v = E_c[x v c]`, `PB v = E_c[tB v c]`, payoff `v QB v − PB v`;
* seller: `QS c = E_v[x v c]`, `RS c = E_v[tS v c]`, payoff `RS c − c QS c`.

Main result, `myerson_satterthwaite`: if there are positive expected gains from trade,
`E[(v − c)⁺] > 0`, no mechanism is simultaneously
* **ex post efficient** (trade iff `c < v`, ties free);
* **Bayesian incentive compatible** for both traders (at every type in `[a, b]`);
* **interim individually rational** for both traders; and
* **ex ante budget balanced**: the buyer's expected payment covers the seller's expected
  receipt, `E_c[RS c] ≤ E_v[PB v]`.
`myerson_satterthwaite_expost` derives the ex ante condition from ex post budget balance
`tB = tS` (with integrable transfers).

Scope. Both traders' type spaces are the whole interval `[a, b]`: efficiency, incentive
compatibility and individual rationality are imposed at every type in `[a, b]`, while the
distributions are only required to be supported in `[a, b]`. In MWG's setting (positive
densities on a common interval, so full support) this is exactly Prop. 23.E.1. Without full
support the theorem remains true but can rule out a mechanism only because of constraints at
types that never occur: with `v ~ U[2,3]`, `c ~ U[0,1]` and `[a, b] = [0, 3]` the posted
price `1.5` works for all types that occur. A version with constraints only on the supports
(and an overlap condition) is not formalized.

Proof (Krishna's VCG comparison). By Myerson's lemma (`Mechanism/Myerson.lean`) an IC
mechanism's interim payments are pinned down by the allocation rule up to the payoff of the
worst type. Under efficiency the allocation rule is that of the VCG (pivot) mechanism, in which
the buyer pays the seller's cost and the seller receives the buyer's value whenever they
trade, and the worst types get zero. So any efficient IC and IR mechanism collects at most the
VCG buyer payments and pays at least the VCG seller receipts; and VCG runs an expected deficit
of exactly `E[(v − c)⁺] > 0`.
-/
module

public import EconLean.Mechanism.Myerson
public import EconLean.Mechanism.BilateralTrade
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

namespace Econ

open MeasureTheory Set Filter

lemma norm_le_of_mem_Icc {a b x : ℝ} (hx : x ∈ Icc a b) : ‖x‖ ≤ |a| + |b| := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hx.1]
  · linarith [le_abs_self b, abs_nonneg a, hx.2]

section VCG

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
  {a b : ℝ}

lemma integrable_ite_one (hf : Measurable f) (v : ℝ) :
    Integrable (fun c => if f c < v then (1 : ℝ) else 0) μ := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun c => ?_)
  · exact (Measurable.ite (measurableSet_lt hf measurable_const) measurable_const
      measurable_const).aestronglyMeasurable
  · split_ifs <;> simp

lemma integrable_ite_self (hf : Measurable f) (hsupp : ∀ᵐ c ∂μ, f c ∈ Icc a b) (v : ℝ) :
    Integrable (fun c => if f c < v then f c else 0) μ := by
  refine Integrable.of_bound ?_ (|a| + |b|) (hsupp.mono fun c hc => ?_)
  · exact (Measurable.ite (measurableSet_lt hf measurable_const) hf
      measurable_const).aestronglyMeasurable
  · split_ifs
    · exact norm_le_of_mem_Icc hc
    · simp only [norm_zero]; positivity

/-- **The interim VCG (pivot) mechanism is IC**: if the other side's "price" is `f c`,
trading exactly when `f c < v` and paying `f c` is incentive compatible at the interim
stage. -/
lemma vcg_isICMech (hf : Measurable f) (hsupp : ∀ᵐ c ∂μ, f c ∈ Icc a b) :
    IsICMech (fun v => ∫ c, (if f c < v then (1 : ℝ) else 0) ∂μ)
      (fun v => ∫ c, (if f c < v then f c else 0) ∂μ) a b := by
  intro θ _ r _
  have hI : ∀ s, Integrable (fun c => if f c < s then θ - f c else 0) μ := fun s =>
    (((integrable_ite_one hf s).const_mul θ).sub (integrable_ite_self hf hsupp s)).congr
      (Eventually.of_forall fun c => by simp only [Pi.sub_apply]; split_ifs <;> ring)
  have e : ∀ s, θ * (∫ c, (if f c < s then (1 : ℝ) else 0) ∂μ) -
      ∫ c, (if f c < s then f c else 0) ∂μ = ∫ c, (if f c < s then θ - f c else 0) ∂μ := by
    intro s
    rw [← integral_const_mul, ← integral_sub ((integrable_ite_one hf s).const_mul θ)
      (integrable_ite_self hf hsupp s)]
    congr 1; funext c; split_ifs <;> ring
  simp only
  rw [e, e]
  refine integral_mono (hI r) (hI θ) fun c => ?_
  simp only
  split_ifs with h1 h2 h2 <;> linarith

/-- **Payments are those of VCG, up to the worst type's rent.** If a mechanism `(q, p)` is IC on
`[a, b]` and its allocation is that of VCG, then each type pays the VCG payment minus the
rent `U(a)` of the worst type. -/
lemma payment_eq_vcg (hf : Measurable f) (hsupp : ∀ᵐ c ∂μ, f c ∈ Icc a b) {q p : ℝ → ℝ}
    (hq : ∀ v ∈ Icc a b, q v = ∫ c, (if f c < v then (1 : ℝ) else 0) ∂μ)
    (hIC : IsICMech q p a b) :
    ∀ v ∈ Icc a b, p v = ∫ c, (if f c < v then f c else 0) ∂μ - infoRent q p a := by
  intro v hv
  set P := fun v => ∫ c, (if f c < v then f c else 0) ∂μ
  have hIC' : IsICMech q P a b := by
    intro θ hθ r hr
    rw [hq θ hθ, hq r hr]
    exact vcg_isICMech hf hsupp θ hθ r hr
  have h1 := (myerson_ic_iff.1 hIC).2 v hv
  have h2 := (myerson_ic_iff.1 hIC').2 v hv
  have ha : a ∈ Icc a b := ⟨le_rfl, hv.1.trans hv.2⟩
  have hqa : q a = 0 := by
    rw [hq a ha]
    exact integral_eq_zero_of_ae (hsupp.mono fun c hc => by simp [not_lt.2 hc.1])
  have hPa : P a = 0 :=
    integral_eq_zero_of_ae (hsupp.mono fun c hc => by simp [not_lt.2 hc.1])
  simp only [infoRent, hqa, hPa, mul_zero, sub_zero] at h1 h2 ⊢
  linarith

end VCG

namespace TradeMechanism

variable (M : TradeMechanism) (μB μS : Measure ℝ)

/-- Buyer's interim trade probability. -/
noncomputable def QB (v : ℝ) : ℝ := ∫ c, M.x v c ∂μS
/-- Buyer's interim expected payment. -/
noncomputable def PB (v : ℝ) : ℝ := ∫ c, M.tB v c ∂μS
/-- Seller's interim trade probability. -/
noncomputable def QS (c : ℝ) : ℝ := ∫ v, M.x v c ∂μB
/-- Seller's interim expected receipt. -/
noncomputable def RS (c : ℝ) : ℝ := ∫ v, M.tS v c ∂μB

/-- **Bayesian incentive compatibility** for both traders, at every type in `[a, b]`. -/
def IsBIC (a b : ℝ) : Prop :=
  IsICMech (M.QB μS) (M.PB μS) a b ∧
    ∀ c ∈ Icc a b, ∀ c' ∈ Icc a b,
      M.RS μB c' - c * M.QS μB c' ≤ M.RS μB c - c * M.QS μB c

/-- **Interim individual rationality** for both traders, at every type in `[a, b]`. -/
def IsInterimIR (a b : ℝ) : Prop :=
  (∀ v ∈ Icc a b, 0 ≤ v * M.QB μS v - M.PB μS v) ∧
    ∀ c ∈ Icc a b, 0 ≤ M.RS μB c - c * M.QS μB c

/-- **Ex ante (weak) budget balance**: the buyer's expected payment covers the seller's
expected receipt. -/
def IsExAnteBudgetBalanced : Prop := ∫ c, M.RS μB c ∂μS ≤ ∫ v, M.PB μS v ∂μB

end TradeMechanism

open TradeMechanism

/-- **Myerson–Satterthwaite** (MWG Prop. 23.E.1). With independent atomless types supported in
`[a, b]` and positive expected gains from trade, no bilateral trade mechanism is ex post
efficient, Bayesian incentive compatible, interim individually rational and ex ante budget
balanced, where the type space of each trader is all of `[a, b]` (see the module docstring:
this matches MWG when the distributions have full support on `[a, b]`). -/
theorem myerson_satterthwaite {a b : ℝ} (μB μS : Measure ℝ) [IsProbabilityMeasure μB]
    [IsProbabilityMeasure μS] (hB : ∀ᵐ v ∂μB, v ∈ Icc a b) (hS : ∀ᵐ c ∂μS, c ∈ Icc a b)
    (hBna : ∀ v, μB {v} = 0) (hSna : ∀ c, μS {c} = 0)
    (hgain : 0 < ∫ v, ∫ c, (if c < v then v - c else 0) ∂μS ∂μB)
    (M : TradeMechanism) (he : M.IsEfficient a b) (hIC : M.IsBIC μB μS a b)
    (hIR : M.IsInterimIR μB μS a b) (hBB : M.IsExAnteBudgetBalanced μB μS) : False := by
  -- `a ≤ b`, since the type distributions live on `[a, b]`.
  obtain ⟨v₀, hv₀⟩ := hB.exists
  have hab : a ≤ b := hv₀.1.trans hv₀.2
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  -- Buyer side: interim allocation is VCG's, so payments are VCG's minus `U_B(a)`.
  have hqB : ∀ v ∈ Icc a b, M.QB μS v = ∫ c, (if id c < v then (1 : ℝ) else 0) ∂μS := by
    intro v hv
    refine integral_congr_ae ?_
    filter_upwards [hS, measure_eq_zero_iff_ae_notMem.1 (hSna v)] with c hc hne
    rcases lt_or_gt_of_ne (show c ≠ v from hne) with h | h
    · simp [(he v hv c hc).1 h, h]
    · simp [(he v hv c hc).2 h, not_lt.2 h.le]
  have hPB := payment_eq_vcg (f := id) measurable_id hS hqB hIC.1
  set UB := infoRent (M.QB μS) (M.PB μS) a
  have hUB : 0 ≤ UB := hIR.1 a haI
  -- Seller side, written as a buyer with type `θ = −c`.
  set q' : ℝ → ℝ := fun θ => M.QS μB (-θ)
  set p' : ℝ → ℝ := fun θ => -M.RS μB (-θ)
  have hmem : ∀ θ ∈ Icc (-b) (-a), -θ ∈ Icc a b := fun θ hθ =>
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hIC' : IsICMech q' p' (-b) (-a) := by
    intro θ hθ r hr
    have := hIC.2 (-θ) (hmem θ hθ) (-r) (hmem r hr)
    simp only [q', p', neg_mul] at this ⊢
    linarith
  have hqS : ∀ θ ∈ Icc (-b) (-a), q' θ = ∫ v, (if -v < θ then (1 : ℝ) else 0) ∂μB := by
    intro θ hθ
    refine integral_congr_ae ?_
    filter_upwards [hB, measure_eq_zero_iff_ae_notMem.1 (hBna (-θ))] with v hv hne
    rcases lt_or_gt_of_ne (show v ≠ -θ from hne) with h | h
    · simp [(he v hv (-θ) (hmem θ hθ)).2 h, show ¬ -v < θ by linarith]
    · simp [(he v hv (-θ) (hmem θ hθ)).1 h, show -v < θ by linarith]
  have hsuppS : ∀ᵐ v ∂μB, -v ∈ Icc (-b) (-a) :=
    hB.mono fun v hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hRS0 := payment_eq_vcg (f := fun v => -v) measurable_neg hsuppS hqS hIC'
  set US := infoRent q' p' (-b)
  have hUS : 0 ≤ US := by
    have := hIR.2 b hbI
    simp only [US, infoRent, q', p', neg_neg]
    linarith
  have hRS : ∀ c ∈ Icc a b, M.RS μB c = ∫ v, (if c < v then v else 0) ∂μB + US := by
    intro c hc
    have h := hRS0 (-c) ⟨by linarith [hc.2], by linarith [hc.1]⟩
    simp only [p', neg_neg] at h
    have : ∫ v, (if -v < -c then -v else 0) ∂μB = -∫ v, (if c < v then v else 0) ∂μB := by
      rw [← integral_neg]
      congr 1; funext v
      by_cases hcv : c < v
      · simp [hcv]
      · simp [hcv, show ¬ -v < -c by linarith]
    linarith
  -- Integrability on the product.
  have hbd : ∀ x ∈ Icc a b, ‖x‖ ≤ |a| + |b| := fun x hx => norm_le_of_mem_Icc hx
  have hF : Integrable (fun p : ℝ × ℝ => if p.2 < p.1 then p.2 else 0) (μB.prod μS) := by
    refine Integrable.of_bound ?_ (|a| + |b|) ?_
    · exact (Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_snd
        measurable_const).aestronglyMeasurable
    · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hS] with p hp
      split_ifs
      · exact hbd _ hp
      · simp only [norm_zero]; positivity
  have hG : Integrable (fun p : ℝ × ℝ => if p.2 < p.1 then p.1 else 0) (μB.prod μS) := by
    refine Integrable.of_bound ?_ (|a| + |b|) ?_
    · exact (Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_fst
        measurable_const).aestronglyMeasurable
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hB] with p hp
      split_ifs
      · exact hbd _ hp
      · simp only [norm_zero]; positivity
  have hG' : Integrable (fun p : ℝ × ℝ => if p.1 < p.2 then p.2 else 0) (μS.prod μB) :=
    hG.swap
  -- Expected payments.
  have hEPB : ∫ v, M.PB μS v ∂μB = ∫ v, ∫ c, (if c < v then c else 0) ∂μS ∂μB - UB := by
    simp only [id] at hPB
    rw [integral_congr_ae (hB.mono fun v hv => hPB v hv),
      integral_sub hF.integral_prod_left (integrable_const _), integral_const]
    simp
  have hERS : ∫ c, M.RS μB c ∂μS = ∫ v, ∫ c, (if c < v then v else 0) ∂μS ∂μB + US := by
    have hswap := integral_integral_swap (μ := μS) (ν := μB)
      (f := fun c v => if c < v then v else 0) hG'
    rw [← hswap, integral_congr_ae (hS.mono fun c hc => hRS c hc),
      integral_add hG'.integral_prod_left (integrable_const _), integral_const]
    simp
  -- VCG's expected deficit is the expected gain from trade.
  have hdef : ∫ v, ∫ c, (if c < v then c else 0) ∂μS ∂μB -
      ∫ v, ∫ c, (if c < v then v else 0) ∂μS ∂μB =
        -∫ v, ∫ c, (if c < v then v - c else 0) ∂μS ∂μB := by
    rw [← integral_sub hF.integral_prod_left hG.integral_prod_left, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [← integral_sub, ← integral_neg]
    · congr 1; funext c; split_ifs <;> ring
    · exact integrable_ite_self (f := id) measurable_id hS v
    · exact (integrable_ite_one (μ := μS) (f := id) measurable_id v).const_mul v |>.congr
        (Eventually.of_forall fun c => by simp only [id]; split_ifs <;> ring)
  have := hBB
  unfold IsExAnteBudgetBalanced at this
  rw [hEPB, hERS] at this
  linarith

/-- **Myerson–Satterthwaite with ex post budget balance.** If the seller receives exactly
what the buyer pays at every report profile (`tB = tS`, with integrable transfers), the
mechanism is ex ante budget balanced, so the impossibility applies. -/
theorem TradeMechanism.isExAnteBudgetBalanced_of_expost (M : TradeMechanism) (μB μS : Measure ℝ)
    [IsProbabilityMeasure μB] [IsProbabilityMeasure μS] (hBB : ∀ v c, M.tB v c = M.tS v c)
    (hint : Integrable (fun p : ℝ × ℝ => M.tB p.1 p.2) (μB.prod μS)) :
    M.IsExAnteBudgetBalanced μB μS := by
  unfold IsExAnteBudgetBalanced RS PB
  have hint' : Integrable (Function.uncurry fun c v => M.tS v c) (μS.prod μB) := by
    have := hint.swap
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, hBB]
  rw [integral_integral_swap hint']
  simp only [hBB, le_refl]

/-- **Myerson–Satterthwaite, ex post budget-balanced form.** -/
theorem myerson_satterthwaite_expost {a b : ℝ} (μB μS : Measure ℝ) [IsProbabilityMeasure μB]
    [IsProbabilityMeasure μS] (hB : ∀ᵐ v ∂μB, v ∈ Icc a b) (hS : ∀ᵐ c ∂μS, c ∈ Icc a b)
    (hBna : ∀ v, μB {v} = 0) (hSna : ∀ c, μS {c} = 0)
    (hgain : 0 < ∫ v, ∫ c, (if c < v then v - c else 0) ∂μS ∂μB)
    (M : TradeMechanism) (he : M.IsEfficient a b) (hIC : M.IsBIC μB μS a b)
    (hIR : M.IsInterimIR μB μS a b) (hBB : ∀ v c, M.tB v c = M.tS v c)
    (hint : Integrable (fun p : ℝ × ℝ => M.tB p.1 p.2) (μB.prod μS)) : False :=
  myerson_satterthwaite μB μS hB hS hBna hSna hgain M he hIC hIR
    (M.isExAnteBudgetBalanced_of_expost μB μS hBB hint)

/-- **The distributional hypotheses are satisfiable**: uniform values and costs on `[0, 1]`
are probability distributions supported in `[0, 1]`, atomless, with expected gains from trade
`E[(v − c)⁺] = 1/6 > 0`. -/
theorem uniform_satisfies_hypotheses : IsProbabilityMeasure (volume.restrict (Icc (0:ℝ) 1)) ∧
    (∀ᵐ v ∂(volume.restrict (Icc (0:ℝ) 1)), v ∈ Icc (0:ℝ) 1) ∧
    (∀ v, volume.restrict (Icc (0:ℝ) 1) {v} = 0) ∧
    0 < ∫ v, ∫ c, (if c < v then v - c else 0) ∂(volume.restrict (Icc (0:ℝ) 1))
      ∂(volume.restrict (Icc (0:ℝ) 1)) := by
  refine ⟨⟨by simp⟩, ae_restrict_mem measurableSet_Icc, fun v => ?_, ?_⟩
  · rw [Measure.restrict_apply' measurableSet_Icc]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)
  · have hin : ∀ v ∈ Icc (0:ℝ) 1,
        ∫ c, (if c < v then v - c else 0) ∂(volume.restrict (Icc (0:ℝ) 1)) = v ^ 2 / 2 := by
      intro v hv
      have : (fun c : ℝ => if c < v then v - c else 0) = (Iio v).indicator (fun c => v - c) := by
        funext c; simp [Set.indicator, Set.mem_Iio]
      rw [this, setIntegral_indicator measurableSet_Iio]
      have hset : Icc (0:ℝ) 1 ∩ Iio v = Ico 0 v := by
        ext c; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]; constructor
        · rintro ⟨⟨h0, -⟩, h⟩; exact ⟨h0, h⟩
        · rintro ⟨h0, h⟩; exact ⟨⟨h0, by linarith [hv.2]⟩, h⟩
      rw [hset, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hv.1]
      rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
        intervalIntegral.integral_const, integral_id]
      simp only [smul_eq_mul, sub_zero]
      ring
    rw [integral_congr_ae (ae_restrict_mem measurableSet_Icc |>.mono fun v hv => hin v hv),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp [intervalIntegral.integral_div, integral_pow]
    norm_num

end Econ
