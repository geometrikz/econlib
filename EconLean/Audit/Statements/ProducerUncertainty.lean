/-
# Frozen statements: producer theory (MWG Ch. 5) and uncertainty (MWG Ch. 6)

Headline statements of `Producer/*.lean` and `Uncertainty/*.lean`, copied
after they passed the two-round adversarial review recorded in
`Audit/REVIEW-producer-uncertainty.md`. Each is closed by the library
theorem, so if a library statement is ever weakened this file stops
compiling. Stand-in for `leanprover/comparator` (PLAN.md §5). Do not edit a
statement here without a new review.
-/
module

public import EconLean.Producer.Aggregation
public import EconLean.Producer.Cost
public import EconLean.Uncertainty.VNM
public import EconLean.Uncertainty.Pratt
public import EconLean.Uncertainty.StochasticDominance

@[expose] public section

-- Every proof here is the uniform `apply <library theorem> <;> assumption`,
-- so the tactic-style linters are silenced for this audit file only.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace Econ.Audit

open Filter Topology Set Econ Econ.SimpleLottery

variable {ι : Type*} [Fintype ι] {Y : Set (ι → ℝ)} {f : (ι → ℝ) → ℝ}
  {C : Type*} [Fintype C] {J : Type*} [Fintype J] {Ys : J → Set (ι → ℝ)} {p : ι → ℝ}

theorem frozen_Additive_constantReturns_and_convex {Y : Set (ι → ℝ)} (hA : Additive Y)
    (hN : NonincreasingReturns Y) : ConstantReturns Y ∧ Convex ℝ Y := by
  apply Econ.Additive.constantReturns_and_convex <;> assumption

theorem frozen_convexOn_profit (hY : Y.Nonempty) : ConvexOn ℝ (profitDomain Y) (profit Y) := by
  apply Econ.convexOn_profit <;> assumption

theorem frozen_law_of_supply {p p' y y' : ι → ℝ} (hy : y ∈ supply Y p) (hy' : y' ∈ supply Y p') :
    0 ≤ cost (p - p') (y - y') := by
  apply Econ.law_of_supply <;> assumption

theorem frozen_hotelling {p y : ι → ℝ} (hy : y ∈ supply Y p)
    (hb : ∀ᶠ q in 𝓝 p, q ∈ profitDomain Y) {P' : (ι → ℝ) →L[ℝ] ℝ}
    (hP : HasFDerivAt (profit Y) P' p) : ∀ δ, P' δ = cost δ y := by
  apply Econ.hotelling <;> assumption

theorem frozen_supply_subsingleton [DecidableEq ι] {p : ι → ℝ}
    (hb : ∀ᶠ q in 𝓝 p, q ∈ profitDomain Y) {P' : (ι → ℝ) →L[ℝ] ℝ}
    (hP : HasFDerivAt (profit Y) P' p) : (supply Y p).Subsingleton := by
  apply Econ.supply_subsingleton <;> assumption

theorem frozen_berge_supply (hne : Y.Nonempty) (hK : IsCompact Y) :
    Continuous (profit Y) ∧ (∀ p, (supply Y p).Nonempty ∧ IsCompact (supply Y p)) ∧
      UpperHemicontinuous (supply Y) := by
  apply Econ.berge_supply <;> assumption

theorem frozen_costFunction_crs (hf : ∀ t : ℝ, 0 < t → ∀ z, 0 ≤ z → f (t • z) = t * f z)
    (w : ι → ℝ) {q : ℝ} (hq : 0 < q) : costFunction f w q = q * costFunction f w 1 := by
  apply Econ.costFunction_crs <;> assumption

theorem frozen_shephard_cost [DecidableEq ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i) {q : ℝ} {z : ι → ℝ}
    (hz : z ∈ factorDemand f w q) {C' : (ι → ℝ) →L[ℝ] ℝ}
    (hC : HasFDerivAt (fun w' => costFunction f w' q) C' w) (j : ι) :
    C' (Pi.single j 1) = z j := by
  apply Econ.shephard_cost <;> assumption

theorem frozen_factorDemand_of_profitMax {p : ℝ} (hp : 0 ≤ p) {w z : ι → ℝ} (hz0 : 0 ≤ z)
    (hmax : ∀ z', 0 ≤ z' → p * f z' - cost w z' ≤ p * f z - cost w z) :
    z ∈ factorDemand f w (f z) := by
  apply Econ.factorDemand_of_profitMax <;> assumption

theorem frozen_supply_aggregate [DecidableEq J] (y : ι → ℝ) :
    y ∈ supply (aggregate Ys) p ↔ ∃ ys : J → ι → ℝ, (∀ j, ys j ∈ supply (Ys j) p) ∧ y = ∑ j, ys j := by
  apply Econ.supply_aggregate <;> assumption

theorem frozen_profit_aggregate (hne : ∀ j, (Ys j).Nonempty)
    (hb : ∀ j, BddAbove ((fun y => cost p y) '' Ys j)) :
    profit (aggregate Ys) p = ∑ j, profit (Ys j) p := by
  apply Econ.profit_aggregate <;> assumption

theorem frozen_efficient_of_mem_supply {p y : ι → ℝ} (hp : ∀ i, 0 < p i) (hy : y ∈ supply Y p) :
    Efficient Y y := by
  apply Econ.efficient_of_mem_supply <;> assumption

theorem frozen_exists_price_of_efficient [Nonempty ι] (hY : Convex ℝ Y) {y : ι → ℝ} (hy : Efficient Y y) :
    ∃ p : ι → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ y ∈ supply Y p := by
  apply Econ.exists_price_of_efficient <;> assumption

theorem frozen_vnm_theorem (R : (C → ℝ) → (C → ℝ) → Prop) :
    VNMAxioms R ↔ ∃ u : C → ℝ, HasEURepresentation R u := by
  apply Econ.vnm_theorem <;> assumption

theorem frozen_HasEURepresentation_unique [DecidableEq C] {R : (C → ℝ) → (C → ℝ) → Prop} {u v : C → ℝ}
    (hu : HasEURepresentation R u) (hv : HasEURepresentation R v) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ c, v c = a * u c + b := by
  apply Econ.HasEURepresentation.unique <;> assumption

theorem frozen_riskAverseOn_iff_concaveOn {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I) :
    RiskAverseOn u I ↔ ConcaveOn ℝ I u := by
  apply Econ.riskAverseOn_iff_concaveOn <;> assumption

theorem frozen_riskAverse_iff_certaintyEquivalent_le_mean {u : ℝ → ℝ} (hc : Continuous u)
    (hm : StrictMono u) :
    RiskAverseOn u univ ↔ ∀ F c, IsCertaintyEquivalent u F c → c ≤ F.mean := by
  apply Econ.riskAverse_iff_certaintyEquivalent_le_mean <;> assumption

theorem frozen_moreRiskAverse_iff {u₁ u₂ : ℝ → ℝ} (hc₁ : Continuous u₁) (hm₁ : StrictMono u₁)
    (hc₂ : Continuous u₂) (hm₂ : StrictMono u₂) :
    MoreRiskAverse u₂ u₁ ↔ ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (range u₁) ∧
      ConcaveOn ℝ (range u₁) ψ ∧ ∀ x, u₂ x = ψ (u₁ x) := by
  apply Econ.moreRiskAverse_iff <;> assumption

theorem frozen_riskAverse_iff_arrowPratt_nonneg {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (hpos : ∀ x, 0 < deriv u x) :
    RiskAverseOn u univ ↔ ∀ x, 0 ≤ arrowPratt u x := by
  apply Econ.riskAverse_iff_arrowPratt_nonneg <;> assumption

theorem frozen_SimpleLottery_fosd_iff_cdf_le (F G : SimpleLottery) : FOSD F G ↔ ∀ t, F.cdf t ≤ G.cdf t := by
  apply Econ.SimpleLottery.fosd_iff_cdf_le <;> assumption

theorem frozen_SimpleLottery_sosd_of_meanPreservingSpread {G F : SimpleLottery}
    (h : IsMeanPreservingSpread G F) : SOSD F G := by
  apply Econ.SimpleLottery.sosd_of_meanPreservingSpread <;> assumption

theorem frozen_SimpleLottery_SOSD_shortfall_le {F G : SimpleLottery} (h : SOSD F G) (t : ℝ) :
    F.expect (fun x => max (t - x) 0) ≤ G.expect (fun x => max (t - x) 0) := by
  apply Econ.SimpleLottery.SOSD.shortfall_le <;> assumption

theorem frozen_SimpleLottery_expect_shortfall_eq_integral_cdf (F : SimpleLottery) {a t : ℝ}
    (ha : ∀ x ∈ F.prob.support, a < x) (hat : a ≤ t) :
    F.expect (fun x => max (t - x) 0) = ∫ s in a..t, F.cdf s := by
  apply Econ.SimpleLottery.expect_shortfall_eq_integral_cdf <;> assumption

theorem frozen_arrowPratt_le_iff_moreRiskAverse {u₁ u₂ : ℝ → ℝ}
    (hd₁ : Differentiable ℝ u₁) (hd₁' : Differentiable ℝ (deriv u₁))
    (hd₂ : Differentiable ℝ u₂) (hd₂' : Differentiable ℝ (deriv u₂))
    (hp₁ : ∀ x, 0 < deriv u₁ x) (hp₂ : ∀ x, 0 < deriv u₂ x) :
    (∀ x, arrowPratt u₁ x ≤ arrowPratt u₂ x) ↔ MoreRiskAverse u₂ u₁ :=
  arrowPratt_le_iff_moreRiskAverse hd₁ hd₁' hd₂ hd₂' hp₁ hp₂

theorem frozen_concaveOn_costFunction {q : ℝ} (hfeas : ∃ z, 0 ≤ z ∧ q ≤ f z) :
    ConcaveOn ℝ {w : ι → ℝ | 0 ≤ w} (fun w => costFunction f w q) := by
  apply Econ.concaveOn_costFunction <;> assumption

theorem frozen_profit_aggregate_of_supply (h : ∀ j, (supply (Ys j) p).Nonempty) :
    profit (aggregate Ys) p = ∑ j, profit (Ys j) p := by
  apply Econ.profit_aggregate_of_supply <;> assumption

end Econ.Audit
