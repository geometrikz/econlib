/-
# Frozen statements: partial equilibrium and IO, social choice, bargaining, cooperative games,
# Myerson–Satterthwaite, the first-price auction, DA strategy-proofness, assortative matching

Headline statements of `Partial/*`, `SocialChoice/*`, `Bargaining/Nash`, `Cooperative/*`,
`Mechanism/{MyersonSatterthwaite,FirstPrice}` and `Matching/{StrategyProof,Assortative}`,
copied after the adversarial review recorded in `Audit/REVIEW-partial-social.md`. Each is closed
by the library theorem, so if a library statement is ever weakened this file stops compiling.
Do not edit a statement here without a new review.
-/
module

public import EconLean.Mechanism.MyersonSatterthwaite
public import EconLean.Mechanism.FirstPrice
public import EconLean.Matching.StrategyProof
public import EconLean.Matching.Assortative
public import EconLean.Partial.Externalities
public import EconLean.Partial.PublicGoods
public import EconLean.Partial.Oligopoly
public import EconLean.Partial.Monopoly
public import EconLean.Partial.Salop
public import EconLean.Partial.DiamondParadox
public import EconLean.SocialChoice.May
public import EconLean.SocialChoice.MedianVoter
public import EconLean.Bargaining.Nash
public import EconLean.Cooperative.Shapley
public import EconLean.Cooperative.Core

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Function Finset Set Econ Filter Topology MeasureTheory

theorem frozen_myerson_satterthwaite {a b : ℝ} (μB μS : Measure ℝ) [IsProbabilityMeasure μB]
    [IsProbabilityMeasure μS] (hB : ∀ᵐ v ∂μB, v ∈ Icc a b) (hS : ∀ᵐ c ∂μS, c ∈ Icc a b)
    (hBna : ∀ v, μB {v} = 0) (hSna : ∀ c, μS {c} = 0)
    (hgain : 0 < ∫ v, ∫ c, (if c < v then v - c else 0) ∂μS ∂μB)
    (M : TradeMechanism) (he : M.IsEfficient a b) (hIC : M.IsBIC μB μS a b)
    (hIR : M.IsInterimIR μB μS a b) (hBB : M.IsExAnteBudgetBalanced μB μS) : False :=
  myerson_satterthwaite μB μS hB hS hBna hSna hgain M he hIC hIR hBB

theorem frozen_firstPrice_equilibrium {m : ℕ} (hm : 0 < m) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (b : ℝ) : fpPayoff m v b ≤ fpPayoff m v (fpBid m v) :=
  firstPrice_equilibrium hm hv b

theorem frozen_firstPrice_revenue {m : ℕ} (hm : 0 < m) :
    (m + 1) * ∫ v in (0 : ℝ)..1, fpBid m v * fpWinProb m (fpBid m v) = m / (m + 2) :=
  firstPrice_revenue hm

theorem frozen_daMatching_strategyproof {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W]
    (um um' : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w)) (m : M)
    (hsame : ∀ m'', m'' ≠ m → um' m'' = um m'') :
    ¬ Improves um (daMatching um uw) (daMatching um' uw) m :=
  daMatching_strategyproof um um' uw hum huw m hsame

theorem frozen_becker_pam {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : HasIncreasingDifferences f)
    {x y : Fin n → ℝ} (hx : Monotone x) (hy : Monotone y) (σ : Equiv.Perm (Fin n)) :
    matchingSurplus f x y σ ≤ matchingSurplus f x y 1 :=
  becker_pam hf hx hy σ

theorem frozen_bertrand_isNash_iff {c : ℝ} {x : ℝ → ℝ} (hx : Continuous x) (hanti : Antitone x)
    (hx0 : ∀ p, 0 ≤ x p) (hxc : 0 < x c) (p : Bool → ℝ) :
    IsNash (bertrandProfit c x) p ↔ p = fun _ => c :=
  bertrand_isNash_iff hx hanti hx0 hxc p

theorem frozen_cournot_isEq_iff {I : Type*} [Fintype I] [DecidableEq I] {a b c : ℝ}
    (hb : 0 < b) (hac : c < a) (q : I → ℝ) :
    IsCournotEq a b c q ↔ ∀ i, q i = cournotQ a b c (Fintype.card I) :=
  cournot_isEq_iff hb hac q

theorem frozen_cournot_price_tendsto (a c : ℝ) :
    Tendsto (fun n : ℕ => (a + n * c) / (n + 1)) atTop (𝓝 c) :=
  cournot_price_tendsto a c

theorem frozen_coase_theorem {H : Set ℝ} {φ₁ φ₂ : ℝ → ℝ} {hstar : ℝ} (hH : hstar ∈ H)
    (hmax : ∀ h' ∈ H, φ₁ h' + φ₂ h' ≤ φ₁ hstar + φ₂ hstar) (h₀ : ℝ) (hh₀ : h₀ ∈ H) :
    (∃ T, IsParetoExt H φ₁ φ₂ hstar T ∧ φ₁ h₀ ≤ φ₁ hstar + T ∧ φ₂ h₀ ≤ φ₂ hstar - T) ∧
      ∀ h T, h ∈ H → IsParetoExt H φ₁ φ₂ h T →
        φ₁ h + φ₂ h = φ₁ hstar + φ₂ hstar :=
  coase_theorem hH hmax h₀ hh₀

theorem frozen_competitive_maximizes_surplus {I J : Type*} [Fintype I] [Fintype J]
    {φ : I → ℝ → ℝ} {c : J → ℝ → ℝ} {p : ℝ} {x : I → ℝ}
    {q : J → ℝ} (h : IsPartialEq φ c p x q) (x' : I → ℝ) (q' : J → ℝ) (hx' : ∀ i, 0 ≤ x' i)
    (hq' : ∀ j, 0 ≤ q' j) (hfeas : ∑ i, x' i = ∑ j, q' j) :
    ∑ i, φ i (x' i) - ∑ j, c j (q' j) ≤ ∑ i, φ i (x i) - ∑ j, c j (q j) :=
  competitive_maximizes_surplus h x' q' hx' hq' hfeas

theorem frozen_samuelson_condition {I : Type*} [Fintype I] {φ : I → ℝ → ℝ} {C : ℝ → ℝ} {G : ℝ}
    {φ' : I → ℝ} {C' : ℝ} (hG : IsEfficientLevel φ C G) (hpos : 0 < G)
    (hφ : ∀ i, HasDerivAt (φ i) (φ' i) G) (hC : HasDerivAt C C' G) : ∑ i, φ' i = C' :=
  samuelson_condition hG hpos hφ hC

theorem frozen_lindahl_efficient {I : Type*} [Fintype I] {φ : I → ℝ → ℝ} {c : ℝ} {p : I → ℝ}
    {G : ℝ} (h : IsLindahlEq φ c p G) : IsEfficientLevel φ (fun G => c * G) G :=
  lindahl_efficient h

theorem frozen_voluntary_underprovision {I : Type*} [Fintype I] [DecidableEq I]
    {φ d : I → ℝ → ℝ}
    (hd : ∀ i x, HasDerivAt (φ i) (d i x) x) (hpos : ∀ i x, 0 < d i x)
    (hanti : ∀ i, StrictAnti (d i)) (htwo : 1 < Fintype.card I) {g : I → ℝ}
    (heq : IsVoluntaryEq φ g) (hGpos : 0 < ∑ j, g j) {Gstar : ℝ}
    (hsam : ∑ i, d i Gstar = 1) : ∑ j, g j < Gstar :=
  voluntary_underprovision hd hpos hanti htwo heq hGpos hsam

theorem frozen_lerner_rule {P C : ℝ → ℝ} {q P' C' : ℝ} (hP : HasDerivAt P P' q)
    (hC : HasDerivAt C C' q) (hq : 0 < q) (hopt : IsMonopolyOptimum P C q) (hp : P q ≠ 0) :
    (P q - C') / P q = 1 / (-(P q) / (P' * q)) :=
  lerner_rule hP hC hq hopt hp

theorem frozen_third_degree_discrimination {P₁ P₂ : ℝ → ℝ} {c q₁ q₂ P₁' P₂' : ℝ} (hc : 0 ≤ c)
    (h₁ : HasDerivAt P₁ P₁' q₁) (h₂ : HasDerivAt P₂ P₂' q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hopt : ∀ q : ℝ × ℝ, 0 ≤ q.1 → 0 ≤ q.2 →
      discrimProfit P₁ P₂ c q ≤ discrimProfit P₁ P₂ c (q₁, q₂))
    (hε₁ : 1 < -(P₁ q₁) / (P₁' * q₁)) (hε₂ : 1 < -(P₂ q₂) / (P₂' * q₂))
    (hε : -(P₁ q₁) / (P₁' * q₁) ≤ -(P₂ q₂) / (P₂' * q₂)) : P₂ q₂ ≤ P₁ q₁ :=
  third_degree_discrimination hc h₁ h₂ hq₁ hq₂ hopt hε₁ hε₂ hε

theorem frozen_salop_equilibrium {n t c : ℝ} (hn : 0 < n) (ht : 0 < t) (D : ℝ → ℝ)
    (hD0 : ∀ q, 0 ≤ D q) (hloc : ∀ q, c ≤ q → D q = salopLocalDemand n t (c + t / n) q) :
    D (c + t / n) = 1 / n ∧ (c + t / n - c) * D (c + t / n) = t / n ^ 2 ∧
      ∀ q, (q - c) * D q ≤ t / n ^ 2 :=
  salop_equilibrium hn ht D hD0 hloc

theorem frozen_salop_excess_entry {t F ne no : ℝ} (ht : 0 < t) (hF : 0 < F) (hne : 0 < ne)
    (hzero : t / ne ^ 2 = F) (hno : 0 < no)
    (hmin : ∀ m > 0, no * F + salopTransportCost no t ≤ m * F + salopTransportCost m t) :
    ne = 2 * no :=
  salop_excess_entry ht hF hne hzero hno hmin

theorem frozen_diamond_paradox {n c u s : ℝ} (hn : 0 < n) (hcu : c < u) (hs : 0 < s) (p : ℝ) :
    IsSearchEq n c u s p ↔ p = u :=
  diamond_paradox hn hcu hs p

theorem frozen_may_theorem {I : Type*} [Fintype I] [DecidableEq I] (F : (I → ℤ) → ℤ) :
    IsAnonymous F ∧ IsNeutral F ∧ IsPositivelyResponsive F ↔
      ∀ α, IsVoteProfile α → F α = majorityRule α :=
  may_theorem F

theorem frozen_median_not_defeated {I : Type*} [Fintype I] {peak : I → ℝ} {u : I → ℝ → ℝ}
    (hsp : ∀ i, SinglePeaked (u i) (peak i)) {m : ℝ} (hm : IsWeakMedianPeak peak m) (y : ℝ) :
    2 * (univ.filter fun i => u i m < u i y).card ≤ Fintype.card I ∧
      (univ.filter fun i => u i m < u i y).card ≤
        (univ.filter fun i => u i y ≤ u i m).card :=
  median_not_defeated hsp hm y

theorem frozen_nash_bargaining_theorem (f : BargSolution) (hPE : IsWeakPareto f)
    (hSym : IsSymmetricSol f) (hAff : IsAffineInvariant f) (hIIA : IsIIA f) (P : BargProblem) :
    IsNashSolution P (f P) :=
  nash_bargaining_theorem f hPE hSym hAff hIIA P

theorem frozen_nashSol_axioms :
    IsWeakPareto nashSol ∧ IsSymmetricSol nashSol ∧ IsAffineInvariant nashSol ∧
      IsIIA nashSol :=
  nashSol_axioms

theorem frozen_eq_shapley_of_axioms {N : Type*} [Fintype N] [DecidableEq N]
    {φ : TUGame N → N → ℝ} (hφ : IsShapleyAxioms φ) : φ = shapley :=
  eq_shapley_of_axioms hφ

theorem frozen_shapley_axioms {N : Type*} [Fintype N] [DecidableEq N] :
    IsShapleyAxioms (shapley (N := N)) :=
  shapley_axioms

theorem frozen_bondareva_shapley {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : TUGame N) : (∃ x, IsInCore v x) ↔ IsBalanced v :=
  bondareva_shapley v

end Econ.Audit
