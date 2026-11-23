/-
# Frozen statements: information economics, mechanism design, repeated games, matching

Headline statements of `Information/{Lemons,Signaling,Screening,MoralHazard}`,
`Mechanism/*`, `Games/Repeated` and `Matching/GaleShapley`, copied after the adversarial
review recorded in `Audit/REVIEW-info-mechanism.md`. Each is closed by the library theorem, so
if a library statement is ever weakened this file stops compiling. Do not edit a statement
here without a new review.
-/
module

public import EconLean.Information.Lemons
public import EconLean.Information.Signaling
public import EconLean.Information.Screening
public import EconLean.Information.MoralHazard
public import EconLean.Mechanism.Revelation
public import EconLean.Mechanism.VCG
public import EconLean.Mechanism.Myerson
public import EconLean.Mechanism.OptimalMechanism
public import EconLean.Mechanism.BilateralTrade
public import EconLean.Games.Repeated
public import EconLean.Matching.GaleShapley

@[expose] public section

set_option linter.unusedSectionVars false

namespace Econ.Audit

open Function Finset Set Econ Filter Topology

theorem frozen_isLemonsEq_iff (F : SimpleLottery) (p : ℝ) :
    IsLemonsEq F p ↔ p = F.prob.support.min' F.support_nonempty :=
  isLemonsEq_iff F p

section Spence
variable {θL θH pH : ℝ} {c : ℝ → ℝ → ℝ} {eL eH : ℝ} {μ : ℝ → ℝ}

theorem frozen_separating_eL (h : IsSpencePBE θL θH pH c eL eH μ) (hsep : eL ≠ eH)
    (hlt : θL < θH) (hcost : ∀ e, 0 < e → c 0 θL < c e θL) : eL = 0 :=
  h.separating_eL hsep hlt hcost

theorem frozen_separating_bounds (h : IsSpencePBE θL θH pH c 0 eH μ) (hsep : (0 : ℝ) ≠ eH) :
    θH - θL ≤ c eH θL - c 0 θL ∧ c eH θH - c 0 θH ≤ θH - θL :=
  h.separating_bounds hsep

theorem frozen_isSpencePBE_separating (pH : ℝ)
    (hmL : MonotoneOn (fun e => c e θL) (Ici 0))
    (hmH : MonotoneOn (fun e => c e θH) (Ici 0)) (heH : 0 < eH)
    (hL : θH - θL ≤ c eH θL - c 0 θL) (hH : c eH θH - c 0 θH ≤ θH - θL) :
    IsSpencePBE θL θH pH c 0 eH (fun e => if eH ≤ e then 1 else 0) :=
  isSpencePBE_separating pH hmL hmH heH hL hH

end Spence

theorem frozen_noDistortionAtTop (M : ScreeningModel) {qL tL qH tH qL₀ qH₀ : ℝ}
    (hopt : M.IsOptimalMenu qL tL qH tH) (hlt : M.θL ≤ M.θH) (hpL : 0 ≤ M.pL)
    (hpH : 0 < M.pH) (hqL₀ : 0 ≤ qL₀) (hqH₀ : 0 ≤ qH₀) (hvL₀ : 0 ≤ M.v qL₀)
    (hmono₀ : M.v qL₀ ≤ M.v qH₀) (hmaxH : ∀ q, 0 ≤ q → M.surplusH q ≤ M.surplusH qH₀)
    (hmaxL : ∀ q, 0 ≤ q → M.virtualL q ≤ M.virtualL qL₀) :
    (∀ q, 0 ≤ q → M.surplusH q ≤ M.surplusH qH) ∧
      (∀ q, 0 ≤ q → M.virtualL q ≤ M.virtualL qL) ∧
      tL = M.θL * M.v qL ∧ M.θH * M.v qH - tH = M.θH * M.v qL - tL :=
  hopt.noDistortionAtTop M hlt hpL hpH hqL₀ hqH₀ hvL₀ hmono₀ hmaxH hmaxL

section MoralHazard
variable {Ω : Type*} [Fintype Ω]

theorem frozen_implementsHigh_cost_gt {fL fH : Ω → ℝ} (hfL : fL ∈ lotteries Ω)
    (hfH : fH ∈ lotteries Ω) (hfull : ∀ ω, 0 < fH ω) {φ : ℝ → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ φ) (hmono : Monotone φ) {gL gH ū : ℝ} (hg : gL < gH)
    {ν : Ω → ℝ} (h : ImplementsHigh fL fH gL gH ū ν) :
    φ (ū + gH) < outcomeMean fH (fun ω => φ (ν ω)) :=
  implementsHigh_cost_gt hfL hfH hfull hconv hmono hg h

end MoralHazard

section Revelation
variable {I : Type*} [DecidableEq I] {Θ : I → Type*} {X : Type*} {M : I → Type*}

theorem frozen_revelation_dominant {u : ∀ i, X → Θ i → ℝ} {g : (∀ i, M i) → X}
    {s : ∀ i, Θ i → M i} (h : IsDominantEq u g s) : IsDSIC u fun θ => g fun j => s j (θ j) :=
  revelation_dominant h

theorem frozen_revelation_bayesian [Fintype I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]
    {u : ∀ i, X → Θ i → ℝ} {g : (∀ i, M i) → X}
    {p : (∀ j, Θ j) → ℝ} {s : ∀ i, Θ i → M i} (h : IsBNE (mechGame u g) p s) :
    IsBIC u p fun θ => g fun j => s j (θ j) :=
  revelation_bayesian h

end Revelation

section VCG
variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} {X : Type*}

theorem frozen_groves_truthful {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X}
    (hk : IsEfficientRule v k) {h : I → (∀ j, Θ j) → ℝ} (hh : ∀ i, IgnoresOwn i (h i)) (i : I)
    (θ : ∀ j, Θ j) (θi' : Θ i) :
    v i (k (update θ i θi')) (θ i) + grovesTransfer v k h i (update θ i θi') ≤
      v i (k θ) (θ i) + grovesTransfer v k h i θ :=
  groves_truthful hk hh i θ θi'

theorem frozen_clarke_transfer_nonpos [Fintype X] [Nonempty X] (v : ∀ i, X → Θ i → ℝ)
    (k : (∀ i, Θ i) → X) (i : I) (θ : ∀ j, Θ j) : clarkeTransfer v k i θ ≤ 0 :=
  clarke_transfer_nonpos v k i θ

end VCG

theorem frozen_myerson_ic_iff {q p : ℝ → ℝ} {a b : ℝ} :
    IsICMech q p a b ↔ MonotoneOn q (Icc a b) ∧
      ∀ θ ∈ Icc a b, infoRent q p θ = infoRent q p a + ∫ s in a..θ, q s :=
  myerson_ic_iff

theorem frozen_revenue_equivalence {q p p' : ℝ → ℝ} {a b : ℝ}
    (h : IsICMech q p a b) (h' : IsICMech q p' a b) (ha : infoRent q p a = infoRent q p' a) :
    ∀ θ ∈ Icc a b, p θ = p' θ :=
  revenue_equivalence h h' ha

theorem frozen_revenue_le_virtual {n : ℕ} {θ f : ℕ → ℝ} (hf : ∀ k < n, 0 ≤ f k)
    {q p : ℕ → ℝ} (hIC : IsICDiscrete n θ q p) (hIR : IsIRDiscrete n θ q p) :
    ∑ k ∈ range n, f k * p k ≤ ∑ j ∈ range n, q j * virtualWeight n θ f j :=
  revenue_le_virtual hf hIC hIR

theorem frozen_postedPrice_isOptimal {n : ℕ} {θ f : ℕ → ℝ} (hθ : MonotoneOn θ (Set.Iio n))
    (hf : ∀ k < n, 0 ≤ f k) (m : ℕ)
    (hlow : ∀ j < n, j < m → virtualWeight n θ f j ≤ 0)
    (hhigh : ∀ j < n, m ≤ j → 0 ≤ virtualWeight n θ f j) :
    IsICDiscrete n θ (postedQ m) (postedP θ m) ∧ IsIRDiscrete n θ (postedQ m) (postedP θ m) ∧
      ∀ q p : ℕ → ℝ, (∀ j < n, 0 ≤ q j ∧ q j ≤ 1) → IsICDiscrete n θ q p →
        IsIRDiscrete n θ q p →
        ∑ k ∈ range n, f k * p k ≤ ∑ k ∈ range n, f k * postedP θ m k :=
  postedPrice_isOptimal hθ hf m hlow hhigh

theorem frozen_no_efficient_dsic_budgetBalanced_trade {a b : ℝ} (hab : a < b)
    (M : TradeMechanism) (he : M.IsEfficient a b) (hB : M.BuyerDSIC a b)
    (hS : M.SellerDSIC a b) (hBB : M.IsBudgetBalanced a b) : False :=
  no_efficient_dsic_budgetBalanced_trade hab M he hB hS hBB

section Repeated
variable {I : Type*} [DecidableEq I] {S : I → Type*}

theorem frozen_grimTrigger_isSPE {a e : ∀ j, S j} {u : I → (∀ j, S j) → ℝ} {δ M : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : ∀ i b, |u i b| ≤ M) (he : IsNash u e)
    (hdev : ∀ i (s : S i), (1 - δ) * u i (update a i s) + δ * u i e ≤ u i a) :
    IsRepeatedSPE u δ (grimTrigger a e) :=
  grimTrigger_isSPE hδ0 hδ1 hM he hdev

theorem frozen_nashReversion_folk [Finite I] {a e : ∀ j, S j} {u : I → (∀ j, S j) → ℝ} {M : ℝ}
    (hM : ∀ i b, |u i b| ≤ M) (he : IsNash u e) (hgain : ∀ i, u i e < u i a) :
    ∀ᶠ δ in 𝓝[<] (1 : ℝ), 0 ≤ δ ∧ IsRepeatedSPE u δ (grimTrigger a e) :=
  nashReversion_folk hM he hgain

end Repeated

theorem frozen_exists_menOptimal_stable_matching {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq W] (um : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w)) :
    ∃ μ : M → Option W, IsStableMatching um uw μ ∧
      ∀ ν, IsStableMatching um uw ν → ∀ m w', ν m = some w' →
        ∃ w, μ m = some w ∧ um m w' ≤ um m w :=
  exists_menOptimal_stable_matching um uw hum huw

end Econ.Audit
