/-
# Frozen statements: Green–Laffont, the intuitive criterion, the first-order approach

Headline statements of `Mechanism/GreenLaffont`, `Information/IntuitiveCriterion` and
`Contracts/FirstOrderApproach`, copied after the adversarial review recorded in
`Audit/REVIEW-batch14.md`. Each is closed by the library theorem, so if a library statement is
ever weakened this file stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Mechanism.GreenLaffont
public import EconLean.Information.IntuitiveCriterion
public import EconLean.Contracts.FirstOrderApproach

@[expose] public section

namespace Econ.Audit

open Finset Set Function Econ

theorem frozen_green_laffont {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} {X : Type*}
    {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X} {t : I → (∀ i, Θ i) → ℝ}
    (hk : IsEfficientRule v k) (hdom : IsUnrestrictedDomain v) (hsp : IsStrategyProof v k t)
    (i : I) : IgnoresOwn i (fun θ => t i θ - othersValue v i θ (k θ)) :=
  green_laffont hk hdom hsp i

theorem frozen_green_laffont_groves {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*}
    {X : Type*} {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X} {t : I → (∀ i, Θ i) → ℝ}
    (hk : IsEfficientRule v k) (hdom : IsUnrestrictedDomain v) (hsp : IsStrategyProof v k t) :
    ∃ h : I → (∀ j, Θ j) → ℝ, (∀ i, IgnoresOwn i (h i)) ∧ t = grovesTransfer v k h :=
  green_laffont_groves hk hdom hsp

theorem frozen_groves_isStrategyProof {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*}
    {X : Type*} {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X} (hk : IsEfficientRule v k)
    {h : I → (∀ j, Θ j) → ℝ} (hh : ∀ i, IgnoresOwn i (h i)) :
    IsStrategyProof v k (grovesTransfer v k h) :=
  groves_isStrategyProof hk hh

theorem frozen_intuitive_separating {θL θH pH : ℝ} {c : ℝ → ℝ → ℝ} {eL eH : ℝ} {μ : ℝ → ℝ}
    (h : IsSpencePBE θL θH pH c eL eH μ) (hsep : eL ≠ eH)
    (hlt : θL < θH) (hcL : StrictMonoOn (fun e => c e θL) (Ici 0))
    (hcH : StrictMonoOn (fun e => c e θH) (Ici 0)) {eR : ℝ} (heR : 0 < eR)
    (hR : c eR θL - c 0 θL = θH - θL) (hpass : ¬ FailsIntuitive θL θH c eL eH μ) :
    eL = 0 ∧ eH = eR :=
  intuitive_separating h hsep hlt hcL hcH heR hR hpass

theorem frozen_intuitive_pooling {θL θH pH : ℝ} {c : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {e : ℝ}
    (h : IsSpencePBE θL θH pH c e e μ) (hlt : θL < θH)
    (hpH : pH < 1) (hcL : StrictMonoOn (fun e => c e θL) (Ici 0))
    (hcontL : ContinuousOn (fun e => c e θL) (Ici 0))
    (hcontH : ContinuousOn (fun e => c e θH) (Ici 0))
    (hsc : ∀ e' e, 0 ≤ e' → e' < e → c e θH - c e' θH < c e θL - c e' θL)
    (hbig : ∃ e₁, e ≤ e₁ ∧ θH - θL ≤ c e₁ θL - c e θL) :
    FailsIntuitive θL θH c e e μ :=
  intuitive_pooling h hlt hpH hcL hcontL hcontH hsc hbig

theorem frozen_riley_passes {θL θH : ℝ} {c : ℝ → ℝ → ℝ} (pH : ℝ)
    (hcL : StrictMonoOn (fun e => c e θL) (Ici 0))
    (hcH : StrictMonoOn (fun e => c e θH) (Ici 0))
    (hsc : ∀ e' e, 0 ≤ e' → e' < e → c e θH - c e' θH < c e θL - c e' θL)
    {eR : ℝ} (heR : 0 < eR) (hR : c eR θL - c 0 θL = θH - θL) :
    IsSpencePBE θL θH pH c 0 eR (fun e => if eR ≤ e then 1 else 0) ∧
      ¬ FailsIntuitive θL θH c 0 eR (fun e => if eR ≤ e then 1 else 0) :=
  riley_passes pH hcL hcH hsc heR hR

theorem frozen_expected_concave {I : Set ℝ} (hI : Convex ℝ I) {p : ℝ → ℕ → ℝ} {m : ℕ}
    (hsum : ∀ a ∈ I, outputCDF (p a) m = 1)
    (hcdfc : ∀ k < m, ConvexOn ℝ I (fun a => outputCDF (p a) k)) {v : ℕ → ℝ}
    (hv : ∀ k, v k ≤ v (k + 1)) :
    ConcaveOn ℝ I (fun a => ∑ j ∈ range (m + 1), p a j * v j) :=
  expected_concave hI hsum hcdfc hv

theorem frozen_foa_valid {I : Set ℝ} (hI : Convex ℝ I) {p : ℝ → ℕ → ℝ} {m : ℕ}
    (hsum : ∀ a ∈ I, outputCDF (p a) m = 1)
    (hcdfc : ∀ k < m, ConvexOn ℝ I (fun a => outputCDF (p a) k)) {v : ℕ → ℝ}
    (hv : ∀ k, v k ≤ v (k + 1)) {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ I ψ) {a : ℝ} (ha : a ∈ I)
    (hfoc : HasDerivAt (fun b => ∑ j ∈ range (m + 1), p b j * v j - ψ b) 0 a) :
    ∀ b ∈ I, ∑ j ∈ range (m + 1), p b j * v j - ψ b ≤ ∑ j ∈ range (m + 1), p a j * v j - ψ a :=
  foa_valid hI hsum hcdfc hv hψ ha hfoc

theorem frozen_mirrlees_monotone {g : ℝ → ℝ} (hg : StrictMono g) {w L : ℕ → ℝ} {lam μ : ℝ}
    (hμ : 0 ≤ μ) (hL : ∀ k, L k ≤ L (k + 1)) (hw : ∀ j, g (w j) = lam + μ * L j) (k : ℕ) :
    w k ≤ w (k + 1) :=
  mirrlees_monotone hg hμ hL hw k

theorem frozen_rogerson {I : Set ℝ} (hI : Convex ℝ I) {p : ℝ → ℕ → ℝ} {m : ℕ}
    (hsum : ∀ a ∈ I, outputCDF (p a) m = 1)
    (hcdfc : ∀ k < m, ConvexOn ℝ I (fun a => outputCDF (p a) k)) {u : ℝ → ℝ} (hu : Monotone u)
    {g : ℝ → ℝ} (hg : StrictMono g) {w L : ℕ → ℝ} {lam μ : ℝ} (hμ : 0 ≤ μ)
    (hL : ∀ k, L k ≤ L (k + 1)) (hw : ∀ j, g (w j) = lam + μ * L j) {ψ : ℝ → ℝ}
    (hψ : ConvexOn ℝ I ψ) {a : ℝ} (ha : a ∈ I)
    (hfoc : HasDerivAt (fun b => ∑ j ∈ range (m + 1), p b j * u (w j) - ψ b) 0 a) :
    ∀ b ∈ I, ∑ j ∈ range (m + 1), p b j * u (w j) - ψ b ≤
      ∑ j ∈ range (m + 1), p a j * u (w j) - ψ a :=
  rogerson hI hsum hcdfc hu hg hμ hL hw hψ ha hfoc

end Econ.Audit
