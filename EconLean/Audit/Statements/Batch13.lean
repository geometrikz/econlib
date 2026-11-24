/-
# Frozen statements: matching-with-contracts optimality, assignment-game prices, Levin hidden effort

Headline statements of `Matching/ContractsLattice`, `Cooperative/AssignmentLattice` and
`Contracts/RelationalMH`, copied after the adversarial review recorded in
`Audit/REVIEW-batch13.md`. Each is closed by the library theorem, so if a library statement is
ever weakened this file stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Matching.ContractsLattice
public import EconLean.Cooperative.AssignmentLattice
public import EconLean.Contracts.RelationalMH

@[expose] public section

namespace Econ.Audit

open Finset Econ

theorem frozen_stable_isFixedPoint {X : Type*} {cD cH : ChoiceFn X} (hsD : cD.Substitutes)
    (hsH : cH.Substitutes) (hiD : cD.IRC) (hiH : cH.IRC) {Y : Set X}
    (hY : IsStableAlloc cD cH Y) :
    hmMap cD cH (stableXD cD cH Y, stableXH cH Y) = (stableXD cD cH Y, stableXH cH Y) ∧
      stableXD cD cH Y ∩ stableXH cH Y = Y :=
  stable_isFixedPoint hsD hsH hiD hiH hY

theorem frozen_doctor_optimal {X : Type*} {cD cH : ChoiceFn X} (hsD : cD.Substitutes)
    (hsH : cH.Substitutes) (hiD : cD.IRC) (hiH : cH.IRC) :
    ∃ Ystar, IsStableAlloc cD cH Ystar ∧
      ∀ Y, IsStableAlloc cD cH Y → cD.C (Ystar ∪ Y) = Ystar :=
  doctor_optimal hsD hsH hiD hiH

theorem frozen_hospital_optimal {X : Type*} {cD cH : ChoiceFn X} (hsD : cD.Substitutes)
    (hsH : cH.Substitutes) (hiD : cD.IRC) (hiH : cH.IRC) :
    ∃ Ystar, IsStableAlloc cD cH Ystar ∧
      ∀ Y, IsStableAlloc cD cH Y → cH.C (Ystar ∪ Y) = Ystar :=
  hospital_optimal hsD hsH hiD hiH

section
variable {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]

theorem frozen_isCorePayoff_iff (a : B → S → ℝ) (u : B → ℝ) (p : S → ℝ) :
    IsCorePayoff a u p ↔ IsInCore (assignmentGame a) (Sum.elim u p) :=
  isCorePayoff_iff a u p

theorem frozen_core_sup_inf {a : B → S → ℝ} {u u' : B → ℝ} {p p' : S → ℝ}
    (h : IsCorePayoff a u p) (h' : IsCorePayoff a u' p') :
    IsCorePayoff a (fun b => max (u b) (u' b)) (fun s => min (p s) (p' s)) ∧
      IsCorePayoff a (fun b => min (u b) (u' b)) (fun s => max (p s) (p' s)) :=
  core_sup_inf h h'

theorem frozen_buyer_optimal_core (a : B → S → ℝ) :
    ∃ u p, IsCorePayoff a u p ∧ ∀ u' p', IsCorePayoff a u' p' → (∀ b, u' b ≤ u b) ∧
      ∀ s, p s ≤ p' s :=
  buyer_optimal_core a

theorem frozen_seller_optimal_core (a : B → S → ℝ) :
    ∃ u p, IsCorePayoff a u p ∧ ∀ u' p', IsCorePayoff a u' p' → (∀ s, p' s ≤ p s) ∧
      ∀ b, u b ≤ u' b :=
  seller_optimal_core a

theorem frozen_core_slack {a : B → S → ℝ} {u : B → ℝ} {p : S → ℝ} (h : IsCorePayoff a u p)
    {M : Finset (B × S)} (hM : IsOptimalMatching a M) :
    (∀ q ∈ M, u q.1 + p q.2 = a q.1 q.2) ∧ (∀ b, ¬ BMatched M b → u b = 0) ∧
      ∀ s, ¬ SMatched M s → p s = 0 :=
  core_slack h hM

theorem frozen_compEq_core {a : B → S → ℝ} {p : S → ℝ} {M : Finset (B × S)}
    (h : IsCompEq a p M) :
    IsOptimalMatching a M ∧ IsCorePayoff a (buyerSurplus a p M) p :=
  compEq_core h

theorem frozen_core_compEq {a : B → S → ℝ} {u : B → ℝ} {p : S → ℝ} (h : IsCorePayoff a u p)
    {M : Finset (B × S)} (hM : IsOptimalMatching a M) : IsCompEq a p M :=
  core_compEq h hM

theorem frozen_compEq_prices_iff (a : B → S → ℝ) (p : S → ℝ) :
    (∃ M, IsCompEq a p M) ↔ ∃ u, IsCorePayoff a u p :=
  compEq_prices_iff a p

theorem frozen_exists_min_compEq_prices (a : B → S → ℝ) :
    ∃ u p, IsCorePayoff a u p ∧ (∀ u' p', IsCorePayoff a u' p' → ∀ b, u' b ≤ u b) ∧
      (∃ M, IsCompEq a p M) ∧ ∀ p' M', IsCompEq a p' M' → ∀ s, p s ≤ p' s :=
  exists_min_compEq_prices a
end

theorem frozen_statContract_iff_range {E Y : Type*} [Fintype Y] [Nonempty Y] {f : E → Y → ℝ}
    {v : Y → ℝ} {c : E → ℝ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hf : ∀ e, ∑ y, f e y = 1)
    (e : E) :
    (∃ w b, IsStatContract f v c δ e w b) ↔
      ∃ b : Y → ℝ, (∀ e', expAt f e' b - c e' ≤ expAt f e b - c e) ∧
        ∀ y y', b y - b y' ≤ δ / (1 - δ) * (expAt f e v - c e) :=
  statContract_iff_range hδ0 hδ1 hf e

theorem frozen_one_step_bound {Y : Type*} [Fintype Y] [Nonempty Y] {fH fL : Y → ℝ}
    (hsum : ∑ y, fH y = ∑ y, fL y) (D : ℝ) :
    (∀ b : Y → ℝ, (∀ y y', b y - b y' ≤ D) →
      ∑ y, (fH y - fL y) * b y ≤ D * ∑ y, max (fH y - fL y) 0) ∧
    ∑ y, (fH y - fL y) * (if fL y < fH y then D else 0) = D * ∑ y, max (fH y - fL y) 0 :=
  one_step_bound hsum D

theorem frozen_two_effort_iff {E Y : Type*} [Fintype Y] [Nonempty Y] {f : E → Y → ℝ}
    {v : Y → ℝ} {c : E → ℝ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hf : ∀ e, ∑ y, f e y = 1)
    {eH eL : E} (hE : ∀ e, e = eH ∨ e = eL) :
    (∃ w b, IsStatContract f v c δ eH w b) ↔ 0 ≤ expAt f eH v - c eH ∧
      c eH - c eL ≤ δ / (1 - δ) * (expAt f eH v - c eH) * ∑ y, max (f eH y - f eL y) 0 :=
  two_effort_iff hδ0 hδ1 hf hE

end Econ.Audit
