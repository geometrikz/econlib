/-
# Frozen statements: rural hospitals, the Nash folk theorem with minmax punishments

Headline statements of `Matching/RuralHospitals` and `Games/MinmaxFolk`, copied after the
adversarial review recorded in `Audit/REVIEW-batch16.md`. Each is closed by the library theorem,
so if a library statement is ever weakened this file stops compiling. Do not edit a statement
here without a new review.
-/
module

public import EconLean.Matching.RuralHospitals
public import EconLean.Games.MinmaxFolk

@[expose] public section

namespace Econ.Audit

open Finset Function Filter Topology Econ

theorem frozen_daMatching_womenPessimal {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W]
    {um : M → W → ℝ} {uw : W → M → ℝ} (hum : ∀ m, Function.Injective (um m))
    {ν : M → Option W} (hν : IsStableMatching um uw ν) {m : M} {w : W}
    (hm : daMatching um uw m = some w) : ∃ m', ν m' = some w ∧ uw w m ≤ uw w m' :=
  daMatching_womenPessimal hum hν hm

theorem frozen_rural_hospitals {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W]
    {um : M → W → ℝ} {uw : W → M → ℝ} (hum : ∀ m, Function.Injective (um m))
    (huw : ∀ w, Function.Injective (uw w)) {ν ν' : M → Option W}
    (hν : IsStableMatching um uw ν) (hν' : IsStableMatching um uw ν') :
    (∀ m, (ν m).isSome ↔ (ν' m).isSome) ∧ (∀ w, (∃ m, ν m = some w) ↔ ∃ m, ν' m = some w) :=
  rural_hospitals hum huw hν hν'

theorem frozen_minmaxTrigger_isNash {I : Type*} [DecidableEq I] {S : I → Type*}
    {a : ∀ j, S j} {p : I → ∀ j, S j} {u : I → (∀ j, S j) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ i b, |u i b| ≤ M) {v : I → ℝ}
    (hpun : ∀ i (s : S i), u i (update (p i) i s) ≤ v i)
    (hdev : ∀ i (s : S i), (1 - δ) * u i (update a i s) + δ * v i ≤ u i a) :
    IsRepeatedNash u δ (minmaxTrigger a p) :=
  minmaxTrigger_isNash hδ0 hδ1 hM hpun hdev

theorem frozen_minmax_folk {I : Type*} [DecidableEq I] [Finite I] {S : I → Type*}
    {a : ∀ j, S j} {p : I → ∀ j, S j} {u : I → (∀ j, S j) → ℝ} {M : ℝ}
    (hM : ∀ i b, |u i b| ≤ M) {v : I → ℝ} (hpun : ∀ i (s : S i), u i (update (p i) i s) ≤ v i)
    (hgain : ∀ i, v i < u i a) :
    ∀ᶠ δ in 𝓝[<] (1 : ℝ), IsRepeatedNash u δ (minmaxTrigger a p) :=
  minmax_folk hM hpun hgain

theorem frozen_nash_folk_pureMinmax {I : Type*} [DecidableEq I] [Fintype I] {S : I → Type*}
    [∀ j, Fintype (S j)] [∀ j, Nonempty (S j)] {u : I → (∀ j, S j) → ℝ} {a : ∀ j, S j}
    (hgain : ∀ i, pureMinmax u i < u i a) :
    ∀ᶠ δ in 𝓝[<] (1 : ℝ), ∃ σ : RepeatedProfile S, IsRepeatedNash u δ σ ∧
      ∀ t, pathFrom σ [] t = a :=
  nash_folk_pureMinmax hgain

end Econ.Audit
