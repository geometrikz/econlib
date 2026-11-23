/-
# Frozen statements: correspondences and Berge's maximum theorem

These are the headline statements of `Foundations/Correspondence.lean` and
`Foundations/Maximum.lean`, copied verbatim after they passed the
adversarial review (2026-11-23; verdicts: faithful, or faithful with the
deviations documented in `Maximum.lean`). Each is closed by the library
theorem, so if a library statement is ever weakened, this file stops
compiling. This is a lightweight stand-in for `leanprover/comparator` until
the audit pipeline (PLAN.md §5) is set up. Do not edit a statement here
without a new review.
-/
module

public import EconLean.Foundations.Maximum

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem frozen_isClosed_of_isClosed_graph {Φ : X → Set Y} (h : IsClosed (graph Φ)) (x : X) :
    IsClosed (Φ x) :=
  isClosed_of_isClosed_graph h x

theorem frozen_isClosed_graph_of_upperHemicontinuous [RegularSpace Y] {Φ : X → Set Y}
    (hΦ : UpperHemicontinuous Φ) (hcl : ∀ x, IsClosed (Φ x)) :
    IsClosed (graph Φ) :=
  isClosed_graph_of_upperHemicontinuous hΦ hcl

theorem frozen_UpperHemicontinuousAt_inter_of_isClosed_graph {Φ Ψ : X → Set Y} {x : X}
    (hΦ : UpperHemicontinuousAt Φ x) (hK : IsCompact (Φ x))
    (hΨ : IsClosed (graph Ψ)) :
    UpperHemicontinuousAt (fun x => Φ x ∩ Ψ x) x :=
  UpperHemicontinuousAt.inter_of_isClosed_graph hΦ hK hΨ

theorem frozen_upperHemicontinuousAt_of_isClosed_graph {Φ : X → Set Y} {x : X} {K : Set Y}
    (hΦ : IsClosed (graph Φ)) (hK : IsCompact K) (hbdd : ∀ᶠ x' in 𝓝 x, Φ x' ⊆ K) :
    UpperHemicontinuousAt Φ x :=
  upperHemicontinuousAt_of_isClosed_graph hΦ hK hbdd

theorem frozen_upperHemicontinuous_of_isClosed_graph [CompactSpace Y] {Φ : X → Set Y}
    (hΦ : IsClosed (graph Φ)) : UpperHemicontinuous Φ :=
  upperHemicontinuous_of_isClosed_graph hΦ

theorem frozen_IsCompact_biUnion_of_upperHemicontinuous {Φ : X → Set Y} {K : Set X}
    (hK : IsCompact K) (hΦ : ∀ x ∈ K, UpperHemicontinuousAt Φ x)
    (hc : ∀ x ∈ K, IsCompact (Φ x)) : IsCompact (⋃ x ∈ K, Φ x) :=
  IsCompact.biUnion_of_upperHemicontinuous hK hΦ hc

theorem frozen_isClosed_graph_iff_seq [FirstCountableTopology X] [FirstCountableTopology Y]
    {Φ : X → Set Y} :
    IsClosed (graph Φ) ↔ ∀ (u : ℕ → X) (v : ℕ → Y) (x : X) (y : Y),
      (∀ n, v n ∈ Φ (u n)) → Tendsto u atTop (𝓝 x) → Tendsto v atTop (𝓝 y) → y ∈ Φ x :=
  isClosed_graph_iff_seq

theorem frozen_UpperHemicontinuousAt_exists_tendsto_subseq {Y : Type*} [PseudoMetricSpace Y]
    {Φ : X → Set Y} {x : X} (hΦ : UpperHemicontinuousAt Φ x) (hK : IsCompact (Φ x))
    {u : ℕ → X} {v : ℕ → Y} (hu : Tendsto u atTop (𝓝 x)) (hv : ∀ n, v n ∈ Φ (u n)) :
    ∃ y ∈ Φ x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (v ∘ φ) atTop (𝓝 y) :=
  UpperHemicontinuousAt.exists_tendsto_subseq hΦ hK hu hv

section Berge

variable {f : X → Y → ℝ} {Φ : X → Set Y}

theorem frozen_isGreatest_maxValue (hf : Continuous (Function.uncurry f)) {x : X}
    (hne : (Φ x).Nonempty) (hK : IsCompact (Φ x)) :
    IsGreatest (f x '' Φ x) (maxValue f Φ x) :=
  isGreatest_maxValue hf hne hK

theorem frozen_argmax_eq (hf : Continuous (Function.uncurry f)) {x : X}
    (hne : (Φ x).Nonempty) (hK : IsCompact (Φ x)) :
    argmax f Φ x = Φ x ∩ {y | maxValue f Φ x ≤ f x y} :=
  argmax_eq hf hne hK

theorem frozen_upperSemicontinuous_maxValue (hf : Continuous (Function.uncurry f))
    (hU : UpperHemicontinuous Φ) (hne : ∀ x, (Φ x).Nonempty) (hK : ∀ x, IsCompact (Φ x)) :
    UpperSemicontinuous (maxValue f Φ) :=
  upperSemicontinuous_maxValue hf hU hne hK

theorem frozen_lowerSemicontinuous_maxValue (hf : Continuous (Function.uncurry f))
    (hL : LowerHemicontinuous Φ) (hne : ∀ x, (Φ x).Nonempty) (hK : ∀ x, IsCompact (Φ x)) :
    LowerSemicontinuous (maxValue f Φ) :=
  lowerSemicontinuous_maxValue hf hL hne hK

theorem frozen_continuous_maxValue (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) :
    Continuous (maxValue f Φ) :=
  continuous_maxValue hf hΦ hne hK

theorem frozen_upperHemicontinuous_argmax (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) :
    UpperHemicontinuous (argmax f Φ) :=
  upperHemicontinuous_argmax hf hΦ hne hK

theorem frozen_berge_maximum_theorem (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) :
    (∀ x, IsGreatest (f x '' Φ x) (maxValue f Φ x)) ∧
    Continuous (maxValue f Φ) ∧
    (∀ x, (argmax f Φ x).Nonempty ∧ IsCompact (argmax f Φ x)) ∧
    UpperHemicontinuous (argmax f Φ) :=
  berge_maximum_theorem hf hΦ hne hK

theorem frozen_continuous_of_argmax_eq_singleton (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) {g : X → Y} (hg : ∀ x, argmax f Φ x = {g x}) :
    Continuous g :=
  continuous_of_argmax_eq_singleton hf hΦ hne hK hg

end Berge

end Econ.Audit
