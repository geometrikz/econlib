/-
# Deferred acceptance is group strategy-proof for the proposing side (Dubins–Freedman)

Dubins and Freedman (1981), "Machiavelli and the Gale–Shapley algorithm"; Gale and Sotomayor
(1985); Roth and Sotomayor (1990), Thm. 4.10. Setting of `Matching/StrategyProof.lean`:
everybody is acceptable to everybody and preferences are strict.

* `daMatching_groupStrategyproof`: no nonempty coalition of men can misreport so that **every**
  member obtains a partner he truly prefers to his partner under truthful reporting, provided the
  other men report truthfully. The proof is the Gale–Sotomayor
  blocking lemma (`gs_blocking_lemma`): a blocking pair of the manipulated matching whose man does
  not improve, hence lies outside the coalition and reported truthfully, would block it under the
  reported preferences, contradicting the stability of deferred acceptance.

This is the strong form of coalition-proofness that holds (all members strictly better); DA is
not immune to coalitions in which some members only weakly gain. Truncation strategies are
outside the strategy space, as before, and only coalitions of men (the proposing side) are
covered: women, or mixed coalitions, can manipulate DA.
-/
module

public import EconLean.Matching.StrategyProof

@[expose] public section

namespace Econ

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W]

/-- **Dubins–Freedman** (group strategy-proofness of men-proposing deferred acceptance): if the
men outside a coalition `C` report truthfully, the coalition cannot misreport so that each of
its members obtains a partner he strictly prefers (by his true preferences) to his partner under
truthful reporting. The women report their true preferences `uw` throughout, and the coalition's
misreports `um'` need not be strict. -/
theorem daMatching_groupStrategyproof (um um' : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w))
    (C : Finset M) (hC : C.Nonempty) (hsame : ∀ m, m ∉ C → um' m = um m) :
    ¬ ∀ m ∈ C, Improves um (daMatching um uw) (daMatching um' uw) m := by
  intro himp
  have hstab' : IsStableMatching um' uw (daMatching um' uw) := daMatching_isStable huw
  obtain ⟨m₁, hm₁⟩ := hC
  obtain ⟨m₀, w, hn, hblock, -⟩ :=
    gs_blocking_lemma hum huw _ hstab'.1 ⟨m₁, himp m₁ hm₁⟩
  have hnot : m₀ ∉ C := fun h => hn (himp m₀ h)
  refine hstab'.2 m₀ w ⟨fun w'' h => ?_, hblock.2⟩
  rw [hsame m₀ hnot]
  exact hblock.1 w'' h

/-- The individual version (`daMatching_strategyproof`) is the case of a one-man coalition. -/
example (um um' : M → W → ℝ) (uw : W → M → ℝ) (hum : ∀ m, Function.Injective (um m))
    (huw : ∀ w, Function.Injective (uw w)) (m : M) (hsame : ∀ m'', m'' ≠ m → um' m'' = um m'') :
    ¬ Improves um (daMatching um uw) (daMatching um' uw) m := by
  classical
  intro h
  exact daMatching_groupStrategyproof um um' uw hum huw {m} ⟨m, mem_singleton_self m⟩
    (fun m' hm' => hsame m' (by simpa using hm')) (fun m' hm' => by
      rw [mem_singleton.1 hm']; exact h)

end Econ
