/-
# Opposition of interests and the rural hospitals theorem

Knuth (1976), Roth (1984), McVitie–Wilson (1970); Roth–Sotomayor (1990), §2.5 (the corollary of
Thm. 2.13) and Thm. 2.22. Setting of `Matching/GaleShapley.lean`: strict preferences, everybody
acceptable, being unmatched is worst; the two sides may have different sizes.

* `daMatching_womenPessimal` (**opposition of interests**): every woman weakly prefers her
  partner in any stable matching to her partner in the men-optimal stable matching (and is
  matched in every stable matching if she is matched in the men-optimal one).
* `card_matched_men_eq`: in any matching, as many men as women are matched.
* `rural_hospitals` (**rural hospitals theorem**, one-to-one version): all stable matchings
  match the same set of men and the same set of women. Since everybody is acceptable, every
  stable matching matches `min(|M|, |W|)` pairs (two single agents would block; this remark is
  not stated as a theorem) and the shorter side is always fully matched;
  the content is that the **same** agents on the longer side are left unmatched, whichever
  stable matching is chosen.

Not formalized: the many-to-one version (a hospital that does not fill its quota gets the same
doctors in every stable matching), and markets with unacceptable partners.
-/
module

public import EconLean.Matching.StrategyProof
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Econ

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W] {um : M → W → ℝ} {uw : W → M → ℝ}

/-- **The men-optimal stable matching is women-pessimal** (Knuth 1976; the corollary of
Roth–Sotomayor Thm. 2.13 on opposition of interests): if a woman is matched to
`m` in the men-optimal stable matching, then in any stable matching `ν` she is matched to a man
she likes at least as much as `m`. -/
theorem daMatching_womenPessimal (hum : ∀ m, Function.Injective (um m))
    {ν : M → Option W} (hν : IsStableMatching um uw ν) {m : M} {w : W}
    (hm : daMatching um uw m = some w) : ∃ m', ν m' = some w ∧ uw w m ≤ uw w m' := by
  by_contra hcon
  push Not at hcon
  refine hν.2 m w ⟨fun w' hw' => ?_, fun m' hm' => hcon m' hm'⟩
  obtain ⟨w₀, hw₀, hle⟩ := daMatching_menOptimal hum ν hν m w' hw'
  rw [hm, Option.some.injEq] at hw₀
  subst hw₀
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · have := (hum m heq); subst this
    exact absurd (hcon m hw') (lt_irrefl _)

/-- In any matching, the number of matched men equals the number of matched women. -/
theorem card_matched_men_eq {μ : M → Option W} (hμ : IsMatching μ) :
    (univ.filter fun m => (μ m).isSome).card = (univ.filter fun w => ∃ m, μ m = some w).card := by
  refine card_bij (fun m hm => (μ m).get (by simpa using hm)) (fun m hm => ?_)
    (fun m₁ hm₁ m₂ hm₂ h => ?_) (fun w hw => ?_)
  · simp only [mem_filter, mem_univ, true_and]
    exact ⟨m, (Option.some_get _).symm⟩
  · exact hμ m₁ m₂ _ (Option.some_get _).symm (by rw [h]; exact (Option.some_get _).symm)
  · obtain ⟨m, hm⟩ := (mem_filter.1 hw).2
    refine ⟨m, by simp [hm], ?_⟩
    simp [hm]

/-- **Rural hospitals theorem** (McVitie–Wilson 1970; Roth 1984; Roth–Sotomayor Thm. 2.22,
one-to-one version): every stable matching matches the same men as the men-optimal one, and the
same women. -/
theorem matched_eq_daMatching (hum : ∀ m, Function.Injective (um m))
    (huw : ∀ w, Function.Injective (uw w)) {ν : M → Option W} (hν : IsStableMatching um uw ν) :
    (univ.filter fun m => (ν m).isSome) = (univ.filter fun m => (daMatching um uw m).isSome) ∧
    (univ.filter fun w => ∃ m, ν m = some w) =
      (univ.filter fun w => ∃ m, daMatching um uw m = some w) := by
  have hμ := daMatching_isStable (um := um) huw
  have hA : (univ.filter fun m => (ν m).isSome) ⊆
      (univ.filter fun m => (daMatching um uw m).isSome) := by
    intro m hm
    simp only [mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at hm ⊢
    obtain ⟨w', hw'⟩ := hm
    obtain ⟨w, hw, -⟩ := daMatching_menOptimal hum ν hν m w' hw'
    exact ⟨w, hw⟩
  have hB : (univ.filter fun w => ∃ m, daMatching um uw m = some w) ⊆
      (univ.filter fun w => ∃ m, ν m = some w) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    obtain ⟨m, hm⟩ := hw
    obtain ⟨m', hm', -⟩ := daMatching_womenPessimal hum hν hm
    exact ⟨m', hm'⟩
  have h1 := card_matched_men_eq hν.1
  have h2 := card_matched_men_eq hμ.1
  have hA' := card_le_card hA
  have hB' := card_le_card hB
  exact ⟨eq_of_subset_of_card_le hA (by omega), (eq_of_subset_of_card_le hB (by omega)).symm⟩

/-- **Rural hospitals theorem**: any two stable matchings match the same set of men and the
same set of women. One-to-one version with everybody acceptable; markets with unacceptable
partners and the many-to-one version are not covered. -/
theorem rural_hospitals (hum : ∀ m, Function.Injective (um m))
    (huw : ∀ w, Function.Injective (uw w)) {ν ν' : M → Option W}
    (hν : IsStableMatching um uw ν) (hν' : IsStableMatching um uw ν') :
    (∀ m, (ν m).isSome ↔ (ν' m).isSome) ∧ (∀ w, (∃ m, ν m = some w) ↔ ∃ m, ν' m = some w) := by
  obtain ⟨h1, h2⟩ := matched_eq_daMatching hum huw hν
  obtain ⟨h1', h2'⟩ := matched_eq_daMatching hum huw hν'
  rw [← h1'] at h1; rw [← h2'] at h2
  refine ⟨fun m => ?_, fun w => ?_⟩
  · have := congrArg (m ∈ ·) h1; simpa using this
  · have := congrArg (w ∈ ·) h2; simpa using this

/-! ### Witness -/

/-- Two men, one woman who prefers man `0`: in **every** stable matching man `1` is single. -/
example (ν : Fin 2 → Option Unit)
    (hν : IsStableMatching (fun _ _ => 0) (fun _ m => if m = 0 then 1 else 0) ν) :
    ν 1 = none := by
  have hum : ∀ m : Fin 2, Function.Injective (fun _ : Unit => (0 : ℝ)) :=
    fun _ _ _ _ => Subsingleton.elim _ _
  have huw : ∀ w : Unit, Function.Injective (fun m : Fin 2 => if m = 0 then (1 : ℝ) else 0) := by
    intro _ a b h; fin_cases a <;> fin_cases b <;> simp_all
  have hν₀ : IsStableMatching (fun (_ : Fin 2) (_ : Unit) => (0 : ℝ))
      (fun _ m => if m = 0 then 1 else 0) (fun m => if m = 0 then some () else none) := by
    refine ⟨fun m₁ m₂ w h₁ h₂ => ?_, fun m w ⟨hm, hw⟩ => ?_⟩
    · fin_cases m₁ <;> fin_cases m₂ <;> simp_all
    · fin_cases m
      · exact lt_irrefl _ (hm () (by simp))
      · exact absurd (hw 0 (by simp)) (by norm_num)
  have := ((rural_hospitals hum huw hν hν₀).1 1)
  simpa using this

end Econ
