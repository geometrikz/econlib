/-
# Two-sided matching: existence of stable matchings (Gale–Shapley)

Gale & Shapley (1962); Roth & Sotomayor (1990), Ch. 2. Finite sets `M` (proposers, "men") and
`W` ("women") with strict preferences given by injective utilities `um m : W → ℝ` and
`uw w : M → ℝ`; every partner is acceptable (being unmatched is worst). A matching is a map
`μ : M → Option W` that never assigns two men to the same woman.

A pair `(m, w)` **blocks** `μ` if `m` prefers `w` to his assignment (or is unmatched) and `w`
prefers `m` to her assignment (or is unmatched). `μ` is **stable** if no pair blocks it.

Main results: `exists_stable_matching` (Gale–Shapley 1962, Thm. 1): a stable matching always
exists; `exists_menOptimal_stable_matching` (Thm. 2): the men-proposing algorithm yields the
**men-optimal** stable matching, which every man weakly prefers to any other stable matching. The proof runs the **men-proposing deferred acceptance** algorithm, encoded by the
sets `R m` of women who have rejected `m`:
* each man proposes to his favourite woman not in `R m` (`proposal`);
* each woman keeps her favourite proposer and rejects the others (`daStep`);
* the invariant `DAInv` says every woman who rejected `m` currently holds a proposal from a man
  she prefers to `m`; it is preserved because a woman's held proposal only improves;
* `∑ₘ |R m|` strictly increases while someone is rejected, so the algorithm stops, and the
  final proposals form a stable matching;
* `OptInv` (no man is ever rejected by a stably achievable partner) is also preserved, giving
  men-optimality.

Strategy-proofness for the proposing side (Dubins–Freedman; Roth 1982) is in
`Matching/StrategyProof.lean`.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace Econ

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W]

/-- A (partial, one-to-one) matching: no two men are assigned the same woman. -/
def IsMatching (μ : M → Option W) : Prop :=
  ∀ m₁ m₂ w, μ m₁ = some w → μ m₂ = some w → m₁ = m₂

omit [Fintype M] [Fintype W] [DecidableEq W] in
/-- `(m, w)` **blocks** `μ`: each strictly prefers the other to the current assignment
(an unmatched agent prefers any partner). -/
def IsBlocking (um : M → W → ℝ) (uw : W → M → ℝ) (μ : M → Option W) (m : M) (w : W) : Prop :=
  (∀ w', μ m = some w' → um m w' < um m w) ∧ (∀ m', μ m' = some w → uw w m' < uw w m)

omit [Fintype M] [Fintype W] [DecidableEq W] in
/-- A **stable matching**: a matching with no blocking pair. -/
def IsStableMatching (um : M → W → ℝ) (uw : W → M → ℝ) (μ : M → Option W) : Prop :=
  IsMatching μ ∧ ∀ m w, ¬ IsBlocking um uw μ m w

omit [Fintype M] [DecidableEq W] in
/-- The woman `m` proposes to when the women in `R m` have rejected him: his favourite among
the others, if any. -/
noncomputable def proposal (um : M → W → ℝ) (R : M → Finset W) (m : M) : Option W :=
  if h : (univ \ R m).Nonempty then some ((univ \ R m).exists_max_image (um m) h).choose
  else none

section DA

variable {um : M → W → ℝ} {uw : W → M → ℝ}

omit [Fintype M] in
lemma proposal_spec {R : M → Finset W} {m : M} {w : W} (h : proposal um R m = some w) :
    w ∉ R m ∧ ∀ w', w' ∉ R m → um m w' ≤ um m w := by
  unfold proposal at h
  split_ifs at h with hne
  · obtain ⟨hmem, hmax⟩ := ((univ \ R m).exists_max_image (um m) hne).choose_spec
    cases h
    exact ⟨(mem_sdiff.1 hmem).2, fun w' hw' => hmax w' (mem_sdiff.2 ⟨mem_univ _, hw'⟩)⟩

omit [Fintype M] in
lemma proposal_eq_none {R : M → Finset W} {m : M} (h : proposal um R m = none) :
    ∀ w, w ∈ R m := by
  unfold proposal at h
  split_ifs at h with hne
  intro w
  by_contra hw
  exact hne ⟨w, mem_sdiff.2 ⟨mem_univ _, hw⟩⟩

omit [Fintype M] in
lemma proposal_isSome {R : M → Finset W} {m : M} {w : W} (hw : w ∉ R m) :
    ∃ w', proposal um R m = some w' := by
  cases h : proposal um R m with
  | none => exact absurd (proposal_eq_none h w) hw
  | some w' => exact ⟨w', rfl⟩

omit [Fintype M] in
/-- `m` is **rejected** at `R`: some other proposer to the same woman is preferred by her. -/
def Rejected (um : M → W → ℝ) (uw : W → M → ℝ) (R : M → Finset W) (m : M) (w : W) : Prop :=
  proposal um R m = some w ∧ ∃ m', proposal um R m' = some w ∧ uw w m < uw w m'

open Classical in
/-- One round of deferred acceptance: every rejected man adds the rejecting woman to `R m`. -/
noncomputable def daStep (um : M → W → ℝ) (uw : W → M → ℝ) (R : M → Finset W) (m : M) :
    Finset W :=
  match proposal um R m with
  | some w => if Rejected um uw R m w then insert w (R m) else R m
  | none => R m

omit [Fintype M] in
/-- **The DA invariant**: every woman who has rejected `m` currently holds a proposal from a
man she prefers to `m`. -/
def DAInv (um : M → W → ℝ) (uw : W → M → ℝ) (R : M → Finset W) : Prop :=
  ∀ m w, w ∈ R m → ∃ m', proposal um R m' = some w ∧ uw w m < uw w m'

/-- A woman's favourite current proposer is not rejected, so he keeps proposing to her. -/
lemma exists_best_proposer (R : M → Finset W) {w : W} {m₀ : M}
    (h₀ : proposal um R m₀ = some w) :
    ∃ b, proposal um (daStep um uw R) b = some w ∧ proposal um R b = some w ∧
      ∀ m, proposal um R m = some w → uw w m ≤ uw w b := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image
    (univ.filter fun m => proposal um R m = some w) (uw w) ⟨m₀, by simp [h₀]⟩
  have hbw : proposal um R b = some w := (mem_filter.1 hb).2
  have hmax' : ∀ m, proposal um R m = some w → uw w m ≤ uw w b :=
    fun m hm => hmax m (by simp [hm])
  have hnr : ¬ Rejected um uw R b w := fun ⟨_, m', hm', hlt⟩ => (hmax' m' hm').not_gt hlt
  have hstep : daStep um uw R b = R b := by simp [daStep, hbw, hnr]
  refine ⟨b, ?_, hbw, hmax'⟩
  have : proposal um (daStep um uw R) b = proposal um R b := by
    simp only [proposal, hstep]
  rw [this, hbw]

omit [Fintype M] in
/-- `R ⊆ daStep R`. -/
lemma subset_daStep (R : M → Finset W) (m : M) : R m ⊆ daStep um uw R m := by
  classical
  unfold daStep
  split
  · split_ifs
    · exact subset_insert _ _
    · exact subset_rfl
  · exact subset_rfl

/-- **Deferred acceptance preserves the invariant.** -/
lemma daInv_daStep {R : M → Finset W} (hR : DAInv um uw R) : DAInv um uw (daStep um uw R) := by
  classical
  intro m w hw
  -- In both cases `w` currently receives a proposal from some `m'` she prefers to `m`.
  have key : ∃ m', proposal um R m' = some w ∧ uw w m < uw w m' := by
    by_cases hold : w ∈ R m
    · exact hR m w hold
    · unfold daStep at hw
      split at hw
      · rename_i w' hw'
        split_ifs at hw with hrej
        · rcases mem_insert.1 hw with rfl | hw
          · exact hrej.2
          · exact absurd hw hold
        · exact absurd hw hold
      · exact absurd hw hold
  obtain ⟨m', hm', hlt⟩ := key
  obtain ⟨b, hb, -, hbmax⟩ := exists_best_proposer (uw := uw) R hm'
  exact ⟨b, hb, hlt.trans_le (hbmax m' hm')⟩

/-- While someone is rejected, the total number of rejections strictly increases. -/
lemma card_lt_daStep {R : M → Finset W} {m : M} {w : W} (h : Rejected um uw R m w) :
    ∑ m, (R m).card < ∑ m, (daStep um uw R m).card := by
  classical
  refine sum_lt_sum (fun m _ => card_le_card (subset_daStep R m)) ⟨m, mem_univ _, ?_⟩
  have hstep : daStep um uw R m = insert w (R m) := by simp [daStep, h.1, h]
  rw [hstep, card_insert_of_notMem (proposal_spec h.1).1]
  exact Nat.lt_succ_self _

omit [DecidableEq W] in
/-- The total number of rejections is bounded by `|M| |W|`. -/
lemma sum_card_le (R : M → Finset W) : ∑ m, (R m).card ≤ Fintype.card M * Fintype.card W := by
  calc ∑ m, (R m).card ≤ ∑ _m : M, Fintype.card W :=
        sum_le_sum fun m _ => card_le_univ _
    _ = Fintype.card M * Fintype.card W := by simp

/-- Deferred acceptance terminates in a state satisfying the invariant (and any further
invariant `Q` preserved by the step) with no rejections. -/
lemma exists_terminal (Q : (M → Finset W) → Prop)
    (hQ : ∀ R, DAInv um uw R → Q R → Q (daStep um uw R))
    (R : M → Finset W) (hR : DAInv um uw R) (hRQ : Q R) :
    ∃ R', DAInv um uw R' ∧ Q R' ∧ ∀ m w, ¬ Rejected um uw R' m w := by
  induction hk : Fintype.card M * Fintype.card W - ∑ m, (R m).card using
    Nat.strong_induction_on generalizing R with
  | _ k ih =>
    by_cases hdone : ∀ m w, ¬ Rejected um uw R m w
    · exact ⟨R, hR, hRQ, hdone⟩
    · push Not at hdone
      obtain ⟨m, w, hrej⟩ := hdone
      have hlt := card_lt_daStep hrej
      have hle := sum_card_le (daStep um uw R)
      exact ih _ (by omega) (daStep um uw R) (daInv_daStep hR) (hQ R hR hRQ) rfl

omit [Fintype M] in
/-- **The optimality invariant**: no man has been rejected by a woman who is his partner in
some stable matching. -/
def OptInv (um : M → W → ℝ) (uw : W → M → ℝ) (R : M → Finset W) : Prop :=
  ∀ m w, w ∈ R m → ∀ ν : M → Option W, IsStableMatching um uw ν → ν m ≠ some w

omit [Fintype M] in
/-- **Deferred acceptance preserves the optimality invariant** (Gale–Shapley 1962, Thm. 2):
if `w` rejects `m` for `m'`, then in any stable `ν` pairing `m` with `w`, the pair `(m', w)`
would block. -/
lemma optInv_daStep (hum : ∀ m, Function.Injective (um m)) {R : M → Finset W}
    (hR : OptInv um uw R) : OptInv um uw (daStep um uw R) := by
  classical
  intro m w hw ν hν hνm
  by_cases hold : w ∈ R m
  · exact hR m w hold ν hν hνm
  have hrej : Rejected um uw R m w := by
    unfold daStep at hw
    split at hw
    · rename_i w' hw'
      split_ifs at hw with hr
      · rcases mem_insert.1 hw with rfl | hw
        · exact hr
        · exact absurd hw hold
      · exact absurd hw hold
    · exact absurd hw hold
  obtain ⟨-, m', hm', hlt⟩ := hrej
  have hne : m' ≠ m := fun h => (lt_irrefl _ (h ▸ hlt))
  -- `(m', w)` blocks `ν`.
  refine hν.2 m' w ⟨fun w'' hw'' => ?_, fun m'' hm'' => ?_⟩
  · have hw''ne : w'' ≠ w := fun h => hne (hν.1 _ _ _ (h ▸ hw'') hνm)
    have hw''R : w'' ∉ R m' := fun h => hR m' w'' h ν hν hw''
    exact lt_of_le_of_ne ((proposal_spec hm').2 w'' hw''R) ((hum m').ne hw''ne)
  · rw [hν.1 _ _ _ hm'' hνm]; exact hlt

end DA

/-- **Gale–Shapley, men-optimal form** (Gale–Shapley 1962, Thms. 1–2). With strict
preferences on both sides, the men-proposing deferred acceptance matching `μ` is stable and
**men-optimal**: every man weakly prefers his `μ`-partner to his partner in any other stable
matching (and is matched under `μ` whenever he is matched in some stable matching). -/
theorem exists_menOptimal_stable_matching (um : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w)) :
    ∃ μ : M → Option W, IsStableMatching um uw μ ∧
      ∀ ν, IsStableMatching um uw ν → ∀ m w', ν m = some w' →
        ∃ w, μ m = some w ∧ um m w' ≤ um m w := by
  obtain ⟨R, hinv, hopt, hterm⟩ := exists_terminal (um := um) (uw := uw) (OptInv um uw)
    (fun _ _ h => optInv_daStep hum h) (fun _ => ∅)
    (fun m w hw => absurd hw (Finset.notMem_empty w))
    (fun m w hw => absurd hw (Finset.notMem_empty w))
  refine ⟨proposal um R, ⟨?_, ?_⟩, ?_⟩
  · -- Two men proposing to the same woman: she strictly prefers one, rejecting the other.
    intro m₁ m₂ w h₁ h₂
    by_contra hne
    rcases lt_or_gt_of_ne ((huw w).ne hne) with hlt | hlt
    · exact hterm m₁ w ⟨h₁, m₂, h₂, hlt⟩
    · exact hterm m₂ w ⟨h₂, m₁, h₁, hlt⟩
  · rintro m w ⟨hm, hw⟩
    -- `m` prefers `w` to his proposal, so `w` must already have rejected him.
    have hwR : w ∈ R m := by
      by_contra hwR
      obtain ⟨w', hw'⟩ := proposal_isSome (um := um) hwR
      exact (hm w' hw').not_ge ((proposal_spec hw').2 w hwR)
    -- She then holds a proposal from someone she prefers to `m`: her partner.
    obtain ⟨m', hm', hlt⟩ := hinv m w hwR
    exact (hw m' hm').not_gt hlt
  · intro ν hν m w' hνm
    have hw'R : w' ∉ R m := fun h => hopt m w' h ν hν hνm
    obtain ⟨w, hw⟩ := proposal_isSome (um := um) hw'R
    exact ⟨w, hw, (proposal_spec hw).2 w' hw'R⟩

/-- **Existence of a stable matching** (Gale–Shapley 1962). -/
theorem exists_stable_matching (um : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w)) :
    ∃ μ : M → Option W, IsStableMatching um uw μ :=
  (exists_menOptimal_stable_matching um uw hum huw).imp fun _ h => h.1

/-- **Witness: stability has bite.** Both men rank woman `0` first and she ranks man `0` first;
the matching `0 ↦ 1, 1 ↦ 0` is blocked by `(0, 0)`. -/
example :
    ¬ IsStableMatching (M := Fin 2) (W := Fin 2) (fun _ w => if w = 0 then 1 else 0)
      (fun _ m => if m = 0 then 1 else 0) (fun m => some (1 - m)) := by
  rintro ⟨-, hst⟩
  refine hst 0 0 ⟨fun w' hw' => ?_, fun m' hm' => ?_⟩
  · simp only [Option.some.injEq] at hw'; subst hw'; simp
  · simp only [Option.some.injEq] at hm'
    have : m' = 1 := by omega
    subst this; simp

end Econ
