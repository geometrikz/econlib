/-
# Deferred acceptance is strategy-proof for the proposing side

Dubins & Freedman (1981); Roth (1982); Gale & Sotomayor (1985), *Some remarks on the stable
matching problem*; Roth & Sotomayor (1990), Thm. 4.7. Setting of `Matching/GaleShapley.lean`.

We run the men-proposing deferred acceptance algorithm as an explicit sequence of states
`daIter t` (the sets of women who have rejected each man by round `t`), show it reaches a
state with no rejections within `|M| |W| + 1` rounds, and call the resulting matching
`daMatching um uw` (the **DA mechanism**: it maps reported preferences to a matching).

Main results:
* `daMatching_isStable`, `daMatching_menOptimal`: the DA matching is stable and men-optimal.
* `gs_blocking_lemma` (Gale–Sotomayor 1985 blocking lemma): if `μ'` is any matching that some
  men strictly prefer to the DA matching `μ`, then some pair `(m₀, w)` blocks `μ'`, where `m₀`
  does **not** strictly prefer `μ'` to `μ` and `w` is matched under `μ'` to a man who does.
* `daMatching_strategyproof` (Dubins–Freedman; Roth): no man can obtain a strictly better
  partner by misreporting his preferences, whatever the others report (individual
  manipulation, with every partner acceptable: truncation reports and coalitional
  manipulation are outside this statement).
-/
module

public import EconLean.Matching.GaleShapley

@[expose] public section

namespace Econ

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq W]

/-- The state of men-proposing deferred acceptance after `t` rounds. -/
noncomputable def daIter (um : M → W → ℝ) (uw : W → M → ℝ) : ℕ → M → Finset W
  | 0 => fun _ => ∅
  | t + 1 => daStep um uw (daIter um uw t)

omit [Fintype M] in
/-- No man is rejected at state `R`: the algorithm has stopped. -/
def NoRejection (um : M → W → ℝ) (uw : W → M → ℝ) (R : M → Finset W) : Prop :=
  ∀ m w, ¬ Rejected um uw R m w

/-- The number of rounds after which deferred acceptance has certainly stopped. -/
def daRounds (M W : Type*) [Fintype M] [Fintype W] : ℕ := Fintype.card M * Fintype.card W + 1

/-- The final state of deferred acceptance. -/
noncomputable def daFinal (um : M → W → ℝ) (uw : W → M → ℝ) : M → Finset W :=
  daIter um uw (daRounds M W)

/-- **The deferred acceptance mechanism**: the men-proposing DA matching for reported
utilities `um`, `uw`. -/
noncomputable def daMatching (um : M → W → ℝ) (uw : W → M → ℝ) : M → Option W :=
  proposal um (daFinal um uw)

omit [Fintype M] in
/-- `m` **strictly prefers** `μ'` to `μ` (being unmatched is worst). -/
def Improves (um : M → W → ℝ) (μ μ' : M → Option W) (m : M) : Prop :=
  ∃ w', μ' m = some w' ∧ ∀ w, μ m = some w → um m w < um m w'

section Iter

variable {um : M → W → ℝ} {uw : W → M → ℝ}

omit [Fintype M] in
lemma daStep_eq_self {R : M → Finset W} (h : NoRejection um uw R) : daStep um uw R = R := by
  classical
  funext m
  unfold daStep
  split
  · rename_i w _
    simp only [h m w, ↓reduceIte]
  · rfl

omit [Fintype M] in
lemma daIter_mono {t t' : ℕ} (h : t ≤ t') (m : M) : daIter um uw t m ⊆ daIter um uw t' m := by
  induction t', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' _ ih => exact ih.trans (subset_daStep _ m)

lemma daIter_inv (t : ℕ) : DAInv um uw (daIter um uw t) := by
  induction t with
  | zero => intro m w hw; exact absurd hw (Finset.notMem_empty w)
  | succ t ih => exact daInv_daStep ih

omit [Fintype M] in
lemma daIter_optInv (hum : ∀ m, Function.Injective (um m)) (t : ℕ) :
    OptInv um uw (daIter um uw t) := by
  induction t with
  | zero => intro m w hw; exact absurd hw (Finset.notMem_empty w)
  | succ t ih => exact optInv_daStep hum ih

omit [Fintype M] in
lemma daIter_add_of_noRejection {t : ℕ} (h : NoRejection um uw (daIter um uw t)) (k : ℕ) :
    daIter um uw (t + k) = daIter um uw t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, daIter, ih, daStep_eq_self h]

/-- Deferred acceptance stops within `daRounds` rounds. -/
lemma exists_noRejection :
    ∃ t ≤ daRounds M W, NoRejection um uw (daIter um uw t) := by
  classical
  have key : ∀ t, (∃ t' ≤ t, NoRejection um uw (daIter um uw t')) ∨
      t ≤ ∑ m, (daIter um uw t m).card := by
    intro t
    induction t with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ t ih =>
      rcases ih with ⟨t', ht', h⟩ | ih
      · exact Or.inl ⟨t', ht'.trans (Nat.le_succ t), h⟩
      · by_cases hno : NoRejection um uw (daIter um uw t)
        · exact Or.inl ⟨t, Nat.le_succ t, hno⟩
        · simp only [NoRejection, not_forall, not_not] at hno
          obtain ⟨m, w, hrej⟩ := hno
          have := card_lt_daStep hrej
          exact Or.inr (by rw [daIter]; omega)
  rcases key (daRounds M W) with h | h
  · exact h
  · have := sum_card_le (daIter um uw (daRounds M W))
    simp only [daRounds] at h this
    omega

lemma daFinal_noRejection : NoRejection um uw (daFinal um uw) := by
  obtain ⟨t, ht, h⟩ := exists_noRejection (um := um) (uw := uw)
  have := daIter_add_of_noRejection h (daRounds M W - t)
  rw [Nat.add_sub_cancel' ht] at this
  show NoRejection um uw (daIter um uw (daRounds M W))
  rw [this]; exact h

lemma daIter_subset_daFinal (t : ℕ) (m : M) : daIter um uw t m ⊆ daFinal um uw m := by
  rcases le_total t (daRounds M W) with h | h
  · exact daIter_mono h m
  · have hno : NoRejection um uw (daIter um uw (daRounds M W)) := daFinal_noRejection
    have := daIter_add_of_noRejection hno (t - daRounds M W)
    rw [Nat.add_sub_cancel' h] at this
    rw [this]; exact subset_rfl

lemma daIter_daRounds : daIter um uw (daRounds M W) = daFinal um uw := rfl

omit [Fintype M] in
/-- A proposal to `w` stays put while `w` has not rejected the man. -/
lemma proposal_stay (hum : ∀ m, Function.Injective (um m)) {A B : M → Finset W} {m : M} {w : W}
    (hA : proposal um A m = some w) (hAB : A m ⊆ B m) (hw : w ∉ B m) :
    proposal um B m = some w := by
  obtain ⟨w', hw'⟩ := proposal_isSome (um := um) hw
  have h1 := (proposal_spec hw').2 w hw
  have h2 := (proposal_spec hA).2 w' fun h => (proposal_spec hw').1 (hAB h)
  rw [hw', (hum m) (le_antisymm h2 h1)]

omit [Fintype M] in
/-- Every rejection recorded at round `t` happened in an earlier round. -/
lemma rejected_of_mem_daIter {t : ℕ} {m : M} {w : W} (h : w ∈ daIter um uw t m) :
    ∃ u < t, Rejected um uw (daIter um uw u) m w := by
  classical
  induction t with
  | zero => exact absurd h (Finset.notMem_empty w)
  | succ t ih =>
    by_cases hold : w ∈ daIter um uw t m
    · obtain ⟨u, hu, hr⟩ := ih hold
      exact ⟨u, hu.trans (Nat.lt_succ_self t), hr⟩
    · refine ⟨t, Nat.lt_succ_self t, ?_⟩
      simp only [daIter] at h
      unfold daStep at h
      split at h
      · split_ifs at h with hr
        · rcases mem_insert.1 h with rfl | h
          · exact hr
          · exact absurd h hold
        · exact absurd h hold
      · exact absurd h hold

/-- A woman's best current proposal only improves over time. -/
lemma exists_proposer_ge {w : W} {u t : ℕ} (hut : u ≤ t) {m₁ : M}
    (h₁ : proposal um (daIter um uw u) m₁ = some w) :
    ∃ m₂, proposal um (daIter um uw t) m₂ = some w ∧ uw w m₁ ≤ uw w m₂ := by
  induction t, hut using Nat.le_induction with
  | base => exact ⟨m₁, h₁, le_rfl⟩
  | succ t _ ih =>
    obtain ⟨m₂, h₂, hle⟩ := ih
    obtain ⟨b, hb, -, hbmax⟩ := exists_best_proposer (uw := uw) (daIter um uw t) h₂
    exact ⟨b, hb, hle.trans (hbmax m₂ h₂)⟩

end Iter

section Mechanism

variable {um : M → W → ℝ} {uw : W → M → ℝ}

/-- The DA matching is **stable**. -/
theorem daMatching_isStable (huw : ∀ w, Function.Injective (uw w)) :
    IsStableMatching um uw (daMatching um uw) := by
  have hinv := daIter_inv (um := um) (uw := uw) (daRounds M W)
  have hterm := daFinal_noRejection (um := um) (uw := uw)
  rw [daIter_daRounds] at hinv
  refine ⟨fun m₁ m₂ w h₁ h₂ => ?_, ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne ((huw w).ne hne) with hlt | hlt
    · exact hterm m₁ w ⟨h₁, m₂, h₂, hlt⟩
    · exact hterm m₂ w ⟨h₂, m₁, h₁, hlt⟩
  · rintro m w ⟨hm, hw⟩
    have hwR : w ∈ daFinal um uw m := by
      by_contra hwR
      obtain ⟨w', hw'⟩ := proposal_isSome (um := um) hwR
      exact (hm w' hw').not_ge ((proposal_spec hw').2 w hwR)
    obtain ⟨m', hm', hlt⟩ := hinv m w hwR
    exact (hw m' hm').not_gt hlt

/-- The DA matching is **men-optimal** among stable matchings. -/
theorem daMatching_menOptimal (hum : ∀ m, Function.Injective (um m))
    (ν : M → Option W) (hν : IsStableMatching um uw ν) (m : M) (w' : W) (hνm : ν m = some w') :
    ∃ w, daMatching um uw m = some w ∧ um m w' ≤ um m w := by
  have hopt := daIter_optInv (uw := uw) hum (daRounds M W)
  rw [daIter_daRounds] at hopt
  have hw'R : w' ∉ daFinal um uw m := fun h => hopt m w' h ν hν hνm
  obtain ⟨w, hw⟩ := proposal_isSome (um := um) hw'R
  exact ⟨w, hw, (proposal_spec hw).2 w' hw'R⟩

/-- **Blocking lemma** (Gale–Sotomayor 1985). Let `μ` be the men-proposing DA matching and
`μ'` any matching that some man strictly prefers. Then some pair `(m₀, w)` blocks `μ'`, where
`m₀` does not strictly prefer `μ'` to `μ`, and `w ∈ μ'(M')`: she is matched under `μ'` to a
man who strictly prefers `μ'` (Roth–Sotomayor 1990, Lemma 3.5). -/
theorem gs_blocking_lemma (hum : ∀ m, Function.Injective (um m))
    (huw : ∀ w, Function.Injective (uw w)) (μ' : M → Option W) (hμ' : IsMatching μ')
    (hM' : ∃ m, Improves um (daMatching um uw) μ' m) :
    ∃ m₀ w, ¬ Improves um (daMatching um uw) μ' m₀ ∧ IsBlocking um uw μ' m₀ w ∧
      ∃ m', Improves um (daMatching um uw) μ' m' ∧ μ' m' = some w := by
  classical
  set μ := daMatching um uw with hμdef
  set Rf := daFinal um uw
  have hstab : IsStableMatching um uw μ := daMatching_isStable huw
  have hμspec : ∀ m w, μ m = some w → w ∉ Rf m := fun m w h => (proposal_spec h).1
  -- If `m₀` does not improve, his `μ'`-partner is no better than his `μ`-partner `w₀`.
  have notImp : ∀ m₀ w'', ¬ Improves um μ μ' m₀ → μ' m₀ = some w'' →
      ∃ w₀, μ m₀ = some w₀ ∧ um m₀ w'' ≤ um m₀ w₀ := by
    intro m₀ w'' hn h
    by_contra hc
    push Not at hc
    exact hn ⟨w'', h, fun w0 hw0 => hc w0 hw0⟩
  set S := univ.filter (Improves um μ μ')
  by_cases hcase : ∃ m' ∈ S, ∃ w, μ' m' = some w ∧ ∀ m, μ m = some w → m ∉ S
  · -- Case 1: some woman matched in `μ'` to an improving man is not `μ`-matched to one.
    obtain ⟨m', hm'S, w, hm'w, hwS⟩ := hcase
    obtain ⟨w', hw', himp⟩ := (mem_filter.1 hm'S).2
    rw [hm'w, Option.some.injEq] at hw'
    subst hw'
    have hnb := hstab.2 m' w
    have : ¬ ∀ m'', μ m'' = some w → uw w m'' < uw w m' := fun h => hnb ⟨himp, h⟩
    push Not at this
    obtain ⟨m'', hm''w, hle⟩ := this
    have hne : m'' ≠ m' := by
      rintro rfl; exact lt_irrefl _ (himp w hm''w)
    have hlt : uw w m' < uw w m'' := lt_of_le_of_ne hle ((huw w).ne hne.symm)
    have hm''S : ¬ Improves um μ μ' m'' := fun h => hwS m'' hm''w (mem_filter.2 ⟨mem_univ _, h⟩)
    refine ⟨m'', w, hm''S, ⟨fun w'' h'' => ?_, fun m3 h3 => ?_⟩, m', (mem_filter.1 hm'S).2, hm'w⟩
    · obtain ⟨w₀, hw₀, hle'⟩ := notImp m'' w'' hm''S h''
      rw [hm''w, Option.some.injEq] at hw₀
      subst hw₀
      have : w'' ≠ w := by
        rintro rfl; exact hne (hμ' _ _ _ h'' hm'w)
      exact lt_of_le_of_ne hle' ((hum m'').ne this)
    · rw [hμ' _ _ _ h3 hm'w]; exact hlt
  · -- Case 2: every `μ'`-partner of an improving man is `μ`-matched to an improving man.
    push Not at hcase
    -- Then `μ(S) = μ'(S)`, by counting.
    have hsub : S.image μ' ⊆ S.image μ := by
      intro o ho
      obtain ⟨m', hm', rfl⟩ := mem_image.1 ho
      obtain ⟨w', hw', -⟩ := (mem_filter.1 hm').2
      obtain ⟨m, hm, hmS⟩ := hcase m' hm' w' hw'
      exact mem_image.2 ⟨m, hmS, by rw [hm, hw']⟩
    have hcard : (S.image μ').card = S.card := by
      refine card_image_of_injOn fun m₁ h₁ m₂ h₂ heq => ?_
      obtain ⟨w₁, hw₁, -⟩ := (mem_filter.1 h₁).2
      exact hμ' _ _ _ hw₁ (heq ▸ hw₁)
    have heq : S.image μ' = S.image μ :=
      eq_of_subset_of_card_le hsub (by rw [hcard]; exact card_image_le)
    have hpartner : ∀ m ∈ S, ∃ w, μ m = some w ∧ ∃ m' ∈ S, μ' m' = some w := by
      intro m hm
      obtain ⟨m', hm', he⟩ := mem_image.1 (heq ▸ mem_image_of_mem μ hm :
        μ m ∈ S.image μ')
      obtain ⟨w, hw, -⟩ := (mem_filter.1 hm').2
      exact ⟨w, by rw [← he, hw], m', hm', hw⟩
    -- The round at which each man of `S` first proposes to his final partner.
    have hex : ∀ m, ∃ t, proposal um (daIter um uw t) m = μ m :=
      fun m => ⟨daRounds M W, rfl⟩
    let s : M → ℕ := fun m => Nat.find (hex m)
    have hs : ∀ m, proposal um (daIter um uw (s m)) m = μ m := fun m => Nat.find_spec (hex m)
    have hSne : S.Nonempty := by
      obtain ⟨m, hm⟩ := hM'; exact ⟨m, mem_filter.2 ⟨mem_univ _, hm⟩⟩
    obtain ⟨mstar, hmstarS, hmax⟩ := exists_max_image S s hSne
    obtain ⟨w, hμw, m', hm'S, hm'w⟩ := hpartner mstar hmstarS
    -- Once a man of `S` has reached his final partner he stays there.
    have hstay : ∀ m ∈ S, ∀ t, s m ≤ t → proposal um (daIter um uw t) m = μ m := by
      intro m hm t ht
      obtain ⟨wm, hwm, -⟩ := hpartner m hm
      have h0 := hs m
      rw [hwm] at h0 ⊢
      exact proposal_stay hum h0 (daIter_mono ht m)
        fun h => hμspec m wm hwm (daIter_subset_daFinal t m h)
    -- `s mstar = k + 1`: at round `0` he proposes to his favourite woman.
    obtain ⟨w₁, hw₁, himp₁⟩ := (mem_filter.1 hmstarS).2
    have hspos : s mstar ≠ 0 := by
      intro h0
      have h := hs mstar
      rw [h0, hμw] at h
      have := (proposal_spec h).2 w₁ (by simp [daIter])
      exact (himp₁ w hμw).not_ge this
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hspos
    -- `m'` (whom `w` gets in `μ'`) was rejected by `w` at some round `u' ≤ k`.
    obtain ⟨w₂, hw₂, himp'⟩ := (mem_filter.1 hm'S).2
    rw [hm'w, Option.some.injEq] at hw₂
    subst hw₂
    obtain ⟨wm', hwm', -⟩ := hpartner m' hm'S
    have hwR : w ∈ Rf m' := by
      by_contra hwR
      have := (proposal_spec hwm').2 w hwR
      exact (himp' wm' hwm').not_ge this
    obtain ⟨u', -, hrej⟩ := rejected_of_mem_daIter hwR
    have hu' : u' ≤ k := by
      by_contra hu
      have := hstay m' hm'S u' ((hmax m' hm'S).trans (by omega))
      rw [hrej.1, hwm', Option.some.injEq] at this
      subst this
      exact lt_irrefl _ (himp' _ hwm')
    obtain ⟨-, m₁, hm₁, hlt₁⟩ := hrej
    obtain ⟨m₂, hm₂, hle₂⟩ := exists_proposer_ge (uw := uw) hu' hm₁
    obtain ⟨b, hb1, hbk, hbmax⟩ := exists_best_proposer (uw := uw) (daIter um uw k) hm₂
    have hb1' : proposal um (daIter um uw (k + 1)) b = some w := hb1
    -- `b ≠ mstar`, since `mstar` first proposes to `w` at round `k + 1`.
    have hbne : b ≠ mstar := by
      rintro rfl
      have := Nat.find_min (hex b) (show k < s b by omega)
      exact this (by rw [hbk, hμw])
    -- `b` does not improve: otherwise he would already be at his final partner `w`.
    have hbS : ¬ Improves um μ μ' b := by
      intro hbI
      have hbS : b ∈ S := mem_filter.2 ⟨mem_univ _, hbI⟩
      have := hstay b hbS (k + 1) (by have := hmax b hbS; omega)
      rw [hb1'] at this
      exact hbne (hstab.1 _ _ _ this.symm hμw)
    refine ⟨b, w, hbS, ⟨fun w'' h'' => ?_, fun m3 h3 => ?_⟩, m', (mem_filter.1 hm'S).2, hm'w⟩
    · obtain ⟨w₀, hw₀, hle₀⟩ := notImp b w'' hbS h''
      have hw₀ne : w₀ ≠ w := by
        rintro rfl; exact hbne (hstab.1 _ _ _ hw₀ hμw)
      have hle : um b w₀ ≤ um b w :=
        (proposal_spec hbk).2 w₀ fun h => hμspec b w₀ hw₀ (daIter_subset_daFinal k b h)
      exact lt_of_le_of_lt hle₀ (lt_of_le_of_ne hle ((hum b).ne hw₀ne))
    · rw [hμ' _ _ _ h3 hm'w]
      exact hlt₁.trans_le (hle₂.trans (hbmax m₂ hm₂))

/-- **Strategy-proofness of deferred acceptance for the proposing side** (Dubins–Freedman
1981; Roth 1982). Fix the women's preferences and all men's reports other than `m`'s. If `m`
reports `um' m` instead of his true utility `um m`, the DA matching does not give him a
partner he truly prefers to his partner under truthful reporting.

Scope: as in `Matching/GaleShapley.lean` everybody is acceptable to everybody, so a report is
a ranking of all women and truncation strategies (declaring women unacceptable) are not in the
strategy space; and only individual manipulation is covered, not the coalitional version of
Dubins–Freedman. -/
theorem daMatching_strategyproof (um um' : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w)) (m : M)
    (hsame : ∀ m'', m'' ≠ m → um' m'' = um m'') :
    ¬ Improves um (daMatching um uw) (daMatching um' uw) m := by
  intro himp
  have hstab' : IsStableMatching um' uw (daMatching um' uw) := daMatching_isStable huw
  obtain ⟨m₀, w, hn, hblock, -⟩ := gs_blocking_lemma hum huw _ hstab'.1 ⟨m, himp⟩
  have hne : m₀ ≠ m := by rintro rfl; exact hn himp
  refine hstab'.2 m₀ w ⟨fun w'' h => ?_, hblock.2⟩
  rw [hsame m₀ hne]
  exact hblock.1 w'' h

end Mechanism

end Econ
