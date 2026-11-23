/-
# Frozen statements: behavioral decision theory

Headline statements of `Behavioral/PresentBias.lean`, `RankDependent.lean`,
`ReferenceDependence.lean`, `Temptation.lean` and `Logit.lean`, copied
verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.PresentBias
public import EconLean.Behavioral.RankDependent
public import EconLean.Behavioral.ReferenceDependence
public import EconLean.Behavioral.Temptation
public import EconLean.Behavioral.Logit

@[expose] public section

-- The uniform closing tactic `apply … <;> assumption` is sometimes more than
-- needed; silence the style linters that would flag that.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Econ.Audit.Behavioral

open Finset

section PresentBias
open Econ.PresentBias

theorem frozen_exponential_timeConsistent {δ : ℝ} (hδ : 0 < δ) {t t' s s' : ℕ}
    (htt' : t ≤ t') (hs : t' ≤ s) (hs' : t' ≤ s') (a b : ℝ) :
    presentValue 1 δ t b s' < presentValue 1 δ t a s ↔
      presentValue 1 δ t' b s' < presentValue 1 δ t' a s := by
  apply @Econ.PresentBias.exponential_timeConsistent <;> assumption

theorem frozen_exists_preferenceReversal_iff {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) :
    (∃ a b : ℝ, ∃ s : ℕ, 0 < a ∧ 0 < b ∧ PreferenceReversal β δ a b s) ↔ β < 1 := by
  apply @Econ.PresentBias.exists_preferenceReversal_iff <;> assumption

theorem frozen_not_preferenceReversal_of_beta_one {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) (s : ℕ) :
    ¬ PreferenceReversal 1 δ a b s := by
  apply @Econ.PresentBias.not_preferenceReversal_of_beta_one <;> assumption

open Econ.PresentBias.Task
variable (P : Task)

theorem frozen_soph_le_naive (β : ℝ) : P.sophDate β ≤ P.naiveDate β := by
  apply @Econ.PresentBias.Task.soph_le_naive <;> assumption

theorem frozen_sophFrom_spec (β : ℝ) {t : ℕ} (ht : t < P.T) :
    (P.sophFrom β t = t ↔ P.U β t (P.sophFrom β (t + 1)) ≤ P.U β t t) := by
  apply @Econ.PresentBias.Task.sophFrom_spec <;> assumption

theorem frozen_tcDate_spec : 1 ≤ P.tcDate ∧ P.tcDate ≤ P.T ∧
    ∀ τ, P.tcDate < τ → τ ≤ P.T → P.w τ ≤ P.w P.tcDate := by
  apply @Econ.PresentBias.Task.tcDate_spec <;> assumption

theorem frozen_tc_le_naive_of_immediateCosts (hs : P.schedule = .immediateCosts)
    (hc : ∀ τ, 0 ≤ P.c τ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    P.tcDate ≤ P.naiveDate β := by
  apply @Econ.PresentBias.Task.tc_le_naive_of_immediateCosts <;> assumption

theorem frozen_naive_le_tc_of_immediateRewards (hs : P.schedule = .immediateRewards)
    (hv : ∀ τ, 0 ≤ P.v τ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    P.naiveDate β ≤ P.tcDate := by
  apply @Econ.PresentBias.Task.naive_le_tc_of_immediateRewards <;> assumption

theorem frozen_report_dates :
    report.tcDate = 1 ∧ report.sophDate (1 / 2) = 2 ∧ report.naiveDate (1 / 2) = 4 := by
  apply @Econ.PresentBias.Task.report_dates <;> assumption

theorem frozen_movie_dates :
    movie.tcDate = 4 ∧ movie.sophDate (1 / 2) = 1 ∧ movie.naiveDate (1 / 2) = 3 := by
  apply @Econ.PresentBias.Task.movie_dates <;> assumption

end PresentBias

section RankDependent
open Econ.RankDependent
variable {n : ℕ}

theorem frozen_fosd_iff_eu (p q : Lottery n) :
    FOSD p q ↔ ∀ u : ℕ → ℝ, MonotoneOnGrid n u → eu u q ≤ eu u p := by
  apply @Econ.RankDependent.fosd_iff_eu <;> assumption

theorem frozen_rdu_eq_layer {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) (u : ℕ → ℝ) (p : Lottery n) :
    rdu w u p = u 0 + ∑ k ∈ range n, w (G p (k + 1)) * (u (k + 1) - u k) := by
  apply @Econ.RankDependent.rdu_eq_layer <;> assumption

theorem frozen_decisionWeight_nonneg {w : ℝ → ℝ} (hw : Monotone w) (p : Lottery n) {k : ℕ}
    (hk : k ≤ n) : 0 ≤ decisionWeight w p k := by
  apply @Econ.RankDependent.decisionWeight_nonneg <;> assumption

theorem frozen_sum_decisionWeight {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) (p : Lottery n) :
    ∑ k ∈ range (n + 1), decisionWeight w p k = 1 := by
  apply @Econ.RankDependent.sum_decisionWeight <;> assumption

theorem frozen_rdu_id (u : ℕ → ℝ) (p : Lottery n) : rdu id u p = eu u p := by
  apply @Econ.RankDependent.rdu_id <;> assumption

theorem frozen_rdu_mono {w : ℝ → ℝ} (hw : Monotone w) (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    {u : ℕ → ℝ} (hu : MonotoneOnGrid n u) {p q : Lottery n} (h : FOSD p q) :
    rdu w u q ≤ rdu w u p := by
  apply @Econ.RankDependent.rdu_mono <;> assumption

theorem frozen_rdu_strictMono {w : ℝ → ℝ} (hw : StrictMono w) (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    {u : ℕ → ℝ} (hu : ∀ k, k < n → u k < u (k + 1)) {p q : Lottery n} (h : FOSD p q)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hk₀n : k₀ ≤ n) (hstrict : G q k₀ < G p k₀) :
    rdu w u q < rdu w u p := by
  apply @Econ.RankDependent.rdu_strictMono <;> assumption

theorem frozen_opt_violates_fosd {π : ℝ → ℝ} (hπ0 : π 0 = 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b ≤ 1) (hsub : π (a + b) < π a + π b) :
    ∃ (v : ℕ → ℝ) (p q : Lottery 3), (∀ k, k < 3 → v k < v (k + 1)) ∧
      FOSD p q ∧ opt π v p < opt π v q := by
  exact Econ.RankDependent.opt_violates_fosd hπ0 ha hb hab hsub

theorem frozen_cpt_mono {wp wm : ℝ → ℝ} (hwp : Monotone wp) (hwm : Monotone wm) {v : ℕ → ℝ}
    (hv : MonotoneOnGrid n v) {r : ℕ} (hr : r ≤ n) {p q : Lottery n} (h : FOSD p q) :
    cpt wp wm v r q ≤ cpt wp wm v r p := by
  apply @Econ.RankDependent.cpt_mono <;> assumption

theorem frozen_cpt_id {v : ℕ → ℝ} {r : ℕ} (hr : r ≤ n) (hvr : v r = 0) (p : Lottery n) :
    cpt id id v r p = eu v p := by
  apply @Econ.RankDependent.cpt_id <;> assumption

theorem frozen_cpt_zero_eq_rdu {wp : ℝ → ℝ} (hw0 : wp 0 = 0) (hw1 : wp 1 = 1) (wm : ℝ → ℝ)
    {v : ℕ → ℝ} (hv0 : v 0 = 0) (p : Lottery n) :
    cpt wp wm v 0 p = rdu wp v p := by
  apply @Econ.RankDependent.cpt_zero_eq_rdu <;> assumption

theorem frozen_cpt_statusQuo {wp wm : ℝ → ℝ} (hwp : wp 0 = 0) (hwm : wm 0 = 0) (v : ℕ → ℝ) {r : ℕ}
    (hr : r ≤ n) (p : Lottery n) (hp : ∀ k, k ≤ n → k ≠ r → p.p k = 0) :
    cpt wp wm v r p = 0 := by
  apply @Econ.RankDependent.cpt_statusQuo <;> assumption

theorem frozen_cpt_rejects_fair_coin {wp wm : ℝ → ℝ} {v : ℕ → ℝ} (hv1 : v 1 = 0) (hv2 : 0 ≤ v 2)
    (hloss : v 0 + v 2 < 0) (hw : 0 < wp (1 / 2)) (hww : wp (1 / 2) ≤ wm (1 / 2)) :
    cpt wp wm v 1 fairCoin < 0 := by
  apply @Econ.RankDependent.cpt_rejects_fair_coin <;> assumption

theorem frozen_tkValue_lossAverse {α lam : ℝ} (hlam : 1 < lam) {x : ℝ} (hx : 0 < x) :
    tkValue α α lam (-x) < -tkValue α α lam x := by
  apply @Econ.RankDependent.tkValue_lossAverse <;> assumption

theorem frozen_tk_rejects_fair_coin {α lam : ℝ} (hα : 0 < α) (hlam : 1 < lam) {x : ℝ} (hx : 0 < x)
    {wp wm : ℝ → ℝ} (hw : 0 < wp (1 / 2)) (hww : wp (1 / 2) ≤ wm (1 / 2)) :
    cpt wp wm (fun k => tkValue α α lam (((k : ℝ) - 1) * x)) 1 fairCoin < 0 := by
  apply @Econ.RankDependent.tk_rejects_fair_coin <;> assumption

end RankDependent

section ReferenceDependence
open Econ.ReferenceDependence
variable {K : Type*} [Fintype K]

section Stochastic
variable {ι : Type*} [Fintype ι] (bundle : ι → K → ℝ)

theorem frozen_exists_ppe {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)} (hD : D.Finite)
    (hPE : ∃ F, IsPE bundle μ m D F) : ∃ F, IsPPE bundle μ m D F := by
  apply @Econ.ReferenceDependence.exists_ppe <;> assumption

theorem frozen_exists_cpe {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)} (hL : IsLotterySet D)
    (hD : D.Finite) (hne : D.Nonempty) : ∃ F, IsCPE bundle μ m D F := by
  apply @Econ.ReferenceDependence.exists_cpe <;> assumption

-- Added 2026-11-23 after the independent review (record: Audit/REVIEW-behavioral-4.md).
theorem frozen_exists_pe {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)} (hL : IsLotterySet D)
    (hconv : Convex ℝ D) (hcomp : IsCompact D) (hne : D.Nonempty) :
    ∃ F, IsPE bundle μ m D F := by
  apply @Econ.ReferenceDependence.exists_pe <;> assumption

theorem frozen_exists_ppe_of_convex {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)}
    (hL : IsLotterySet D) (hconv : Convex ℝ D) (hcomp : IsCompact D) (hne : D.Nonempty) :
    ∃ F, IsPPE bundle μ m D F := by
  apply @Econ.ReferenceDependence.exists_ppe_of_convex <;> assumption

theorem frozen_U_pure [DecidableEq ι] (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (i j : ι) :
    U bundle μ m (Pi.single i 1) (Pi.single j 1) = u μ m (bundle i) (bundle j) := by
  apply @Econ.ReferenceDependence.U_pure <;> assumption

end Stochastic

theorem frozen_isPEDet_of_isMax {η lam : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (m : K → ℝ → ℝ)
    {D : Set (K → ℝ)} {c : K → ℝ} (hc : c ∈ D)
    (hmax : ∀ c' ∈ D, consumptionUtility m c' ≤ consumptionUtility m c) :
    IsPEDet (μLin η lam) m D c := by
  apply @Econ.ReferenceDependence.isPEDet_of_isMax <;> assumption

theorem frozen_exists_ppeDet {η lam : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (m : K → ℝ → ℝ)
    {D : Set (K → ℝ)} (hD : D.Finite) (hne : D.Nonempty) :
    ∃ c, IsPPEDet (μLin η lam) m D c := by
  apply @Econ.ReferenceDependence.exists_ppeDet <;> assumption

theorem frozen_two_PE_example :
    let D : Set (Fin 2 → ℝ) := {![1, 0], ![0, 1]}
    IsPEDet (μLin 1 3) (fun _ x => x) D ![1, 0] ∧ IsPEDet (μLin 1 3) (fun _ x => x) D ![0, 1] := by
  apply @Econ.ReferenceDependence.two_PE_example <;> assumption

theorem frozen_sell_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hv : 0 ≤ v) (hp : 0 ≤ p) :
    u (μLin η lam) (mugMoney v) ![1, 0] ![1, 0] ≤ u (μLin η lam) (mugMoney v) ![0, p] ![1, 0] ↔
      WTA η lam v ≤ p := by
  apply @Econ.ReferenceDependence.sell_iff <;> assumption

theorem frozen_buy_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (hv : 0 ≤ v) (hp : 0 ≤ p) :
    u (μLin η lam) (mugMoney v) ![0, 0] ![0, 0] ≤ u (μLin η lam) (mugMoney v) ![1, -p] ![0, 0] ↔
      p ≤ WTP η lam v := by
  apply @Econ.ReferenceDependence.buy_iff <;> assumption

theorem frozen_endowment_effect {η lam v : ℝ} (hη : 0 < η) (hlam : 1 ≤ lam) (hv : 0 < v) :
    WTP η lam v < WTA η lam v ↔ 1 < lam := by
  apply @Econ.ReferenceDependence.endowment_effect <;> assumption

theorem frozen_keep_isPE_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hv : 0 < v) (hp : 0 < p) :
    IsPEDet (μLin η lam) (mugMoney v) {keep, sell p} keep ↔ p ≤ WTA η lam v := by
  apply @Econ.ReferenceDependence.keep_isPE_iff <;> assumption

theorem frozen_sell_isPE_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (hv : 0 < v) (hp : 0 < p) :
    IsPEDet (μLin η lam) (mugMoney v) {keep, sell p} (sell p) ↔ WTP η lam v ≤ p := by
  apply @Econ.ReferenceDependence.sell_isPE_iff <;> assumption

end ReferenceDependence

section Temptation
open Econ.Temptation
variable {X : Type*}

theorem frozen_W_le_max_u (u v : X → ℝ) (A : Finset X) (hA : A.Nonempty) :
    W u v A hA ≤ A.sup' hA u := by
  apply @Econ.Temptation.W_le_max_u <;> assumption

theorem frozen_setBetweenness [DecidableEq X] (u v : X → ℝ) {A B : Finset X} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : W u v B hB ≤ W u v A hA) :
    W u v (A ∪ B) (hA.mono Finset.subset_union_left) ≤ W u v A hA ∧
      W u v B hB ≤ W u v (A ∪ B) (hA.mono Finset.subset_union_left) := by
  apply @Econ.Temptation.setBetweenness <;> assumption

theorem frozen_commitment_strict [DecidableEq X] (u v : X → ℝ) {x y : X} (htempt : v x < v y)
    (hresist : u y + v y ≤ u x + v x) :
    W u v {x, y} (Finset.insert_nonempty x {y}) < W u v {x} (Finset.singleton_nonempty x) := by
  apply @Econ.Temptation.commitment_strict <;> assumption

theorem frozen_W_pair_succumb [DecidableEq X] (u v : X → ℝ) {x y : X} (htempt : v x ≤ v y)
    (hsuccumb : u x + v x ≤ u y + v y) :
    W u v {x, y} (Finset.insert_nonempty x {y}) = u y := by
  apply @Econ.Temptation.W_pair_succumb <;> assumption

theorem frozen_W_union_of_not_tempting [DecidableEq X] (u v : X → ℝ) {A B : Finset X} (hA : A.Nonempty)
    (hB : B.Nonempty) (hv : B.sup' hB v ≤ A.sup' hA v) :
    W u v A hA ≤ W u v (A ∪ B) (hA.mono Finset.subset_union_left) := by
  apply @Econ.Temptation.W_union_of_not_tempting <;> assumption

end Temptation

section Logit
open Econ.Logit Real
variable {ι : Type*} [Fintype ι] {lam : ℝ} {P v : ι → ℝ}

theorem frozen_objective_generalizedLogit [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i) :
    objective lam P v (generalizedLogit lam P v) = lam * log (Z lam P v) := by
  apply @Econ.Logit.objective_generalizedLogit <;> assumption

theorem frozen_generalizedLogit_optimal [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i)
    {p : ι → ℝ} (hp : IsProb p) :
    objective lam P v p ≤ objective lam P v (generalizedLogit lam P v) := by
  apply @Econ.Logit.generalizedLogit_optimal <;> assumption

theorem frozen_eq_generalizedLogit_of_optimal [Nonempty ι] (hlam : 0 < lam) (hP : ∀ i, 0 < P i)
    {p : ι → ℝ} (hp : IsProb p)
    (hopt : objective lam P v (generalizedLogit lam P v) ≤ objective lam P v p) :
    p = generalizedLogit lam P v := by
  apply @Econ.Logit.eq_generalizedLogit_of_optimal <;> assumption

theorem frozen_generalizedLogit_const_eq_softmax (lam : ℝ) (v : ι → ℝ) :
    generalizedLogit lam (fun _ => 1) v = softmax lam v := by
  apply @Econ.Logit.generalizedLogit_const_eq_softmax <;> assumption

theorem frozen_softmax_optimal [Nonempty ι] (hlam : 0 < lam) {p : ι → ℝ} (hp : IsProb p) :
    IsProb (softmax lam v) ∧
      ∑ i, p i * v i + lam * entropy p ≤ ∑ i, softmax lam v i * v i + lam * entropy (softmax lam v) ∧
      (∑ i, softmax lam v i * v i + lam * entropy (softmax lam v) ≤ ∑ i, p i * v i + lam * entropy p →
        p = softmax lam v) := by
  apply @Econ.Logit.softmax_optimal <;> assumption

end Logit

end Econ.Audit.Behavioral
