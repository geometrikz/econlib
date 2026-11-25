/-
# Exact market clearing under aggregate free disposal

Companion to `GE/ExistenceArrowDebreu.lean` (MWG ch. 17 and its appendix on
production; Debreu 1959 ch. 5).

`exists_walrasianEquilibrium_arrowDebreu_lns` gets exact clearing from a single
firm with free disposal. Here free disposal is imposed on the **aggregate**
technology `Y = ∑ⱼ Yⱼ`, in the MWG 5.B.2(vi) form `Y − ℝᴸ₊ ⊆ Y`, which is
weaker. (Debreu 1959, §3.3(e) and §5.7(b.4), assumes only `−Ω ⊆ Y`, which is
equivalent under additivity `Y + Y ⊆ Y` but weaker in general; that literal form
is not covered here.) Other differences from Debreu's §5.7, inherited from the
base theorem: each `Yⱼ` (rather than `Y`) is closed and convex, consumption sets
are `ℝᴸ₊`, endowments are strictly positive and preferences come from
continuous utilities.

* `freeDisposal_aggProd_of_firm`: one free-disposal firm gives aggregate free
  disposal;
* `exists_walrasianEquilibrium_arrowDebreu_aggFD`: aggregate free disposal is
  enough (and makes no free lunch automatic, as in Debreu) for an exact-clearing equilibrium with prices in the simplex. The
  excess supply `z ≤ 0` is absorbed by re-choosing production plans that add up
  to `∑ⱼ yⱼ + z`; since `p · z = 0` and each firm already maximizes profit, the
  new plans still maximize profit and leave every consumer's wealth unchanged.
* `disposalEconomy_*`: two firms, one able to dispose only of good `0` and the
  other only of good `1`. Neither firm has free disposal, but their sum (the
  nonpositive orthant) does. With the consumer of `badEconomy`, who regards
  good `1` as a bad, an exact-clearing equilibrium exists (compare
  `badEconomy_no_walrasianEquilibrium`, where no disposal is possible).
-/
module

public import EconLean.GE.ExistenceWitnesses

@[expose] public section

noncomputable section

namespace Econ

open Set Finset

namespace ProductionEconomy

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

omit [Fintype ι] in
/-- If one firm has free disposal, so does the aggregate technology. -/
theorem freeDisposal_aggProd_of_firm (E : ProductionEconomy α β ι)
    {j0 : β} (hj0 : FreeDisposal (E.prod j0)) :
    FreeDisposal E.aggProd := by
  classical
  rintro _ ⟨y, hy, rfl⟩ y' hle
  refine ⟨fun j => y j + if j = j0 then y' - ∑ k, y k else 0, fun j => ?_, ?_⟩
  · by_cases h : j = j0
    · subst h
      simp only [ite_true]
      refine hj0 _ (hy j) _ fun i => ?_
      have := hle i
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      linarith
    · simpa [h] using hy j
  · simp [Finset.sum_add_distrib]

omit [Fintype ι] in
/-- With inaction possible, aggregate free disposal and irreversibility imply
no free lunch. -/
theorem noFreeLunch_of_freeDisposal (E : ProductionEconomy α β ι)
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hirr : Irreversible E.aggProd)
    (hfd : FreeDisposal E.aggProd) : NoFreeLunch E.aggProd := by
  intro y hy h0
  have hz : (0 : ι → ℝ) ∈ E.aggProd := ⟨fun _ => 0, hY0, by simp⟩
  exact hirr y hy (hfd 0 hz (-y) (fun i => by have := h0 i; simp at this ⊢; linarith))

/-- **Arrow–Debreu existence with aggregate free disposal.** As
`exists_walrasianEquilibrium_arrowDebreu_lns`, but with free disposal of the
aggregate technology `∑ⱼ Yⱼ` (MWG 5.B.2(vi) form) instead of a single
free-disposal firm, and with no free lunch dropped (it follows): markets clear
exactly at prices in the simplex. -/
theorem exists_walrasianEquilibrium_arrowDebreu_aggFD [Nonempty ι]
    (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hqc : ∀ a, QuasiconcaveOn ℝ (Ici 0) (u a))
    (hlns : ∀ a, LocallyNonsatiated (prefOf (u a)))
    (hωa : ∀ a, PositivePrices (E.endow a))
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j))
    (hirr : Irreversible E.aggProd) (hfd : FreeDisposal E.aggProd) :
    ∃ p x y, p ∈ priceSimplex ι ∧ E.IsWalrasianEquilibrium p x y := by
  classical
  have hnfl := E.noFreeLunch_of_freeDisposal hY0 hirr hfd
  obtain ⟨p, x, y, hpΔ, hprofit, hdem, hle, hcz0⟩ :=
    E.exists_freeDisposalEquilibrium_arrowDebreu hpref hu hqc hlns hωa hY0 hYcl hYcv hnfl hirr
  set z := ∑ a, x a - E.totalEndowment - ∑ j, y j with hz
  have hzle : ∑ j, y j + z ≤ ∑ j, y j := fun i => by
    have := hle i
    simp only [hz, Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at this ⊢
    linarith
  obtain ⟨y', hy', hsum⟩ := hfd _ ⟨y, fun j => (hprofit j).1, rfl⟩ _ hzle
  -- each firm's new profit is at most its old (maximal) profit, and the totals agree
  have hle' : ∀ j ∈ (Finset.univ : Finset β), cost p (y' j) ≤ cost p (y j) := fun j _ =>
    (hprofit j).2 _ (hy' j)
  have htot : ∑ j, cost p (y' j) = ∑ j, cost p (y j) := by
    rw [← cost_sum, ← cost_sum, hsum, cost_add_right, hcz0,
      add_zero]
  have hcost : ∀ j, cost p (y' j) = cost p (y j) := fun j =>
    (Finset.sum_eq_sum_iff_of_le hle').1 htot j (Finset.mem_univ j)
  have hwealth : ∀ a, E.wealth p y' a = E.wealth p y a := fun a => by
    simp only [wealth, hcost]
  refine ⟨p, x, y', hpΔ, fun j => ⟨hy' j, fun y'' hy'' => ?_⟩, fun a => ?_, ?_⟩
  · rw [hcost]; exact (hprofit j).2 y'' hy''
  · rw [hwealth]; exact hdem a
  · rw [hsum, hz]; abel

end ProductionEconomy

namespace GEExamples

open ProductionEconomy

/-- A firm that can only throw away good `0`. -/
def dispose0 : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 = 0}

/-- A firm that can only throw away good `1`. -/
def dispose1 : Set (Fin 2 → ℝ) := {y | y 0 = 0 ∧ y 1 ≤ 0}

theorem isClosed_dispose0 : IsClosed dispose0 :=
  show IsClosed ({y : Fin 2 → ℝ | y 0 ≤ 0} ∩ {y | y 1 = 0}) from
  (isClosed_le (continuous_apply 0) continuous_const).inter
    (isClosed_eq (continuous_apply 1) continuous_const)

theorem isClosed_dispose1 : IsClosed dispose1 :=
  show IsClosed ({y : Fin 2 → ℝ | y 0 = 0} ∩ {y | y 1 ≤ 0}) from
  (isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_le (continuous_apply 1) continuous_const)

theorem convex_dispose0 : Convex ℝ dispose0 := by
  intro x hx y hy a b ha hb hab
  simp only [dispose0, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  exact ⟨by nlinarith [hx.1, hy.1], by rw [hx.2, hy.2]; ring⟩

theorem convex_dispose1 : Convex ℝ dispose1 := by
  intro x hx y hy a b ha hb hab
  simp only [dispose1, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  exact ⟨by rw [hx.1, hy.1]; ring, by nlinarith [hx.2, hy.2]⟩

theorem not_freeDisposal_dispose0 : ¬ FreeDisposal dispose0 := by
  intro h
  have := h 0 (by simp [dispose0]) ![0, -1] (fun i => by fin_cases i <;> simp)
  simp [dispose0] at this

theorem not_freeDisposal_dispose1 : ¬ FreeDisposal dispose1 := by
  intro h
  have := h 0 (by simp [dispose1]) ![-1, 0] (fun i => by fin_cases i <;> simp)
  simp [dispose1] at this

/-- The consumer of `badEconomy` (good `1` is a bad, endowment `(1, 1)`), owning
two disposal firms, each able to dispose of only one good. -/
def disposalEconomy : ProductionEconomy (Fin 1) (Fin 2) (Fin 2) where
  pref _ := prefOf uBad
  endow _ := fun _ => 1
  endow_nonneg _ _ := by norm_num
  prod j := if j = 0 then dispose0 else dispose1
  share _ _ := 1
  share_nonneg _ _ := by norm_num
  share_sum _ := by simp

theorem disposalEconomy_aggProd : disposalEconomy.aggProd = {y | y ≤ 0} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have h0 : y 0 ∈ dispose0 := by simpa [disposalEconomy] using hy 0
    have h1 : y 1 ∈ dispose1 := by simpa [disposalEconomy] using hy 1
    simp only [dispose0, dispose1, mem_ofPred_eq] at h0 h1
    fin_cases i <;> simp [Fin.sum_univ_two] <;> linarith [h0.1, h0.2, h1.1, h1.2]
  · intro hz
    refine ⟨![![z 0, 0], ![0, z 1]], fun j => ?_, ?_⟩
    · fin_cases j
      · simpa [disposalEconomy, dispose0] using hz 0
      · simpa [disposalEconomy, dispose1] using hz 1
    · funext i; fin_cases i <;> simp [Fin.sum_univ_two]

/-- Neither firm can dispose freely, but the aggregate technology can. -/
theorem disposalEconomy_freeDisposal :
    FreeDisposal disposalEconomy.aggProd ∧ ∀ j, ¬ FreeDisposal (disposalEconomy.prod j) := by
  refine ⟨?_, fun j => ?_⟩
  · rw [disposalEconomy_aggProd]
    intro y hy y' hle
    exact le_trans hle hy
  · fin_cases j
    · simpa [disposalEconomy] using not_freeDisposal_dispose0
    · simpa [disposalEconomy] using not_freeDisposal_dispose1

/-- **Exact clearing with a bad, via aggregate disposal.** -/
theorem disposalEconomy_exists_equilibrium :
    ∃ p x y, p ∈ priceSimplex (Fin 2) ∧ disposalEconomy.IsWalrasianEquilibrium p x y := by
  refine disposalEconomy.exists_walrasianEquilibrium_arrowDebreu_aggFD (u := fun _ => uBad)
    (fun _ => rfl) (fun _ => continuous_uBad) (fun _ => quasiconcaveOn_uBad) (fun _ => lns_uBad)
    (fun _ _ => by simp [disposalEconomy]) (fun j => ?_) (fun j => ?_) (fun j => ?_) ?_
    disposalEconomy_freeDisposal.1
  · fin_cases j <;> simp [disposalEconomy, dispose0, dispose1]
  · fin_cases j
    · simpa [disposalEconomy] using isClosed_dispose0
    · simpa [disposalEconomy] using isClosed_dispose1
  · fin_cases j
    · simpa [disposalEconomy] using convex_dispose0
    · simpa [disposalEconomy] using convex_dispose1
  · rw [disposalEconomy_aggProd]
    intro y hy hny
    exact le_antisymm hy (fun i => by have := hny i; simp at this; simpa using this)

end GEExamples
end Econ
