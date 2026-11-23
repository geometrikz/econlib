/-
# Reference-dependent preferences (Kőszegi–Rabin 2006)

Reference. B. Kőszegi and M. Rabin (2006), "A Model of Reference-Dependent
Preferences", *QJE* 121(4). Also Kőszegi–Rabin (2007), *AER* 97(4), for
choice-acclimating personal equilibrium.

**The model.** Consumption bundles are `c : K → ℝ` (finitely many dimensions
`K`, e.g. mugs and money). Utility from bundle `c` given reference bundle `r`
is

    u(c | r) = m(c) + n(c | r),   m(c) = Σₖ mₖ(cₖ),
    n(c | r) = Σₖ μ(mₖ(cₖ) - mₖ(rₖ)),

consumption utility plus gain–loss utility, dimension by dimension, where the
gain–loss function `μ` is applied to consumption-utility differences. For
random outcomes `F` and random reference points `G` (here: probability vectors
on a finite list of possible bundles) utility is the double average

    U(F | G) = Σ_c Σ_r F(c) G(r) u(c | r).

The reference point is the agent's recent *expectations*. Given a choice set
`D` of lotteries (`IsLotterySet D`: every element is a probability vector;
the equilibrium notions require it):
* `F` is a **personal equilibrium (PE)** if `F ∈ D` and `U(F' | F) ≤ U(F | F)`
  for all `F' ∈ D`: expecting `F`, the agent is willing to choose `F`.
* `F` is a **preferred personal equilibrium (PPE)** if it is a PE and
  `U(F' | F') ≤ U(F | F)` for every PE `F'`.
* (KR 2007) `F` is a **choice-acclimating PE (CPE)** if it maximizes
  `U(F | F)` over `D`.

KR's assumptions A0–A4 on `μ` include differentiability at 0; we state
general definitions for any `μ`, and prove the existence and endowment-effect
results for KR's piecewise-linear specification `μ(x) = η x` for gains,
`η λ x` for losses (`η ≥ 0`, loss aversion `λ ≥ 1`), which KR use in their
applications.

Results:
* `exists_pe`, `exists_ppe_of_convex`: on a nonempty, compact, convex set of
  lotteries (e.g. all lotteries over finitely many bundles,
  `exists_ppe_allLotteries`) a PE and a PPE exist, for any gain–loss function
  `μ` (Kakutani; `U(F' | F)` is linear in `F'`);
* `exists_ppe`: on a finite choice set with a PE, a PPE exists (on a finite
  set a PE need not exist);
* `exists_cpe`: on a finite nonempty choice set, a CPE exists;
* `isPE_det_of_isMax`: with linear `μ`, `η ≥ 0`, `λ ≥ 1`, in riskless choice
  the consumption-utility maximizer is a PE (so PE and PPE exist);
* `two_PE_example`: PE need not be unique: expectations are self-fulfilling;
* `endowment_effect`: with the status-quo expectation as reference point,
  `WTA = v (1 + ηλ) / (1 + η)`, `WTP = v (1 + η) / (1 + ηλ)`, and `WTP < WTA`
  iff `λ > 1`.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import EconLean.Behavioral.Logit
public import EconLean.Foundations.FixedPoint

@[expose] public section

namespace Econ

namespace ReferenceDependence

open Finset

variable {K : Type*} [Fintype K]

/-- Additively separable consumption utility `m(c) = Σₖ mₖ(cₖ)`. -/
def consumptionUtility (m : K → ℝ → ℝ) (c : K → ℝ) : ℝ := ∑ k, m k (c k)

/-- Gain–loss utility `n(c | r) = Σₖ μ(mₖ(cₖ) - mₖ(rₖ))`. -/
def gainLoss (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (c r : K → ℝ) : ℝ :=
  ∑ k, μ (m k (c k) - m k (r k))

/-- Reference-dependent utility `u(c | r) = m(c) + n(c | r)`. -/
def u (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (c r : K → ℝ) : ℝ :=
  consumptionUtility m c + gainLoss μ m c r

/-- KR's piecewise-linear gain–loss function: slope `η` on gains, `η λ` on
losses. -/
noncomputable def μLin (η lam : ℝ) (x : ℝ) : ℝ := if 0 ≤ x then η * x else η * lam * x

/-- With `η ≥ 0` and `λ ≥ 1`, linear gain–loss utility is never larger than
`η x`: a loss of size `x` hurts at least as much as an equal gain helps. -/
theorem μLin_le (η lam : ℝ) (hη : 0 ≤ η) (hlam : 1 ≤ lam) (x : ℝ) : μLin η lam x ≤ η * x := by
  unfold μLin
  split_ifs with h
  · exact le_rfl
  · push Not at h
    -- `η (λ - 1) ≥ 0` times `x < 0` is `≤ 0`.
    have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hη (sub_nonneg.2 hlam)) h.le
    nlinarith

/-! ### Stochastic outcomes and reference points -/

section Stochastic

-- Possible bundles are indexed by a finite type `ι`; a lottery is a
-- probability vector on `ι`.
variable {ι : Type*} [Fintype ι] (bundle : ι → K → ℝ)

/-- Expected reference-dependent utility `U(F | G)`: outcome drawn from `F`,
compared with every reference outcome drawn from `G`. -/
def U (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (F G : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, F i * G j * u μ m (bundle i) (bundle j)

/-- A choice set of lotteries: every element is a probability vector on `ι`. -/
def IsLotterySet (D : Set (ι → ℝ)) : Prop := ∀ G ∈ D, Logit.IsProb G

/-- **Personal equilibrium** (KR 2006, Def. 1), in the static form "choose
from `D` given expectations" (KR 2007's unacclimating PE). `D` must be a set
of lotteries. -/
def IsPE (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (D : Set (ι → ℝ)) (F : ι → ℝ) : Prop :=
  IsLotterySet D ∧ F ∈ D ∧ ∀ F' ∈ D, U bundle μ m F' F ≤ U bundle μ m F F

/-- **Preferred personal equilibrium** (KR 2006, Def. 2). -/
def IsPPE (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (D : Set (ι → ℝ)) (F : ι → ℝ) : Prop :=
  IsPE bundle μ m D F ∧ ∀ F', IsPE bundle μ m D F' → U bundle μ m F' F' ≤ U bundle μ m F F

/-- **Choice-acclimating personal equilibrium** (KR 2007). -/
def IsCPE (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (D : Set (ι → ℝ)) (F : ι → ℝ) : Prop :=
  IsLotterySet D ∧ F ∈ D ∧ ∀ F' ∈ D, U bundle μ m F' F' ≤ U bundle μ m F F

/-- On a finite choice set, if a personal equilibrium exists then a preferred
personal equilibrium exists. (On a finite set a PE need not exist; on a
convex compact set of lotteries it always does, `exists_pe`.) -/
theorem exists_ppe {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)} (hD : D.Finite)
    (hPE : ∃ F, IsPE bundle μ m D F) : ∃ F, IsPPE bundle μ m D F := by
  classical
  have hS : {F | IsPE bundle μ m D F}.Finite := hD.subset fun F hF => hF.2.1
  obtain ⟨F, hF, hmax⟩ := hS.toFinset.exists_max_image (fun F => U bundle μ m F F)
    (hS.toFinset_nonempty.2 hPE)
  rw [Set.Finite.mem_toFinset] at hF
  exact ⟨F, hF, fun F' hF' => hmax F' (by simpa using hF')⟩

/-- On a finite nonempty choice set of lotteries a choice-acclimating PE
exists. -/
theorem exists_cpe {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)} (hL : IsLotterySet D)
    (hD : D.Finite) (hne : D.Nonempty) : ∃ F, IsCPE bundle μ m D F := by
  obtain ⟨F, hF, hmax⟩ := hD.toFinset.exists_max_image (fun F => U bundle μ m F F)
    (by simpa using hne)
  rw [Set.Finite.mem_toFinset] at hF
  exact ⟨F, hL, hF, fun F' hF' => hmax F' (by simpa using hF')⟩

/-- `U(F' | F)` is linear in the outcome lottery: `Σᵢ F'ᵢ wᵢ(F)`. -/
theorem U_eq_sum (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (F' F : ι → ℝ) :
    U bundle μ m F' F = ∑ i, F' i * ∑ j, F j * u μ m (bundle i) (bundle j) := by
  unfold U
  exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

theorem continuous_U (μ : ℝ → ℝ) (m : K → ℝ → ℝ) :
    Continuous fun p : (ι → ℝ) × (ι → ℝ) => U bundle μ m p.1 p.2 := by
  unfold U
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_apply i).comp continuous_fst).mul
      ((continuous_apply j).comp continuous_snd)).mul continuous_const

/- Note (review 2026-11-23): convexity of `D` lets the agent randomize among
lotteries; KR choice sets such as "buy or not" are not convex, and on them a
PE need not exist. The PE found here may be a mixture. -/
/-- **Existence of personal equilibrium** (KR 2006). On a nonempty, compact,
convex set of lotteries (e.g. all lotteries over finitely many bundles) a
personal equilibrium exists, for any gain–loss function `μ`: `U(F' | F)` is
linear in `F'` and continuous, so Kakutani applies to the best-reply
correspondence `F ↦ argmax_{F' ∈ D} U(F' | F)`. -/
theorem exists_pe {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)} (hL : IsLotterySet D)
    (hconv : Convex ℝ D) (hcomp : IsCompact D) (hne : D.Nonempty) :
    ∃ F, IsPE bundle μ m D F := by
  let φ : (ι → ℝ) → Set (ι → ℝ) := fun F =>
    {F' | F' ∈ D ∧ ∀ G ∈ D, U bundle μ m G F ≤ U bundle μ m F' F}
  have hcU : ∀ F, Continuous fun G => U bundle μ m G F := fun F =>
    (continuous_U bundle μ m).comp (continuous_id.prodMk continuous_const)
  have hmaps : ∀ F ∈ D, φ F ⊆ D := fun F _ F' h => h.1
  have hφne : ∀ F ∈ D, (φ F).Nonempty := by
    intro F _
    obtain ⟨F', hF', hmax⟩ := hcomp.exists_isMaxOn hne (hcU F).continuousOn
    exact ⟨F', hF', fun G hG => hmax hG⟩
  have hφconv : ∀ F ∈ D, Convex ℝ (φ F) := by
    intro F _ F₁ h₁ F₂ h₂ a b ha hb hab
    refine ⟨hconv h₁.1 h₂.1 ha hb hab, fun G hG => ?_⟩
    have e : U bundle μ m (a • F₁ + b • F₂) F =
        a * U bundle μ m F₁ F + b * U bundle μ m F₂ F := by
      simp only [U_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
        mul_sum, mul_assoc]
    rw [e]
    have k1 := mul_le_mul_of_nonneg_left (h₁.2 G hG) ha
    have k2 := mul_le_mul_of_nonneg_left (h₂.2 G hG) hb
    have : U bundle μ m G F = a * U bundle μ m G F + b * U bundle μ m G F := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hgraph : IsClosed {p : (ι → ℝ) × (ι → ℝ) | p.1 ∈ D ∧ p.2 ∈ φ p.1} := by
    have e : {p : (ι → ℝ) × (ι → ℝ) | p.1 ∈ D ∧ p.2 ∈ φ p.1} =
        (Prod.fst ⁻¹' D) ∩ (Prod.snd ⁻¹' D) ∩
          ⋂ G ∈ D, {p | U bundle μ m G p.1 ≤ U bundle μ m p.2 p.1} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, φ]
      tauto
    rw [e]
    have hcl := hcomp.isClosed
    refine ((hcl.preimage continuous_fst).inter (hcl.preimage continuous_snd)).inter
      (isClosed_biInter fun G _ => isClosed_le ?_ ?_)
    · exact (continuous_U bundle μ m).comp (continuous_const.prodMk continuous_fst)
    · exact (continuous_U bundle μ m).comp (continuous_snd.prodMk continuous_fst)
  obtain ⟨F, hF, hfix⟩ := kakutani_fixedPoint hconv hcomp hne hmaps hφne hφconv hgraph
  exact ⟨F, hL, hF, fun G hG => hfix.2 G hG⟩

/-- **Existence of preferred personal equilibrium** on a nonempty, compact,
convex set of lotteries: the PE set is closed, hence compact, and `U(F | F)`
is continuous. -/
theorem exists_ppe_of_convex {μ : ℝ → ℝ} {m : K → ℝ → ℝ} {D : Set (ι → ℝ)}
    (hL : IsLotterySet D) (hconv : Convex ℝ D) (hcomp : IsCompact D) (hne : D.Nonempty) :
    ∃ F, IsPPE bundle μ m D F := by
  set P := {F | IsPE bundle μ m D F}
  have hPcl : IsClosed P := by
    have e : P = D ∩ ⋂ G ∈ D, {F | U bundle μ m G F ≤ U bundle μ m F F} := by
      ext F; simp [P, IsPE, hL]
    rw [e]
    refine hcomp.isClosed.inter (isClosed_biInter fun G _ => isClosed_le ?_ ?_)
    · exact (continuous_U bundle μ m).comp (continuous_const.prodMk continuous_id)
    · exact (continuous_U bundle μ m).comp (continuous_id.prodMk continuous_id)
  have hPc : IsCompact P := hcomp.of_isClosed_subset hPcl fun F hF => hF.2.1
  obtain ⟨F, hF, hmax⟩ := hPc.exists_isMaxOn (exists_pe bundle hL hconv hcomp hne)
    ((continuous_U bundle μ m).comp (continuous_id.prodMk continuous_id)).continuousOn
  exact ⟨F, hF, fun F' hF' => hmax hF'⟩

/-- The set of all lotteries over `ι`. -/
def allLotteries (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {F | Logit.IsProb F}

/-- Non-vacuity: with all lotteries over a nonempty finite set of bundles
available, a preferred personal equilibrium exists. -/
theorem exists_ppe_allLotteries [Nonempty ι] (μ : ℝ → ℝ) (m : K → ℝ → ℝ) :
    ∃ F, IsPPE bundle μ m (allLotteries ι) F := by
  classical
  have hL : IsLotterySet (allLotteries ι) := fun G hG => hG
  have hconv : Convex ℝ (allLotteries ι) := by
    intro p hp q hq a b ha hb hab
    refine ⟨fun s => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hp.1 s)) (mul_nonneg hb (hq.1 s))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.2,
        hq.2]
      linarith
  have hcl : IsClosed (allLotteries ι) := by
    have e : allLotteries ι = (⋂ s, {p : ι → ℝ | 0 ≤ p s}) ∩ {p | ∑ s, p s = 1} := by
      ext p; simp [allLotteries, Logit.IsProb]
    rw [e]
    exact (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter
      (isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const)
  have hcomp : IsCompact (allLotteries ι) := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      hcl fun p hp s _ => ⟨hp.1 s, ?_⟩
    rw [← hp.2]
    exact single_le_sum (f := p) (fun c _ => hp.1 c) (mem_univ s)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hne : (allLotteries ι).Nonempty :=
    ⟨Pi.single i 1, fun j => by by_cases h : j = i <;> simp [h], by simp⟩
  exact exists_ppe_of_convex bundle hL hconv hcomp hne

/-- For degenerate lotteries, `U` reduces to `u`. -/
theorem U_pure [DecidableEq ι] (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (i j : ι) :
    U bundle μ m (Pi.single i 1) (Pi.single j 1) = u μ m (bundle i) (bundle j) := by
  unfold U
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end Stochastic

/-! ### Riskless choice -/

/-- Personal equilibrium in riskless choice: expecting bundle `c` (and so
using it as reference point), the agent weakly prefers `c` to every other
feasible bundle. (Equivalent to `IsPE` on degenerate lotteries, by `U_pure`.) -/
def IsPEDet (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (D : Set (K → ℝ)) (c : K → ℝ) : Prop :=
  c ∈ D ∧ ∀ c' ∈ D, u μ m c' c ≤ u μ m c c

/-- Preferred personal equilibrium in riskless choice. -/
def IsPPEDet (μ : ℝ → ℝ) (m : K → ℝ → ℝ) (D : Set (K → ℝ)) (c : K → ℝ) : Prop :=
  IsPEDet μ m D c ∧ ∀ c', IsPEDet μ m D c' → u μ m c' c' ≤ u μ m c c

/-- Gain–loss utility relative to oneself is zero when `μ 0 = 0`. -/
theorem u_self {μ : ℝ → ℝ} (hμ : μ 0 = 0) (m : K → ℝ → ℝ) (c : K → ℝ) :
    u μ m c c = consumptionUtility m c := by
  simp [u, gainLoss, hμ]

/-- **Existence of PE in riskless choice (linear μ).** With `η ≥ 0` and
`λ ≥ 1`, any maximizer of consumption utility over `D` is a personal
equilibrium. -/
theorem isPEDet_of_isMax {η lam : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (m : K → ℝ → ℝ)
    {D : Set (K → ℝ)} {c : K → ℝ} (hc : c ∈ D)
    (hmax : ∀ c' ∈ D, consumptionUtility m c' ≤ consumptionUtility m c) :
    IsPEDet (μLin η lam) m D c := by
  refine ⟨hc, fun c' hc' => ?_⟩
  rw [u_self (by simp [μLin]) m c]
  have hgl : gainLoss (μLin η lam) m c' c ≤ η * (consumptionUtility m c' - consumptionUtility m c) := by
    unfold gainLoss consumptionUtility
    rw [← sum_sub_distrib, mul_sum]
    exact sum_le_sum fun k _ => μLin_le η lam hη hlam _
  have := hmax c' hc'
  unfold u
  nlinarith

/-- Hence on a finite nonempty riskless choice set PE and PPE exist. -/
theorem exists_ppeDet {η lam : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (m : K → ℝ → ℝ)
    {D : Set (K → ℝ)} (hD : D.Finite) (hne : D.Nonempty) :
    ∃ c, IsPPEDet (μLin η lam) m D c := by
  obtain ⟨c, hc, hmax⟩ := hD.toFinset.exists_max_image (consumptionUtility m)
    (by simpa using hne)
  rw [Set.Finite.mem_toFinset] at hc
  replace hmax : ∀ c' ∈ D, consumptionUtility m c' ≤ consumptionUtility m c :=
    fun c' hc' => hmax c' (by simpa using hc')
  have hPE : ∃ c, IsPEDet (μLin η lam) m D c := ⟨c, isPEDet_of_isMax hη hlam m hc hmax⟩
  have hS : {c | IsPEDet (μLin η lam) m D c}.Finite := hD.subset fun c hc => hc.1
  obtain ⟨c', hc', hmax'⟩ := hS.toFinset.exists_max_image (fun c => u (μLin η lam) m c c)
    (hS.toFinset_nonempty.2 hPE)
  rw [Set.Finite.mem_toFinset] at hc'
  exact ⟨c', hc', fun c'' h => hmax' c'' (by simpa using h)⟩

/-- **PE need not be unique.** Two goods, `m = id` in each, `η = 1`, `λ = 3`:
both "one unit of good 0" and "one unit of good 1" are personal equilibria.
Whatever the agent expects, she is willing to choose. -/
theorem two_PE_example :
    let D : Set (Fin 2 → ℝ) := {![1, 0], ![0, 1]}
    IsPEDet (μLin 1 3) (fun _ x => x) D ![1, 0] ∧ IsPEDet (μLin 1 3) (fun _ x => x) D ![0, 1] := by
  intro D
  constructor
  · refine ⟨by simp [D], fun c' hc' => ?_⟩
    rcases hc' with rfl | rfl <;>
      simp [u, consumptionUtility, gainLoss, μLin, Fin.sum_univ_two]; norm_num
  · refine ⟨by simp [D], fun c' hc' => ?_⟩
    rcases hc' with rfl | rfl <;>
      simp [u, consumptionUtility, gainLoss, μLin, Fin.sum_univ_two]; norm_num

/-! ### The endowment effect

Two dimensions: dimension `0` is the mug (consumption utility `v` per mug),
dimension `1` is money (consumption utility linear). The reference point is the
status quo the agent expected to keep. -/

/-- Mug–money consumption utilities. -/
def mugMoney (v : ℝ) : Fin 2 → ℝ → ℝ := fun k x => if k = 0 then v * x else x

/-- Willingness to accept for the mug. -/
noncomputable def WTA (η lam v : ℝ) : ℝ := v * (1 + η * lam) / (1 + η)

/-- Willingness to pay for the mug (status-quo reference). The same number is
also the seller's cutoff in `sell_isPE_iff`, where it is *not* a buyer's
willingness to pay but the lowest price at which planning to sell is
self-confirming. -/
noncomputable def WTP (η lam v : ℝ) : ℝ := v * (1 + η) / (1 + η * lam)

/-! The next three results fix the reference point at the endowment (the
agent *expected no trade*): they are one-shot comparisons, the classic
status-quo endowment effect. KR's own point, that the reference point is
the agent's expectation, is the personal-equilibrium version further down
(`keep_isPE_iff`, `sell_isPE_iff`). -/

/-- An owner who expected to keep the mug weakly prefers selling it at price
`p` to keeping it iff `p ≥ WTA`. -/
theorem sell_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hv : 0 ≤ v) (hp : 0 ≤ p) :
    u (μLin η lam) (mugMoney v) ![1, 0] ![1, 0] ≤ u (μLin η lam) (mugMoney v) ![0, p] ![1, 0] ↔
      WTA η lam v ≤ p := by
  rw [WTA, div_le_iff₀ (by linarith)]
  rcases eq_or_lt_of_le hv with rfl | hv'
  · simp [u, consumptionUtility, gainLoss, μLin, mugMoney, Fin.sum_univ_two, hp]
    constructor <;> intro h <;> nlinarith
  · simp [u, consumptionUtility, gainLoss, μLin, mugMoney, Fin.sum_univ_two, hp, not_le.2 hv']
    constructor <;> intro h <;> nlinarith

/-- A non-owner who expected not to buy weakly prefers buying at price `p`
iff `p ≤ WTP`. -/
theorem buy_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (hv : 0 ≤ v) (hp : 0 ≤ p) :
    u (μLin η lam) (mugMoney v) ![0, 0] ![0, 0] ≤ u (μLin η lam) (mugMoney v) ![1, -p] ![0, 0] ↔
      p ≤ WTP η lam v := by
  have hpos : 0 < 1 + η * lam := by nlinarith
  rw [WTP, le_div_iff₀ hpos]
  rcases eq_or_lt_of_le hp with rfl | hp'
  · simp [u, consumptionUtility, gainLoss, μLin, mugMoney, Fin.sum_univ_two, hv]
    constructor <;> intro h <;> nlinarith
  · simp [u, consumptionUtility, gainLoss, μLin, mugMoney, Fin.sum_univ_two, hv, not_le.2 hp']
    constructor <;> intro h <;> nlinarith

/-- **The endowment effect.** For a valued mug (`v > 0`) and some gain–loss
sensitivity (`η > 0`), `WTP < WTA` iff the agent is loss averse (`λ > 1`). -/
theorem endowment_effect {η lam v : ℝ} (hη : 0 < η) (hlam : 1 ≤ lam) (hv : 0 < v) :
    WTP η lam v < WTA η lam v ↔ 1 < lam := by
  unfold WTP WTA
  have h1 : 0 < 1 + η := by linarith
  have h2 : 0 < 1 + η * lam := by nlinarith
  rw [div_lt_div_iff₀ h2 h1]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : lam = 1 := le_antisymm hc hlam
    subst this
    simp at h
  · intro h
    have : 1 + η < 1 + η * lam := by nlinarith
    have := mul_lt_mul this this.le h1 h2.le
    nlinarith

/-! ### Expectations as the reference point (KR 2006 §IV)

An owner chooses between keeping the mug and selling it at price `p`. In a
personal equilibrium the reference point is the plan itself. -/

/-- Keep the mug, no money. -/
def keep : Fin 2 → ℝ := ![1, 0]

/-- Sell the mug for `p`. -/
def sell (p : ℝ) : Fin 2 → ℝ := ![0, p]

/-- **Planning to keep is a PE iff `p ≤ WTA`.** -/
theorem keep_isPE_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hv : 0 < v) (hp : 0 < p) :
    IsPEDet (μLin η lam) (mugMoney v) {keep, sell p} keep ↔ p ≤ WTA η lam v := by
  rw [WTA, le_div_iff₀ (by linarith)]
  simp [IsPEDet, keep, sell, u, consumptionUtility, gainLoss, μLin, mugMoney, Fin.sum_univ_two,
    hp.le, not_le.2 hv]
  constructor <;> intro h <;> nlinarith

/-- **Planning to sell is a PE iff `p ≥ v (1 + η) / (1 + η λ)`**, the same
cutoff as `WTP`. So for `WTP ≤ p ≤ WTA` (a nonempty interval when `λ ≥ 1`)
both plans are personal equilibria: what the owner expected decides. -/
theorem sell_isPE_iff {η lam v p : ℝ} (hη : 0 ≤ η) (hlam : 1 ≤ lam) (hv : 0 < v) (hp : 0 < p) :
    IsPEDet (μLin η lam) (mugMoney v) {keep, sell p} (sell p) ↔ WTP η lam v ≤ p := by
  have hpos : 0 < 1 + η * lam := by nlinarith
  rw [WTP, div_le_iff₀ hpos]
  simp [IsPEDet, keep, sell, u, consumptionUtility, gainLoss, μLin, mugMoney, Fin.sum_univ_two,
    hv.le, not_le.2 hp]
  constructor <;> intro h <;> nlinarith

end ReferenceDependence

end Econ
