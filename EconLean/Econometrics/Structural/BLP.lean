/-
# Demand inversion: Berry (1994) logit and BLP mixed logit

Berry, "Estimating discrete-choice models of product differentiation",
*RAND Journal of Economics* (1994); Berry, Levinsohn and Pakes, "Automobile
prices in market equilibrium", *Econometrica* (1995); Berry, Gandhi and Haile,
"Connected substitutes and invertibility of demand", *Econometrica* (2013).

**The economics.** In a market with products `j ∈ J` and an outside good `0`,
consumer `i` gets utility `δⱼ + μᵢⱼ + εᵢⱼ` from product `j` and `εᵢ₀` from the
outside good, with i.i.d. type-I extreme value `ε`. Market shares are
`σⱼ(δ) = Σᵢ wᵢ exp(δⱼ + μᵢⱼ) / (1 + Σₖ exp(δₖ + μᵢₖ))` for consumer types `i`
with weights `wᵢ` (plain logit: one type with `μ = 0`). Estimation à la BLP
inverts observed shares to mean utilities `δ = σ⁻¹(s)`, then uses
`δⱼ = xⱼβ − αpⱼ + ξⱼ` as a linear IV model (`IV`, `GMM`).

**The results.**

* **Berry's logit inversion**: `δⱼ = log sⱼ − log s₀` (`berry_inversion`), and
  every interior share vector is attained (`share_surjective`), so the logit
  share map is a bijection from `ℝ^J` onto the interior of the simplex.
* **Invertibility of mixed-logit (BLP) demand** (`mixedShare_injective`): for
  any finite set of consumer types with positive weights and any taste shifts
  `μ`, the share map is injective. The proof is the connected-substitutes
  argument of Berry–Gandhi–Haile: if `δ ≠ δ'`, say `max (δ − δ') = M > 0`, the
  set `K` of products attaining the maximum gains share for every consumer
  type, since raising all utilities by at most `M` and those in `K` by exactly
  `M` raises the share of `K` (`share_set_lt`).

**Not covered.** Existence of the inverse for the mixed logit (surjectivity
onto the simplex) and BLP's contraction mapping `δ ↦ δ + log s − log σ(δ)`.
Consumer heterogeneity is a finite mixture; a continuous mixture would replace
the finite sum by an integral.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Econ.Structural.BLP

open Real Finset

variable {J : Type*} [Fintype J]

/-- Logit share of product `j` at mean utilities `δ` (outside good normalised
to utility 0). -/
noncomputable def share (δ : J → ℝ) (j : J) : ℝ :=
  exp (δ j) / (1 + ∑ k, exp (δ k))

/-- Logit share of the outside good. -/
noncomputable def outsideShare (δ : J → ℝ) : ℝ :=
  1 / (1 + ∑ k, exp (δ k))

lemma denom_pos (δ : J → ℝ) : 0 < 1 + ∑ k, exp (δ k) := by
  have : 0 ≤ ∑ k, exp (δ k) := sum_nonneg fun k _ => (exp_pos _).le
  linarith

lemma share_pos (δ : J → ℝ) (j : J) : 0 < share δ j :=
  div_pos (exp_pos _) (denom_pos δ)

lemma outsideShare_pos (δ : J → ℝ) : 0 < outsideShare δ :=
  div_pos one_pos (denom_pos δ)

/-- Shares sum to one: inside shares plus the outside share. -/
lemma sum_share_add_outside (δ : J → ℝ) : ∑ j, share δ j + outsideShare δ = 1 := by
  have h := (denom_pos δ).ne'
  simp only [share, outsideShare, ← sum_div]
  field_simp
  ring

/-- **Berry's (1994) inversion** for the logit: `δⱼ = log sⱼ − log s₀`. -/
theorem berry_inversion (δ : J → ℝ) (j : J) :
    δ j = log (share δ j) - log (outsideShare δ) := by
  have hD := denom_pos δ
  rw [share, outsideShare, log_div (exp_pos _).ne' hD.ne', log_div one_ne_zero hD.ne', log_exp,
    log_one]
  ring

/-- **Logit shares are onto the interior of the simplex**: for any shares
`sⱼ > 0` with `Σ sⱼ < 1`, the mean utilities `δⱼ = log sⱼ − log(1 − Σ s)`
reproduce them. -/
theorem share_surjective {s : J → ℝ} (hs : ∀ j, 0 < s j) (hsum : ∑ j, s j < 1) :
    share (fun j => log (s j) - log (1 - ∑ k, s k)) = s := by
  have h0 : 0 < 1 - ∑ k, s k := by linarith
  have hexp : ∀ j, exp (log (s j) - log (1 - ∑ k, s k)) = s j / (1 - ∑ k, s k) := by
    intro j; rw [exp_sub, exp_log (hs j), exp_log h0]
  funext j
  simp only [share, hexp, ← sum_div]
  have h1 : 1 + (∑ k, s k) / (1 - ∑ k, s k) = 1 / (1 - ∑ k, s k) := by
    field_simp; ring
  rw [h1]
  field_simp

/-- The logit share map is injective (a consequence of the inversion formula). -/
theorem share_injective : Function.Injective (share (J := J)) := by
  intro δ δ' h
  funext j
  rw [berry_inversion δ j, berry_inversion δ' j, h]
  congr 2
  have h1 := sum_share_add_outside δ
  have h2 := sum_share_add_outside δ'
  rw [h] at h1
  linarith

/-! ### Mixed logit (BLP) -/

/-- **Key inequality** (connected substitutes): if every utility rises by at most
`M > 0` (factor `exp dⱼ ≤ exp M` on `aⱼ = exp(utility)`) and those in a nonempty
set `K` rise by exactly `M`, the logit share of `K` strictly increases. -/
theorem share_set_lt {a d : J → ℝ} (ha : ∀ j, 0 < a j) {M : ℝ} (hM : 0 < M)
    (hd : ∀ j, d j ≤ M) {K : Finset J} (hK : K.Nonempty) (hdK : ∀ j ∈ K, d j = M) :
    (∑ j ∈ K, a j) / (1 + ∑ j, a j)
      < (∑ j ∈ K, exp (d j) * a j) / (1 + ∑ j, exp (d j) * a j) := by
  have hA : 0 < ∑ j ∈ K, a j := sum_pos (fun j _ => ha j) hK
  have hT : 0 ≤ ∑ j, a j := sum_nonneg fun j _ => (ha j).le
  have hT' : 0 ≤ ∑ j, exp (d j) * a j :=
    sum_nonneg fun j _ => mul_nonneg (exp_pos _).le (ha j).le
  have hKsum : ∑ j ∈ K, exp (d j) * a j = exp M * ∑ j ∈ K, a j := by
    rw [mul_sum]; exact sum_congr rfl fun j hj => by rw [hdK j hj]
  have hle : ∑ j, exp (d j) * a j ≤ exp M * ∑ j, a j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (exp_le_exp.mpr (hd j)) (ha j).le
  have heM : 1 < exp M := one_lt_exp_iff.mpr hM
  rw [hKsum, div_lt_div_iff₀ (by linarith) (by linarith)]
  have : 1 + ∑ j, exp (d j) * a j < exp M * (1 + ∑ j, a j) := by nlinarith
  nlinarith

variable {I : Type*} [Fintype I]

/-- Mixed-logit (BLP) market shares with consumer types `i`, weights `w i` and
taste shifts `μ i j`. -/
noncomputable def mixedShare (w : I → ℝ) (μ : I → J → ℝ) (δ : J → ℝ) (j : J) : ℝ :=
  ∑ i, w i * share (δ + μ i) j

/-- If some product has `δⱼ > δ'ⱼ`, the set of products maximising `δ − δ'` has
a strictly larger mixed-logit share under `δ` than under `δ'`. -/
theorem exists_set_share_lt [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i) (μ : I → J → ℝ)
    {δ δ' : J → ℝ} (h : ∃ j, δ' j < δ j) :
    ∃ K : Finset J, ∑ j ∈ K, mixedShare w μ δ' j < ∑ j ∈ K, mixedShare w μ δ j := by
  classical
  obtain ⟨j₀, hj₀⟩ := h
  have hne : (univ : Finset J).Nonempty := ⟨j₀, mem_univ _⟩
  set d : J → ℝ := fun j => δ j - δ' j with hd
  set M := univ.sup' hne d with hMdef
  have hdM : ∀ j, d j ≤ M := fun j => le_sup' d (mem_univ j)
  obtain ⟨j₁, -, hj₁⟩ := exists_mem_eq_sup' hne d
  have hM : 0 < M := lt_of_lt_of_le (by simp only [hd]; linarith) (hdM j₀)
  set K := univ.filter fun j => d j = M with hK
  have hKne : K.Nonempty := ⟨j₁, by simp [hK, ← hj₁, hMdef]⟩
  refine ⟨K, ?_⟩
  simp only [mixedShare]
  rw [sum_comm, sum_comm (s := K)]
  refine sum_lt_sum_of_nonempty univ_nonempty fun i _ => ?_
  rw [← mul_sum, ← mul_sum]
  refine mul_lt_mul_of_pos_left ?_ (hw i)
  -- the single-type inequality
  have key := share_set_lt (a := fun j => exp (δ' j + μ i j)) (d := d)
    (fun j => exp_pos _) hM hdM hKne (fun j hj => (mem_filter.mp hj).2)
  have hexp : ∀ j, exp (d j) * exp (δ' j + μ i j) = exp (δ j + μ i j) := by
    intro j; rw [← exp_add]; congr 1; simp only [hd]; ring
  simp only [hexp] at key
  simpa [share, ← sum_div, Pi.add_apply] using key

/-- **Invertibility of BLP demand** (Berry 1994; BLP 1995; Berry–Gandhi–Haile
2013): with finitely many consumer types of positive weight, the mixed-logit
share map is injective for any taste shifts `μ`. -/
theorem mixedShare_injective [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i)
    (μ : I → J → ℝ) : Function.Injective (mixedShare w μ) := by
  intro δ δ' h
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  rcases lt_or_gt_of_ne hj with hlt | hlt
  · obtain ⟨K, hK⟩ := exists_set_share_lt hw μ (δ := δ') (δ' := δ) ⟨j, hlt⟩
    rw [h] at hK; exact lt_irrefl _ hK
  · obtain ⟨K, hK⟩ := exists_set_share_lt hw μ (δ := δ) (δ' := δ') ⟨j, hlt⟩
    rw [h] at hK; exact lt_irrefl _ hK

/-- The plain logit is the one-type mixed logit with no taste shifts. -/
lemma mixedShare_unit (δ : J → ℝ) :
    mixedShare (fun _ : Unit => (1 : ℝ)) (fun _ => 0) δ = share δ := by
  funext j; simp [mixedShare]

/-- **Non-vacuity**: a two-type, two-product market with opposite tastes. The
share map is injective, and the two types have different logit shares (so the
mixture is genuinely not a logit in `δ`). -/
theorem mixed_witness :
    let w : Fin 2 → ℝ := fun _ => 1 / 2
    let μ : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else -1
    Function.Injective (mixedShare w μ) ∧ share (0 + μ 0) 0 ≠ share (0 + μ 1) 0 := by
  intro w μ
  refine ⟨mixedShare_injective (fun _ => by norm_num) μ, ?_⟩
  intro h
  have := berry_inversion (0 + μ 0) 0
  have h2 := berry_inversion (0 + μ 1) 0
  -- outside shares coincide by symmetry, so equal inside shares force equal utilities
  have hout : outsideShare (0 + μ 0) = outsideShare (0 + μ 1) := by
    simp [outsideShare, μ, Fin.sum_univ_two, add_comm]
  rw [h, hout] at this
  rw [← h2] at this
  simp [μ] at this
  norm_num at this

end Econ.Structural.BLP
