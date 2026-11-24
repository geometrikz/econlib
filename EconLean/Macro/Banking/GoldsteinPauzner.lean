/-
# Bank runs as a global game (Goldstein–Pauzner)

Diamond and Dybvig (1983), JPE; Goldstein and Pauzner (2005),
"Demand–Deposit Contracts and the Probability of Bank Runs", JF;
Morris and Shin (2003), "Global Games: Theory and Applications".

**Setting.** A unit mass of depositors deposit one unit each. A fraction
`λ ∈ (0, 1)` are impatient and withdraw at date 1; the bank promises
`r ∈ (1, 1/λ)` to anyone withdrawing at date 1 (`r > 1` is the liquidity
insurance). Long-run investment pays `R > 0` at date 2 with probability
`p(θ)`, strictly increasing and continuous in the fundamental `θ`, with
`0 ≤ p ≤ 1`. If a fraction `n ∈ [λ, 1]` withdraws early, a patient
depositor's gain from waiting over withdrawing is
* `v(θ, n) = p(θ) R (1 − n r)/(1 − n) − r` while the bank survives
  (`n < 1/r`), and
* `v(θ, n) = −1/n` once it fails (`n ≥ 1/r`: early withdrawers are served
  in random order and waiters get nothing).
`v` is continuous at `n = 1/r` (both expressions equal `−r`) but **not
monotone in `n`**, the one-sided strategic complementarity of GP.

**Results.** With vanishing private noise, a patient depositor at the
threshold signal holds Laplacian beliefs: the fraction withdrawing is uniform
on `[λ, 1]`. The run threshold `θ*` is defined by `A(θ*) = 0`, where
`A(θ) = ∫_λ^1 v(θ, n) dn` (`A`).
* `A_eq`: `A(θ) = p(θ) R I − (1 − rλ) − log r` with
  `I = ∫_λ^{1/r} (1 − n r)/(1 − n) dn > 0` (`I_pos`).
* `A_strictMono`, `continuous_A`: `A` is continuous and strictly increasing
  in `θ`.
* `existsUnique_threshold`, `lt_threshold_iff`: if `A` changes sign there
  is a unique threshold `θ*`, and `A(θ) < 0` (patient depositors run)
  exactly when `θ < θ*`.
* `v_anti_r`, `A_anti_r`, `A_strictAnti_r`, `threshold_mono_r`: offering
  more liquidity insurance (a larger `r`) lowers `v` pointwise, strictly
  lowers `A` and strictly raises the run threshold: **more risk sharing
  makes runs more likely** (GP Theorem 2).

**Deviations.** No global game is modelled here: there are no private
signals, noise or dominance regions. `θ*` is the threshold of GP's
vanishing-noise limit, defined by the Laplacian indifference condition
`A(θ*) = 0`; the facts that this limit holds and that the threshold
equilibrium is the unique equilibrium are taken from GP Theorem 1, not
proved, so `existsUnique_threshold` is uniqueness of the root of `A`.
Utility is linear, so the risk-sharing benefit of `r > 1` (the other side of
GP's trade-off) and the bank's choice of the optimal `r` are not
formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

noncomputable section

namespace Econ
namespace GoldsteinPauzner

open Set intervalIntegral

/-- Primitives. -/
structure Params where
  lam : ℝ
  r : ℝ
  R : ℝ
  p : ℝ → ℝ
  hlam : 0 < lam
  hr : 1 < r
  hlr : lam * r < 1
  hR : 0 < R
  hp_mono : StrictMono p
  hp_cont : Continuous p
  hp_nn : ∀ θ, 0 ≤ p θ
  hp_le : ∀ θ, p θ ≤ 1

namespace Params

variable (P : Params)

/-- A patient depositor's gain from waiting when a fraction `n` withdraws. -/
def v (θ n : ℝ) : ℝ := if n < 1 / P.r then P.p θ * P.R * ((1 - n * P.r) / (1 - n)) - P.r else -1 / n

/-- The Laplacian expected gain from waiting. -/
def A (θ : ℝ) : ℝ := ∫ n in P.lam..1, P.v θ n

/-- `∫_λ^{1/r} (1 − n r)/(1 − n) dn`. -/
def I : ℝ := ∫ n in P.lam..1 / P.r, (1 - n * P.r) / (1 - n)

theorem r_pos : 0 < P.r := by linarith [P.hr]
theorem lam_lt : P.lam < 1 / P.r := by rw [lt_div_iff₀ P.r_pos]; exact P.hlr
theorem inv_r_lt_one : 1 / P.r < 1 := by rw [div_lt_one P.r_pos]; exact P.hr

theorem v_eqOn₁ (θ : ℝ) : EqOn (P.v θ) (fun n => P.p θ * P.R * ((1 - n * P.r) / (1 - n)) - P.r)
    (Icc P.lam (1 / P.r)) := by
  intro n hn
  simp only [v]
  split_ifs with h
  · rfl
  · have : n = 1 / P.r := le_antisymm hn.2 (not_lt.1 h)
    subst this
    have := P.r_pos
    field_simp
    simp

theorem v_eqOn₂ (θ : ℝ) : EqOn (P.v θ) (fun n => -1 / n) (Icc (1 / P.r) 1) := by
  intro n hn
  simp only [v, not_lt.2 hn.1, ↓reduceIte]

theorem contOn₀ :
    ContinuousOn (fun n : ℝ => (1 - n * P.r) / (1 - n)) (Icc P.lam (1 / P.r)) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro n hn
  have := P.inv_r_lt_one
  linarith [hn.2]

theorem contOn₁ (c : ℝ) :
    ContinuousOn (fun n : ℝ => c * ((1 - n * P.r) / (1 - n)) - P.r) (Icc P.lam (1 / P.r)) :=
  (continuousOn_const.mul P.contOn₀).sub continuousOn_const

theorem contOn₂ : ContinuousOn (fun n : ℝ => -1 / n) (Icc (1 / P.r) 1) := by
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro n hn
  have : 0 < 1 / P.r := div_pos one_pos P.r_pos
  exact (this.trans_le hn.1).ne'

theorem int₁ (θ : ℝ) : IntervalIntegrable (P.v θ) MeasureTheory.volume P.lam (1 / P.r) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le P.lam_lt.le]
  exact (P.contOn₁ (P.p θ * P.R)).congr (P.v_eqOn₁ θ)

theorem int₂ (θ : ℝ) : IntervalIntegrable (P.v θ) MeasureTheory.volume (1 / P.r) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le P.inv_r_lt_one.le]
  exact P.contOn₂.congr (P.v_eqOn₂ θ)

theorem I_pos : 0 < P.I := by
  have hlt := P.lam_lt
  apply intervalIntegral_pos_of_pos_on _ _ hlt
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlt.le]
    exact P.contOn₀
  · intro n hn
    have h1 := P.inv_r_lt_one
    have hnr : n * P.r < 1 := by
      have := hn.2; rw [lt_div_iff₀ P.r_pos] at this; exact this
    exact div_pos (by linarith) (by linarith [hn.2])

/-- **Closed form.** -/
theorem A_eq (θ : ℝ) : P.A θ = P.p θ * P.R * P.I - (1 - P.r * P.lam) - Real.log P.r := by
  have hlt := P.lam_lt; have h1 := P.inv_r_lt_one; have hr := P.r_pos
  have e1 : ∫ n in P.lam..1 / P.r, P.v θ n =
      ∫ n in P.lam..1 / P.r, (P.p θ * P.R * ((1 - n * P.r) / (1 - n)) - P.r) :=
    integral_congr (by rw [uIcc_of_le hlt.le]; exact P.v_eqOn₁ θ)
  have e2 : ∫ n in 1 / P.r..1, P.v θ n = ∫ n in 1 / P.r..1, -1 / n :=
    integral_congr (by rw [uIcc_of_le h1.le]; exact P.v_eqOn₂ θ)
  rw [A, ← integral_add_adjacent_intervals (P.int₁ θ) (P.int₂ θ), e1, e2]
  have hint : IntervalIntegrable (fun n : ℝ => (1 - n * P.r) / (1 - n)) MeasureTheory.volume
      P.lam (1 / P.r) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlt.le]
    exact P.contOn₀
  rw [integral_sub (hint.const_mul _) intervalIntegrable_const, integral_const_mul,
    integral_const]
  have hlog : ∫ n in 1 / P.r..1, -1 / n = -Real.log P.r := by
    simp only [neg_div, integral_neg, one_div]
    rw [integral_inv_of_pos (inv_pos.2 hr) one_pos]
    simp
  rw [hlog, I, smul_eq_mul, show (1 / P.r - P.lam) * P.r = 1 - P.r * P.lam by field_simp]
  ring

theorem continuous_A : Continuous P.A := by
  have : P.A = fun θ => P.p θ * P.R * P.I - (1 - P.r * P.lam) - Real.log P.r :=
    funext P.A_eq
  rw [this]
  exact ((P.hp_cont.mul continuous_const).mul continuous_const).sub continuous_const |>.sub
    continuous_const

/-- **Stronger fundamentals make waiting more attractive.** -/
theorem A_strictMono : StrictMono P.A := by
  intro θ₁ θ₂ h
  rw [P.A_eq, P.A_eq]
  have := P.hp_mono h
  have := mul_pos P.hR P.I_pos
  nlinarith

/-- **A unique run threshold.** -/
theorem existsUnique_threshold {θL θH : ℝ} (hL : P.A θL < 0) (hH : 0 < P.A θH) :
    ∃! θs, P.A θs = 0 := by
  have hle : θL ≤ θH := le_of_lt (P.A_strictMono.lt_iff_lt.1 (hL.trans hH))
  obtain ⟨θs, -, hθs⟩ := intermediate_value_Icc hle P.continuous_A.continuousOn ⟨hL.le, hH.le⟩
  exact ⟨θs, hθs, fun θ hθ => P.A_strictMono.injective (hθ.trans hθs.symm)⟩

/-- Patient depositors run (`A < 0`) exactly below the threshold. -/
theorem lt_threshold_iff {θs : ℝ} (hθs : P.A θs = 0) (θ : ℝ) : P.A θ < 0 ↔ θ < θs := by
  rw [← hθs]; exact P.A_strictMono.lt_iff_lt

/-! ### More liquidity insurance, more runs -/

/-- Raising `r` lowers the gain from waiting at every `n ∈ [λ, 1]`. -/
theorem v_anti_r (P' : Params) (hR : P'.R = P.R) (hp : P'.p = P.p)
    (hrr : P.r < P'.r) (θ : ℝ) {n : ℝ} (hn : P.lam ≤ n) : P'.v θ n ≤ P.v θ n := by
  have hr := P.r_pos
  have hnpos : 0 < n := P.hlam.trans_le hn
  have hinv : 1 / P'.r < 1 / P.r := one_div_lt_one_div_of_lt hr hrr
  have hpR : 0 ≤ P.p θ * P.R := mul_nonneg (P.hp_nn θ) P.hR.le
  simp only [v, hR, hp]
  by_cases h' : n < 1 / P'.r
  · have h : n < 1 / P.r := h'.trans hinv
    simp only [h', h, ↓reduceIte]
    have hn1' : 0 < 1 - n := by linarith [P.inv_r_lt_one]
    have : (1 - n * P'.r) / (1 - n) ≤ (1 - n * P.r) / (1 - n) :=
      div_le_div_of_nonneg_right (by nlinarith) hn1'.le
    nlinarith [mul_le_mul_of_nonneg_left this hpR]
  · simp only [h', ↓reduceIte]
    by_cases h : n < 1 / P.r
    · simp only [h, ↓reduceIte]
      have hn1' : 0 < 1 - n := by linarith [P.inv_r_lt_one]
      have hnr : 0 < 1 - n * P.r := by rw [lt_div_iff₀ hr] at h; linarith
      have h0 : 0 ≤ P.p θ * P.R * ((1 - n * P.r) / (1 - n)) := mul_nonneg hpR (div_pos hnr hn1').le
      have : -1 / n < -P.r := by
        rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hnpos]
        rw [lt_div_iff₀ hr] at h; linarith
      linarith
    · simp only [h, ↓reduceIte]; rfl

theorem A_anti_r (P' : Params) (hlam : P'.lam = P.lam) (hR : P'.R = P.R) (hp : P'.p = P.p)
    (hrr : P.r < P'.r) (θ : ℝ) : P'.A θ ≤ P.A θ := by
  have hle : P.lam ≤ 1 := (P.lam_lt.trans P.inv_r_lt_one).le
  have hi : ∀ Q : Params, IntervalIntegrable (Q.v θ) MeasureTheory.volume Q.lam 1 :=
    fun Q => (Q.int₁ θ).trans (Q.int₂ θ)
  simp only [A]
  have := hi P'
  rw [hlam] at this ⊢
  exact integral_mono_on hle this (hi P) fun n hn => P.v_anti_r P' hR hp hrr θ hn.1

/-- Raising `r` strictly lowers the Laplacian gain from waiting. -/
theorem A_strictAnti_r (P' : Params) (hlam : P'.lam = P.lam) (hR : P'.R = P.R)
    (hp : P'.p = P.p) (hrr : P.r < P'.r) (θ : ℝ) : P'.A θ < P.A θ := by
  have hb' : P.lam < 1 / P'.r := hlam ▸ P'.lam_lt
  have hb'1 : 1 / P'.r ≤ 1 := P'.inv_r_lt_one.le
  have hinv : 1 / P'.r < 1 / P.r := one_div_lt_one_div_of_lt P.r_pos hrr
  have hle1 : P.lam ≤ 1 := hb'.le.trans hb'1
  have hiP : IntervalIntegrable (P.v θ) MeasureTheory.volume P.lam 1 := (P.int₁ θ).trans (P.int₂ θ)
  have hiP' : IntervalIntegrable (P'.v θ) MeasureTheory.volume P.lam 1 := by
    have := (P'.int₁ θ).trans (P'.int₂ θ); rwa [hlam] at this
  have hs1 : uIcc P.lam (1 / P'.r) ⊆ uIcc P.lam 1 := by
    rw [uIcc_of_le hb'.le, uIcc_of_le hle1]; exact Icc_subset_Icc le_rfl hb'1
  have hs2 : uIcc (1 / P'.r) 1 ⊆ uIcc P.lam 1 := by
    rw [uIcc_of_le hb'1, uIcc_of_le hle1]; exact Icc_subset_Icc hb'.le le_rfl
  simp only [A]
  rw [hlam, ← integral_add_adjacent_intervals (hiP'.mono_set hs1) (hiP'.mono_set hs2),
    ← integral_add_adjacent_intervals (hiP.mono_set hs1) (hiP.mono_set hs2)]
  have hweak : ∫ n in 1 / P'.r..1, P'.v θ n ≤ ∫ n in 1 / P'.r..1, P.v θ n :=
    integral_mono_on hb'1 (hiP'.mono_set hs2) (hiP.mono_set hs2)
      fun n hn => P.v_anti_r P' hR hp hrr θ (hb'.le.trans hn.1)
  have hsub : Icc P.lam (1 / P'.r) ⊆ Icc P.lam (1 / P.r) := Icc_subset_Icc le_rfl hinv.le
  have e1 : ∫ n in P.lam..1 / P'.r, P'.v θ n =
      ∫ n in P.lam..1 / P'.r, (P'.p θ * P'.R * ((1 - n * P'.r) / (1 - n)) - P'.r) :=
    integral_congr (by rw [uIcc_of_le hb'.le, ← hlam]; exact P'.v_eqOn₁ θ)
  have e2 : ∫ n in P.lam..1 / P'.r, P.v θ n =
      ∫ n in P.lam..1 / P'.r, (P.p θ * P.R * ((1 - n * P.r) / (1 - n)) - P.r) :=
    integral_congr (by rw [uIcc_of_le hb'.le]; exact (P.v_eqOn₁ θ).mono hsub)
  have hpR : 0 ≤ P.p θ * P.R := mul_nonneg (P.hp_nn θ) P.hR.le
  have hcmp : ∀ n, P.lam ≤ n → n < 1 →
      P.p θ * P.R * ((1 - n * P'.r) / (1 - n)) ≤ P.p θ * P.R * ((1 - n * P.r) / (1 - n)) := by
    intro n hn hn1
    have hn0 : 0 < n := P.hlam.trans_le hn
    apply mul_le_mul_of_nonneg_left _ hpR
    exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  have hstrict : ∫ n in P.lam..1 / P'.r, P'.v θ n < ∫ n in P.lam..1 / P'.r, P.v θ n := by
    rw [e1, e2, hp, hR]
    have hc' := P'.contOn₁ (P.p θ * P.R)
    rw [hlam] at hc'
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hb' hc'
      ((P.contOn₁ (P.p θ * P.R)).mono hsub)
    · intro n hn
      have := hcmp n (hn.1.le) (lt_of_le_of_lt hn.2 P'.inv_r_lt_one)
      linarith
    · refine ⟨P.lam, left_mem_Icc.2 hb'.le, ?_⟩
      have := hcmp P.lam le_rfl (P.lam_lt.trans P.inv_r_lt_one)
      linarith
  linarith

/-- **The run threshold rises strictly with `r`.** -/
theorem threshold_mono_r (P' : Params) (hlam : P'.lam = P.lam) (hR : P'.R = P.R)
    (hp : P'.p = P.p) (hrr : P.r < P'.r) {θs θs' : ℝ} (h : P.A θs = 0) (h' : P'.A θs' = 0) :
    θs < θs' := by
  have := P.A_strictAnti_r P' hlam hR hp hrr θs'
  rw [h'] at this
  exact P.A_strictMono.lt_iff_lt.1 (h ▸ this)

end Params
end GoldsteinPauzner
end Econ

end
