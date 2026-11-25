/-
# Level-k thinking and forward guidance (a stylized representative-agent version)

References. E. Farhi and I. Werning (2019), "Monetary Policy, Bounded
Rationality, and Incomplete Markets", *AER* 109(11), §II (representative
agent, level-k); M. García-Schmidt and M. Woodford (2019), "Are Low Interest
Rates Deflationary? A Paradox of Perfect-Foresight Analysis", *AER* 109(1).
Catalog item B6.4.

**The economy** (log-deviations from steady state, endowment economy with
output `y = c`). A household with discount factor `β ∈ (0, 1)`, `β R = 1`,
and elasticity of intertemporal substitution `σ` faces a real-rate path
`r` with a one-period cut announced today for date `T` (`rcut T`). Its plan
`c` satisfies the linearized Euler equation `c (s+1) = c s + σ r s` and the
linearized intertemporal budget `Σ_s β^s (c s − y s) = 0` given its beliefs
about income `y` (`IsPlan`). Beliefs about output after the guidance date
are anchored at steady state (`y s = 0` for `s > T`).
* `plan_eq`: then `c s = c 0` up to `T`, and
  `c 0 = (1 − β) Σ_{s ≤ T} β^s y s + σ β^{T+1}` (permanent income plus the
  direct effect of the rate cut); `exists_plan`: such a plan exists.

**Rational expectations** (`IsRational`: believed and realized output agree up
to `T`): output is `σ` at every date up to `T`, whatever the horizon `T`
(`rational_eq`): the forward-guidance puzzle. Markets then also clear after
`T` (`rational_clears_after`: the plan has `c s = 0 = y s` there).

**Level-k** (`IsLevelK`): level-0 expects steady-state output; level `k+1`
plans against the output path that level-`k` behaviour produces *up to `T`*,
with beliefs about output after `T` anchored at steady state. Two
simplifications relative to Farhi–Werning: (i) that anchoring is an assumption,
not an outcome of level-`k` behaviour (whose own consumption after `T` is
`c₀ − σ ≠ 0`); (ii) each level makes a single plan at date 0, so output is flat
on `[0, T]`, whereas Farhi–Werning and García-Schmidt–Woodford let agents
re-reason at each date with the remaining horizon. The closed form below is
therefore this model's, not a formula quoted from the papers; the qualitative
conclusions (attenuation, monotone convergence in `k`, vanishing with the
horizon for finite `k`) are the papers'.
* `levelK_eq`: output up to `T` is `σ (1 − (1 − β^{T+1})^k)`.
* `levelK_lt_rational`, `levelK_strictMono`, `tendsto_levelK`: level-k output
  is strictly below the rational response, strictly increasing in `k`, and
  converges to it as `k → ∞`.
* `levelK_strictAnti_horizon`, `tendsto_levelK_horizon`: for every finite
  `k ≥ 1` the response strictly falls with the horizon `T` and vanishes as
  `T → ∞`. Under anchored post-`T` beliefs, level-k thinking removes the
  forward-guidance puzzle; the puzzle is a knife-edge property of the `k = ∞`
  limit (PLAN bridge B5).

**Scope.** Representative agent with fixed real rates and the
anchored-beliefs-after-`T` assumption; Farhi–Werning's incomplete-markets
interaction and inflation feedback are not formalized.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Econ

namespace LevelKFG

open Finset Filter Topology

/-- The real-rate path: a one-period cut of one unit at date `T`. -/
def rcut (T s : ℕ) : ℝ := if s = T then -1 else 0

/-- `c` is the household's plan given believed income `y`: linearized Euler
equation and intertemporal budget. -/
def IsPlan (β σ : ℝ) (T : ℕ) (y c : ℕ → ℝ) : Prop :=
  (∀ s, c (s + 1) = c s + σ * rcut T s) ∧ HasSum (fun s => β ^ s * (c s - y s)) 0

theorem plan_path {σ : ℝ} {T : ℕ} {c : ℕ → ℝ} (h : ∀ s, c (s + 1) = c s + σ * rcut T s) (s : ℕ) :
    c s = c 0 - σ * (if T < s then 1 else 0) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [h, ih, rcut]
    rcases lt_trichotomy s T with hs | hs | hs
    · simp [show ¬ T < s by omega, show ¬ T < s + 1 by omega, show s ≠ T by omega]
    · subst hs; simp [sub_eq_add_neg]
    · simp [show T < s by omega, show T < s + 1 by omega, show s ≠ T by omega]

/-- **The household's plan**: flat consumption up to `T`, at the level
`(1 − β) Σ_{s ≤ T} β^s y s + σ β^{T+1}`. -/
theorem plan_eq {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {T : ℕ} {y c : ℕ → ℝ}
    (hy : ∀ s, T < s → y s = 0) (hc : IsPlan β σ T y c) :
    c 0 = (1 - β) * ∑ s ∈ range (T + 1), β ^ s * y s + σ * β ^ (T + 1) ∧
      ∀ s ≤ T, c s = c 0 := by
  have hpath := plan_path hc.1
  refine ⟨?_, fun s hs => by rw [hpath s]; simp [show ¬ T < s by omega]⟩
  have hβ1' : 0 < 1 - β := by linarith
  -- decompose the summand
  have hf : ∀ s, β ^ s * (c s - y s) = (c 0 - σ) * β ^ s +
      (if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0) := by
    intro s
    rw [hpath s]
    by_cases hs : T < s
    · simp [hs, hy s hs, show s ∉ range (T + 1) by simp; omega]; ring
    · simp [hs, show s ∈ range (T + 1) by simp; omega]; ring
  have h1 : HasSum (fun s => (c 0 - σ) * β ^ s) ((c 0 - σ) * (1 - β)⁻¹) :=
    (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left _
  have h2 : HasSum (fun s => if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0)
      (∑ s ∈ range (T + 1), β ^ s * (σ - y s)) := by
    have : HasSum (fun s : ℕ => if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0)
        (∑ s ∈ range (T + 1), if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0) :=
      hasSum_sum_of_ne_finset_zero fun s hs => by simp [hs]
    rwa [sum_congr rfl fun s hs => (by simp [hs] :
      (if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0) = β ^ s * (σ - y s))] at this
  have hsum := (h1.add h2).unique (hc.2.congr_fun fun s => (hf s).symm ▸ rfl)
  · have hgeom : (1 - β) * ∑ s ∈ range (T + 1), β ^ s = 1 - β ^ (T + 1) := by
      rw [mul_comm, geom_sum_mul_neg]
    have e : ∑ s ∈ range (T + 1), β ^ s * (σ - y s) =
        σ * ∑ s ∈ range (T + 1), β ^ s - ∑ s ∈ range (T + 1), β ^ s * y s := by
      rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
    rw [e] at hsum
    field_simp at hsum
    have h3 : (1 - β) * (σ * ∑ s ∈ range (T + 1), β ^ s - ∑ s ∈ range (T + 1), β ^ s * y s) =
        σ * (1 - β ^ (T + 1)) - (1 - β) * ∑ s ∈ range (T + 1), β ^ s * y s := by
      rw [mul_sub, ← hgeom]; ring
    linarith

/-- The plan exists: flat at `c₀` up to `T`, then `c₀ − σ`. -/
theorem exists_plan {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) {y : ℕ → ℝ}
    (hy : ∀ s, T < s → y s = 0) : ∃ c, IsPlan β σ T y c := by
  set c₀ := (1 - β) * ∑ s ∈ range (T + 1), β ^ s * y s + σ * β ^ (T + 1)
  refine ⟨fun s => c₀ - σ * (if T < s then 1 else 0), fun s => ?_, ?_⟩
  · simp only [rcut]
    rcases lt_trichotomy s T with hs | hs | hs
    · simp [show ¬ T < s by omega, show ¬ T < s + 1 by omega, show s ≠ T by omega]
    · subst hs; simp [sub_eq_add_neg]
    · simp [show T < s by omega, show T < s + 1 by omega, show s ≠ T by omega]
  · have hf : ∀ s, β ^ s * (c₀ - σ * (if T < s then 1 else 0) - y s) = (c₀ - σ) * β ^ s +
        (if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0) := by
      intro s
      by_cases hs : T < s
      · simp [hs, hy s hs, show s ∉ range (T + 1) by simp; omega]; ring
      · simp [hs, show s ∈ range (T + 1) by simp; omega]; ring
    have h1 : HasSum (fun s => (c₀ - σ) * β ^ s) ((c₀ - σ) * (1 - β)⁻¹) :=
      (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left _
    have h2 : HasSum (fun s : ℕ => if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0)
        (∑ s ∈ range (T + 1), if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0) :=
      hasSum_sum_of_ne_finset_zero fun s hs => by simp [hs]
    rw [sum_congr rfl fun s hs => (by simp [hs] :
      (if s ∈ range (T + 1) then β ^ s * (σ - y s) else 0) = β ^ s * (σ - y s))] at h2
    have hgeom : (1 - β) * ∑ s ∈ range (T + 1), β ^ s = 1 - β ^ (T + 1) := by
      rw [mul_comm, geom_sum_mul_neg]
    convert (h1.add h2).congr_fun (fun s => hf s) using 1
    · have hβ1' : (1 - β) ≠ 0 := by linarith
      have e : ∑ s ∈ range (T + 1), β ^ s * (σ - y s) =
          σ * ∑ s ∈ range (T + 1), β ^ s - ∑ s ∈ range (T + 1), β ^ s * y s := by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
      rw [e]
      field_simp
      have h3 : (1 - β) * (σ * ∑ s ∈ range (T + 1), β ^ s) = σ * (1 - β ^ (T + 1)) := by
        rw [← hgeom]; ring
      simp only [c₀]
      linear_combination -h3

/-- **Rational expectations**: believed output up to `T` equals the
household's consumption (= output) up to `T`. -/
def IsRational (β σ : ℝ) (T : ℕ) (y : ℕ → ℝ) : Prop :=
  (∀ s, T < s → y s = 0) ∧ ∃ c, IsPlan β σ T y c ∧ ∀ s ≤ T, y s = c s

/-- **The forward-guidance puzzle**: under rational expectations output up to
`T` equals `σ`, independently of the horizon `T`. -/
theorem rational_eq {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {T : ℕ} {y : ℕ → ℝ}
    (h : IsRational β σ T y) : ∀ s ≤ T, y s = σ := by
  obtain ⟨hy, c, hc, hyc⟩ := h
  obtain ⟨h0, hflat⟩ := plan_eq hβ0.le hβ1 hy hc
  have hsum : ∑ s ∈ range (T + 1), β ^ s * y s = c 0 * ∑ s ∈ range (T + 1), β ^ s := by
    rw [mul_sum]
    exact sum_congr rfl fun s hs => by
      rw [hyc s (by simp at hs; omega), hflat s (by simp at hs; omega)]; ring
  have hgeom : (1 - β) * ∑ s ∈ range (T + 1), β ^ s = 1 - β ^ (T + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  have hpow : 0 < β ^ (T + 1) := pow_pos hβ0 _
  have : c 0 * β ^ (T + 1) = σ * β ^ (T + 1) := by
    rw [hsum] at h0; linear_combination h0 + c 0 * hgeom
  have hc0 : c 0 = σ := mul_right_cancel₀ hpow.ne' this
  intro s hs
  rw [hyc s hs, hflat s hs, hc0]

/-- Under rational expectations markets also clear after `T`: the plan's
consumption there is `0`, the believed (and realized) output. -/
theorem rational_clears_after {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {T : ℕ} {y c : ℕ → ℝ}
    (hy : ∀ s, T < s → y s = 0) (hc : IsPlan β σ T y c) (hyc : ∀ s ≤ T, y s = c s) :
    ∀ s, T < s → c s = 0 := by
  have h0 := rational_eq hβ0 hβ1 ⟨hy, c, hc, hyc⟩ 0 (Nat.zero_le _)
  have hpath := plan_path hc.1
  intro s hs
  rw [hpath s, ← hyc 0 (Nat.zero_le _), h0]
  simp [hs]

/-- A rational-expectations path exists (output `σ` up to `T`). -/
theorem exists_rational {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    IsRational β σ T fun s => if s ≤ T then σ else 0 := by
  have hy : ∀ s, T < s → (fun s => if s ≤ T then σ else 0) s = 0 := fun s hs => by
    simp [show ¬ s ≤ T by omega]
  obtain ⟨c, hc⟩ := exists_plan hβ0.le hβ1 T hy
  refine ⟨hy, c, hc, fun s hs => ?_⟩
  obtain ⟨h0, hflat⟩ := plan_eq hβ0.le hβ1 hy hc
  have hsum : ∑ s ∈ range (T + 1), β ^ s * (if s ≤ T then σ else 0) =
      σ * ∑ s ∈ range (T + 1), β ^ s := by
    rw [mul_sum]
    exact sum_congr rfl fun s hs => by simp [show s ≤ T by simp at hs; omega]; ring
  have hgeom : (1 - β) * ∑ s ∈ range (T + 1), β ^ s = 1 - β ^ (T + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  rw [hflat s hs, h0, hsum]
  simp only [show s ≤ T from hs, ite_true]
  linear_combination (-σ) * hgeom

/-- **Level-k paths**: `Y k` is the output path level-`k` behaviour produces up
to the guidance date `T`; beliefs about output after `T` are anchored at steady
state by assumption (not produced by level-`k` behaviour), and each level makes
one plan at date 0. Level 0 expects steady state. -/
def IsLevelK (β σ : ℝ) (T : ℕ) (Y : ℕ → ℕ → ℝ) : Prop :=
  (∀ s, Y 0 s = 0) ∧ (∀ k s, T < s → Y k s = 0) ∧
    ∀ k, ∃ c, IsPlan β σ T (Y k) c ∧ ∀ s ≤ T, Y (k + 1) s = c s

/-- The level-k response `σ (1 − (1 − β^{T+1})^k)`. -/
noncomputable def levelK (β σ : ℝ) (T k : ℕ) : ℝ := σ * (1 - (1 - β ^ (T + 1)) ^ k)

/-- **Level-k output** up to the guidance date. -/
theorem levelK_eq {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {T : ℕ} {Y : ℕ → ℕ → ℝ}
    (h : IsLevelK β σ T Y) : ∀ k, ∀ s ≤ T, Y k s = levelK β σ T k := by
  intro k
  induction k with
  | zero => intro s _; simp [h.1 s, levelK]
  | succ k ih =>
    intro s hs
    obtain ⟨c, hc, hY⟩ := h.2.2 k
    obtain ⟨h0, hflat⟩ := plan_eq hβ0 hβ1 (h.2.1 k) hc
    have hsum : ∑ s ∈ range (T + 1), β ^ s * Y k s =
        levelK β σ T k * ∑ s ∈ range (T + 1), β ^ s := by
      rw [mul_sum]
      exact sum_congr rfl fun s hs => by rw [ih s (by simp at hs; omega)]; ring
    have hgeom : (1 - β) * ∑ s ∈ range (T + 1), β ^ s = 1 - β ^ (T + 1) := by
      rw [mul_comm, geom_sum_mul_neg]
    rw [hY s hs, hflat s hs, h0, hsum]
    simp only [levelK, pow_succ]
    linear_combination σ * (1 - (1 - β ^ (T + 1)) ^ k) * hgeom

/-- Level-k paths exist. -/
theorem exists_levelK {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) :
    ∃ Y, IsLevelK β σ T Y := by
  set Y : ℕ → ℕ → ℝ := fun k s => if s ≤ T then levelK β σ T k else 0
  have hY : ∀ k s, T < s → Y k s = 0 := fun k s hs => by simp [Y, show ¬ s ≤ T by omega]
  refine ⟨Y, fun s => by simp [Y, levelK], hY, fun k => ?_⟩
  obtain ⟨c, hc⟩ := exists_plan hβ0 hβ1 T (hY k)
  refine ⟨c, hc, fun s hs => ?_⟩
  obtain ⟨h0, hflat⟩ := plan_eq hβ0 hβ1 (hY k) hc
  have hsum : ∑ s ∈ range (T + 1), β ^ s * Y k s =
      levelK β σ T k * ∑ s ∈ range (T + 1), β ^ s := by
    rw [mul_sum]
    exact sum_congr rfl fun s hs => by simp [Y, show s ≤ T by simp at hs; omega]; ring
  have hgeom : (1 - β) * ∑ s ∈ range (T + 1), β ^ s = 1 - β ^ (T + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  rw [hflat s hs, h0, hsum]
  simp only [Y, show s ≤ T from hs, ite_true, levelK, pow_succ]
  linear_combination (-(σ * (1 - (1 - β ^ (T + 1)) ^ k))) * hgeom

theorem gap_mem {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    0 ≤ 1 - β ^ (T + 1) ∧ 1 - β ^ (T + 1) < 1 := by
  have h1 : β ^ (T + 1) < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have h2 : 0 < β ^ (T + 1) := pow_pos hβ0 _
  constructor <;> linarith

/-- Level-k output is strictly below the rational response `σ > 0`. -/
theorem levelK_lt_rational {β σ : ℝ} (hσ : 0 < σ) (T k : ℕ)
    (hT : 0 < 1 - β ^ (T + 1)) : levelK β σ T k < σ := by
  have := pow_pos hT k
  unfold levelK; nlinarith

/-- Level-k output is strictly increasing in the depth of reasoning `k`. -/
theorem levelK_strictMono {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (T : ℕ)
    (hT : 0 < 1 - β ^ (T + 1)) : StrictMono (levelK β σ T) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hlt := (gap_mem hβ0 hβ1 T).2
  have hp := pow_pos hT k
  have h2 : (1 - β ^ (T + 1)) ^ k * (1 - β ^ (T + 1)) < (1 - β ^ (T + 1)) ^ k := by
    simpa using mul_lt_mul_of_pos_left hlt hp
  unfold levelK
  rw [pow_succ (1 - β ^ (T + 1)) k]
  exact mul_lt_mul_of_pos_left (by linarith) hσ

/-- Level-k output converges to the rational response `σ` as `k → ∞`. -/
theorem tendsto_levelK {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    Tendsto (levelK β σ T) atTop (𝓝 σ) := by
  obtain ⟨h0, h1⟩ := gap_mem hβ0 hβ1 T
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_sub 1 |>.const_mul σ
  convert this using 2 <;> simp [levelK]

/-- **Level-k removes the forward-guidance puzzle**: for every finite `k ≥ 1`
the response strictly falls with the horizon `T` (under anchored post-`T` beliefs). -/
theorem levelK_strictAnti_horizon {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) {k : ℕ}
    (hk : 1 ≤ k) : StrictAnti fun T => levelK β σ T k := by
  apply strictAnti_nat_of_succ_lt
  intro T
  have hb : β ^ (T + 1 + 1) < β ^ (T + 1) := pow_lt_pow_right_of_lt_one₀ hβ0 hβ1 (by omega)
  have hlo : 0 ≤ 1 - β ^ (T + 1) := (gap_mem hβ0 hβ1 T).1
  have hlt : 1 - β ^ (T + 1) < 1 - β ^ (T + 1 + 1) := by linarith
  have := pow_lt_pow_left₀ hlt hlo (by omega : k ≠ 0)
  unfold levelK
  nlinarith

/-- For fixed `k`, level-k output vanishes as the horizon `T → ∞`. -/
theorem tendsto_levelK_horizon {β σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (k : ℕ) :
    Tendsto (fun T => levelK β σ T k) atTop (𝓝 0) := by
  have hb : Tendsto (fun T : ℕ => β ^ (T + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).comp (tendsto_add_atTop_nat 1)
  have := ((((hb.const_sub 1).pow k).const_sub 1).const_mul σ)
  simpa [levelK] using this

end LevelKFG

end Econ
