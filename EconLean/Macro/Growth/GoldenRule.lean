/-
# The golden rule of capital accumulation

Phelps (1961); Acemoglu ch. 2 (golden rule, §2.2.4 in the discrete model);
Romer §1.4; Barro and Sala-i-Martin §1.2.4.

**The economics.** In a Solow steady state, consumption per worker is
output minus the investment needed to keep `k` constant:

    c* = (1 − s) f(k*) = f(k*) − (n + δ) k*.

Saving more raises `k*` but also raises the "maintenance" investment
`(n + δ) k*`. The **golden rule** capital stock `k_gold` maximizes steady-state
consumption; it is characterized by `f'(k_gold) = n + δ` (the marginal product
of capital equals the effective depreciation rate). The saving rate that
delivers it is `s_gold = (n + δ) k_gold / f(k_gold)`; for Cobb–Douglas
`f k = k^α` this is just `s_gold = α`, the capital share.

Main results:
* `goldenRule_lt`: for a strictly concave `f`, if `f'(k_gold) = c` then
  `f k − c k < f k_gold − c k_gold` for every other `k ≥ 0`.
* `Economy.consumption_le_goldenRule`: steady-state consumption per worker in
  *any* Solow economy is at most the golden-rule level, with equality iff its
  steady state is `k_gold`.
* `Economy.isSteadyState_goldenRule`: the saving rate `s_gold` attains it.
* `Economy.consumption_lt_withGoldenSaving`: any economy not at `k_gold` would
  have higher steady-state consumption with `s_gold`; with `k* > k_gold`
  (overaccumulation) that means saving less.
* `cobbDouglas_goldenRule`: closed forms
  `k_gold = (α / (n + δ))^{1/(1−α)}` and `s_gold = α`.

**Deviation from the textbook.** We assume `f` is differentiable only at
`k_gold` (the point where we use the first-order condition), not everywhere.
-/
module

public import EconLean.Macro.Growth.Solow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

noncomputable section

namespace Econ
namespace Solow

open Set Filter Topology

/-- **Strict tangent-line inequality.** A strictly concave function lies
strictly below its tangent line, except at the point of tangency. -/
theorem lt_tangent {f : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Ici 0) f) {c kg k : ℝ}
    (hkg : 0 ≤ kg) (hd : HasDerivAt f c kg) (hk : 0 ≤ k) (hne : k ≠ kg) :
    f k < f kg + c * (k - kg) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hconc.lt_slope_of_hasDerivAt (mem_Ici.2 hk) (mem_Ici.2 hkg) hlt hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.2 hlt)] at this
    linarith
  · have := hconc.slope_lt_of_hasDerivAt (mem_Ici.2 hkg) (mem_Ici.2 hk) hgt hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.2 hgt)] at this
    linarith

/-- **The golden rule.** If `f` is strictly concave and `f'(k_gold) = c`, then
`k_gold` is the unique maximizer of `f k − c k` on `k ≥ 0`. With
`c = n + δ`, `f k − (n + δ) k` is steady-state consumption per worker. -/
theorem goldenRule_lt {f : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Ici 0) f) {c kg k : ℝ}
    (hkg : 0 ≤ kg) (hd : HasDerivAt f c kg) (hk : 0 ≤ k) (hne : k ≠ kg) :
    f k - c * k < f kg - c * kg := by
  have := lt_tangent hconc hkg hd hk hne
  linarith

theorem goldenRule_le {f : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Ici 0) f) {c kg k : ℝ}
    (hkg : 0 ≤ kg) (hd : HasDerivAt f c kg) (hk : 0 ≤ k) :
    f k - c * k ≤ f kg - c * kg := by
  rcases eq_or_ne k kg with rfl | hne
  · exact le_rfl
  · exact (goldenRule_lt hconc hkg hd hk hne).le

namespace Economy

variable (E : Economy)

/-- In a steady state, consumption per worker `(1 − s) f(k*)` equals
`f(k*) − (n + δ) k*`. -/
theorem consumption_eq {k : ℝ} (hs : E.IsSteadyState k) :
    (1 - E.s) * E.f k = E.f k - (E.n + E.δ) * k := by
  have := ((E.isSteadyState_iff).1 hs).2
  linarith

/-- **No saving rate beats the golden rule.** Let `k_gold > 0` satisfy
`f'(k_gold) = n + δ`. Then steady-state consumption per worker is at most
`f(k_gold) − (n + δ) k_gold`, with equality only if `k* = k_gold`. -/
theorem consumption_le_goldenRule {kg : ℝ} (hkg : 0 < kg)
    (hd : HasDerivAt E.f (E.n + E.δ) kg) {k : ℝ} (hs : E.IsSteadyState k) :
    (1 - E.s) * E.f k ≤ E.f kg - (E.n + E.δ) * kg := by
  rw [E.consumption_eq hs]
  exact goldenRule_le E.hf.strictConcaveOn hkg.le hd hs.1.le

theorem consumption_lt_goldenRule {kg : ℝ} (hkg : 0 < kg)
    (hd : HasDerivAt E.f (E.n + E.δ) kg) {k : ℝ} (hs : E.IsSteadyState k) (hne : k ≠ kg) :
    (1 - E.s) * E.f k < E.f kg - (E.n + E.δ) * kg := by
  rw [E.consumption_eq hs]
  exact goldenRule_lt E.hf.strictConcaveOn hkg.le hd hs.1.le hne

/-- The golden-rule saving rate `s_gold = (n + δ) k_gold / f(k_gold)`. -/
def goldenSavingRate (kg : ℝ) : ℝ := (E.n + E.δ) * kg / E.f kg

/-- `s_gold ∈ (0, 1]`, so it is an admissible saving rate. (`s_gold ≤ 1`
because golden-rule consumption is at least the consumption `0` at `k = 0`.) -/
theorem goldenSavingRate_mem {kg : ℝ} (hkg : 0 < kg) (hd : HasDerivAt E.f (E.n + E.δ) kg) :
    0 < E.goldenSavingRate kg ∧ E.goldenSavingRate kg ≤ 1 := by
  have hf := E.hf.pos hkg
  refine ⟨div_pos (mul_pos E.hnδ hkg) hf, ?_⟩
  rw [goldenSavingRate, div_le_one hf]
  have := goldenRule_le E.hf.strictConcaveOn hkg.le hd (le_refl 0)
  rw [E.hf.map_zero] at this
  linarith

/-- The same economy with saving rate `s_gold`. -/
def withGoldenSaving {kg : ℝ} (hkg : 0 < kg) (hd : HasDerivAt E.f (E.n + E.δ) kg) :
    Economy :=
  { E with
    s := E.goldenSavingRate kg
    hs_pos := (E.goldenSavingRate_mem hkg hd).1
    hs_le_one := (E.goldenSavingRate_mem hkg hd).2 }

/-- **The golden rule is attainable:** with saving rate `s_gold` the steady
state is exactly `k_gold`, so steady-state consumption reaches its maximum. -/
theorem isSteadyState_goldenRule {kg : ℝ} (hkg : 0 < kg)
    (hd : HasDerivAt E.f (E.n + E.δ) kg) :
    (E.withGoldenSaving hkg hd).IsSteadyState kg := by
  rw [isSteadyState_iff]
  refine ⟨hkg, ?_⟩
  show (E.n + E.δ) * kg / E.f kg * E.f kg = (E.n + E.δ) * kg
  exact div_mul_cancel₀ _ (E.hf.pos hkg).ne'

/-- **Switching to the golden-rule saving rate raises steady-state
consumption** whenever the current steady state is not `k_gold`. In particular
an economy that saves so much that `k* > k_gold` (overaccumulation) would have
higher steady-state consumption with a *lower* saving rate. This compares
steady states only; the transition path is analysed for the Diamond model in
`Diamond.exists_dominating_path`. -/
theorem consumption_lt_withGoldenSaving {kg : ℝ} (hkg : 0 < kg)
    (hd : HasDerivAt E.f (E.n + E.δ) kg) {k : ℝ} (hs : E.IsSteadyState k) (hne : k ≠ kg) :
    (1 - E.s) * E.f k <
      (1 - (E.withGoldenSaving hkg hd).s) * (E.withGoldenSaving hkg hd).f kg := by
  rw [(E.withGoldenSaving hkg hd).consumption_eq (E.isSteadyState_goldenRule hkg hd)]
  exact E.consumption_lt_goldenRule hkg hd hs hne

end Economy

/-! ## Cobb–Douglas closed forms -/

/-- **Unit test.** For `f k = k^α`, the golden-rule capital stock is
`k_gold = (α / (n + δ))^{1/(1−α)}`: it satisfies `f'(k_gold) = n + δ`. -/
theorem cobbDouglas_hasDerivAt_goldenRule (E : Economy) {α : ℝ} (hα₁ : α < 1)
    (hf : E.f = fun k => k ^ α) (hα₀ : 0 < α) :
    HasDerivAt E.f (E.n + E.δ) ((α / (E.n + E.δ)) ^ (1 / (1 - α))) := by
  have hx : 0 < α / (E.n + E.δ) := div_pos hα₀ E.hnδ
  have hk : 0 < (α / (E.n + E.δ)) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hx _
  rw [hf]
  convert Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne') using 1
  rw [← Real.rpow_mul hx.le, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
    Real.rpow_neg_one, inv_div]
  have := E.hnδ.ne'
  field_simp

/-- **Unit test.** For Cobb–Douglas the golden-rule saving rate is the
capital share: `s_gold = α`. -/
theorem cobbDouglas_goldenSavingRate (E : Economy) {α : ℝ} (hα₁ : α < 1)
    (hf : E.f = fun k => k ^ α) (hα₀ : 0 < α) :
    E.goldenSavingRate ((α / (E.n + E.δ)) ^ (1 / (1 - α))) = α := by
  have hx : 0 < α / (E.n + E.δ) := div_pos hα₀ E.hnδ
  have hk : 0 < (α / (E.n + E.δ)) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hx _
  unfold Economy.goldenSavingRate
  rw [hf]
  dsimp only
  -- `(n+δ) k / k^α = (n+δ) k^(1-α) = (n+δ) (α/(n+δ)) = α`
  rw [mul_div_assoc, ← Real.rpow_one_sub' hk.le, ← Real.rpow_mul hx.le]
  · rw [show 1 / (1 - α) * (1 - α) = 1 by field_simp, Real.rpow_one]
    have := E.hnδ.ne'
    field_simp
  · linarith

end Solow
end Econ

end
