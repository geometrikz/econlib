/-
# Hulten's theorem

Hulten (1978), "Growth Accounting with Intermediate Inputs", REStud;
Baqaee–Farhi (2019) §2; Acemoglu–Carvalho–Ozdaglar–Tahbaz-Salehi (2012).

**The economics.** In an efficient economy, the first-order effect on
aggregate output of a productivity shock to sector `i` equals sector `i`'s
**Domar weight**, its sales divided by GDP:

    ∂ log Y / ∂ log Aᵢ = pᵢ xᵢ / GDP.

With intermediate inputs, Domar weights sum to *more* than one (gross output
exceeds value added), which is how micro shocks can have large aggregate
effects.

We prove the theorem in two Cobb–Douglas economies with labour (supply `1`)
as the only factor, where everything has closed forms:

* `Horizontal`: sectors `x_i = A_i l_i` feed a Cobb–Douglas final good
  `Y = Π xᵢ^{aᵢ}` (`Σ aᵢ = 1`). `Horizontal.output_le`: the planner's maximum is
  `Y* = Π (Aᵢ aᵢ)^{aᵢ}`; `Horizontal.ce_eq`: every competitive equilibrium
  attains it; `Horizontal.hulten`: along competitive equilibria of the shocked
  economies, `∂ log Y / ∂ log Aᵢ = aᵢ = pᵢ xᵢ / Y`, the equilibrium Domar weight
  (`hulten_planner` is the same statement for the planner's `Y*`).
* `Vertical`: an upstream sector `x₁ = A₁ l₁` sells an intermediate input to a
  downstream sector producing the final good `Y = A₂ l₂^{1−ω} x₁^ω`.
  `Vertical.hulten`: `∂ log Y*/∂ log A₁ = ω` and `∂ log Y*/∂ log A₂ = 1`, which
  are the equilibrium Domar weights, and they sum to `1 + ω > 1`.

**The Lean.** "∂ log Y*/∂ log Aᵢ" is the derivative at `t = 0` of
`t ↦ log Y*(A with Aᵢ replaced by Aᵢ eᵗ)`.

**Deviation.** Hulten's theorem holds for any efficient economy with
constant returns; we prove it only for these Cobb–Douglas economies (general
production networks with Domar weights `b'(I − Ω)⁻¹` are a follow-up).
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

noncomputable section

namespace Econ
namespace Hulten

open Finset Real

/-! ## Horizontal economy -/

/-- A horizontal Cobb–Douglas economy. -/
structure Horizontal (ι : Type*) [Fintype ι] where
  /-- Sector productivities. -/
  A : ι → ℝ
  /-- Cobb–Douglas expenditure shares of the final good. -/
  a : ι → ℝ
  hA : ∀ i, 0 < A i
  ha : ∀ i, 0 < a i
  sum_a : ∑ i, a i = 1

namespace Horizontal

variable {ι : Type*} [Fintype ι] (H : Horizontal ι)

/-- Final output when sector `i` employs `l i`. -/
def output (l : ι → ℝ) : ℝ := ∏ i, (H.A i * l i) ^ H.a i

/-- The planner's maximum `Y* = Π (Aᵢ aᵢ)^{aᵢ}`. -/
def maxOutput : ℝ := ∏ i, (H.A i * H.a i) ^ H.a i

/-- **Planner's problem.** No feasible labour allocation produces more than
`Y*`, and `lᵢ = aᵢ` attains it. -/
theorem output_le {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hsum : ∑ i, l i = 1) :
    H.output l ≤ H.maxOutput := by
  have hfac : ∀ i, (H.A i * l i) ^ H.a i =
      (H.A i * H.a i) ^ H.a i * (l i / H.a i) ^ H.a i := by
    intro i
    rw [← mul_rpow (mul_pos (H.hA i) (H.ha i)).le (div_nonneg (hl i) (H.ha i).le)]
    congr 1
    have := H.ha i
    field_simp
  have hAM := geom_mean_le_arith_mean_weighted (s := univ) H.a (fun i => l i / H.a i)
    (fun i _ => (H.ha i).le) H.sum_a (fun i _ => div_nonneg (hl i) (H.ha i).le)
  have : ∑ i, H.a i * (l i / H.a i) = 1 := by
    rw [← hsum]; exact Finset.sum_congr rfl fun i _ => by have := H.ha i; field_simp
  rw [this] at hAM
  rw [output, Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib]
  have hpos : 0 ≤ ∏ i, (H.A i * H.a i) ^ H.a i :=
    Finset.prod_nonneg fun i _ => rpow_nonneg (mul_pos (H.hA i) (H.ha i)).le _
  calc (∏ i, (H.A i * H.a i) ^ H.a i) * ∏ i, (l i / H.a i) ^ H.a i
      ≤ (∏ i, (H.A i * H.a i) ^ H.a i) * 1 := mul_le_mul_of_nonneg_left hAM hpos
    _ = H.maxOutput := mul_one _

theorem output_a : H.output H.a = H.maxOutput := rfl

/-- A **competitive equilibrium** with the final good as numeraire: wage `w`,
sector prices `p i`, labour `l i`, final output `Y`, such that sector firms
make zero profit (`pᵢ Aᵢ = w`, constant returns), the final-good firm spends
the Cobb–Douglas share `aᵢ` of revenue on input `i`, the labour market clears
and `Y` is what the technology produces. -/
structure IsCE (p : ι → ℝ) (w Y : ℝ) (l : ι → ℝ) : Prop where
  w_pos : 0 < w
  l_nonneg : ∀ i, 0 ≤ l i
  labor : ∑ i, l i = 1
  zeroProfit : ∀ i, p i * H.A i = w
  demand : ∀ i, p i * (H.A i * l i) = H.a i * Y
  tech : Y = H.output l

/-- **Every competitive equilibrium is efficient:** `lᵢ = aᵢ`, `Y = Y*`, and
GDP (the wage bill `w · 1`) equals `Y`. -/
theorem ce_eq {p : ι → ℝ} {w Y : ℝ} {l : ι → ℝ} (h : H.IsCE p w Y l) :
    (∀ i, l i = H.a i) ∧ Y = H.maxOutput ∧ w = Y := by
  have hwl : ∀ i, w * l i = H.a i * Y := fun i => by
    rw [← h.demand i, ← h.zeroProfit i]; ring
  have hwY : w = Y := by
    have := Finset.sum_congr rfl fun i (_ : i ∈ univ) => hwl i
    rw [← Finset.mul_sum, ← Finset.sum_mul, h.labor, H.sum_a] at this
    linarith
  have hl : ∀ i, l i = H.a i := fun i => by
    have := hwl i
    rw [← hwY] at this
    exact mul_left_cancel₀ h.w_pos.ne' (this.trans (mul_comm _ _))
  refine ⟨hl, ?_, hwY⟩
  rw [h.tech, show l = H.a from funext hl, output_a]

/-- Domar weight of sector `i` in a competitive equilibrium: its sales over
GDP, which is `aᵢ`. -/
theorem domar {p : ι → ℝ} {w Y : ℝ} {l : ι → ℝ} (h : H.IsCE p w Y l) (i : ι) :
    p i * (H.A i * l i) / Y = H.a i := by
  obtain ⟨-, hY, -⟩ := H.ce_eq h
  have hYpos : 0 < Y := by
    rw [hY]
    exact Finset.prod_pos fun i _ => rpow_pos_of_pos (mul_pos (H.hA i) (H.ha i)) _
  rw [h.demand i]; field_simp

/-- The economy after scaling sector `i`'s productivity by `eᵗ`. -/
def shock [DecidableEq ι] (i : ι) (t : ℝ) : Horizontal ι :=
  { H with
    A := fun j => if j = i then H.A j * exp t else H.A j
    hA := fun j => by
      split_ifs
      · exact mul_pos (H.hA j) (exp_pos t)
      · exact H.hA j }

theorem log_maxOutput : log H.maxOutput = ∑ i, H.a i * log (H.A i * H.a i) := by
  rw [maxOutput, log_prod]
  · exact Finset.sum_congr rfl fun i _ => log_rpow (mul_pos (H.hA i) (H.ha i)) _
  · exact fun i _ => (rpow_pos_of_pos (mul_pos (H.hA i) (H.ha i)) _).ne'

/-- **Hulten's theorem (horizontal economy):** `∂ log Y*/∂ log Aᵢ = aᵢ`, which
is sector `i`'s equilibrium Domar weight `pᵢ xᵢ / Y`. -/
theorem hulten_planner [DecidableEq ι] {p : ι → ℝ} {w Y : ℝ} {l : ι → ℝ} (h : H.IsCE p w Y l) (i : ι) :
    HasDerivAt (fun t => log (H.shock i t).maxOutput) (p i * (H.A i * l i) / Y) 0 := by
  rw [H.domar h i]
  have heq : (fun t => log (H.shock i t).maxOutput) =
      fun t => log H.maxOutput + H.a i * t := by
    funext t
    rw [log_maxOutput, log_maxOutput, ← Finset.add_sum_erase _ _ (mem_univ i),
      ← Finset.add_sum_erase _ _ (mem_univ i)]
    have hrest : ∑ j ∈ univ.erase i, (H.shock i t).a j * log ((H.shock i t).A j * (H.shock i t).a j)
        = ∑ j ∈ univ.erase i, H.a j * log (H.A j * H.a j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [shock, Finset.ne_of_mem_erase hj]
    rw [hrest]
    simp only [shock, ite_true]
    rw [show H.A i * exp t * H.a i = (H.A i * H.a i) * exp t by ring,
      log_mul (mul_pos (H.hA i) (H.ha i)).ne' (exp_pos t).ne', log_exp]
    ring
  rw [heq]
  simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (H.a i)).const_add (log H.maxOutput)

/-- **Hulten's theorem, stated for competitive equilibria.** Take any family of
competitive equilibria `(pₜ, wₜ, Yₜ, lₜ)` of the shocked economies
`shock i t`. Then `d log Yₜ / dt` at `t = 0` equals the sector's Domar weight
in the original equilibrium. -/
theorem hulten [DecidableEq ι] {p : ι → ℝ} {w Y : ℝ} {l : ι → ℝ} (h : H.IsCE p w Y l)
    (i : ι) {pt : ℝ → ι → ℝ} {wt Yt : ℝ → ℝ} {lt : ℝ → ι → ℝ}
    (ht : ∀ t, (H.shock i t).IsCE (pt t) (wt t) (Yt t) (lt t)) :
    HasDerivAt (fun t => log (Yt t)) (p i * (H.A i * l i) / Y) 0 := by
  have heq : (fun t => log (Yt t)) = fun t => log (H.shock i t).maxOutput := by
    funext t; rw [((H.shock i t).ce_eq (ht t)).2.1]
  rw [heq]; exact H.hulten_planner h i

end Horizontal

/-! ## Vertical economy: an input-output link -/

/-- Upstream sector `x₁ = A₁ l₁` supplies the downstream sector, which makes
the final good `Y = A₂ l₂^{1−ω} x₁^ω` (`l₁ + l₂ = 1`). -/
structure Vertical where
  A₁ : ℝ
  A₂ : ℝ
  ω : ℝ
  hA₁ : 0 < A₁
  hA₂ : 0 < A₂
  hω₀ : 0 < ω
  hω₁ : ω < 1

namespace Vertical

variable (V : Vertical)

/-- Final output when upstream employs `l₁` and downstream `1 − l₁`. -/
def output (l₁ : ℝ) : ℝ := V.A₂ * (1 - l₁) ^ (1 - V.ω) * (V.A₁ * l₁) ^ V.ω

/-- The planner's maximum `Y* = A₂ (1 − ω)^{1−ω} (A₁ ω)^ω`, at `l₁ = ω`. -/
def maxOutput : ℝ := V.output V.ω

/-- **Planner's problem.** -/
theorem output_le {l₁ : ℝ} (h0 : 0 ≤ l₁) (h1 : l₁ ≤ 1) : V.output l₁ ≤ V.maxOutput := by
  have hω1 : 0 < 1 - V.ω := by linarith [V.hω₁]
  have hAM := geom_mean_le_arith_mean2_weighted hω1.le V.hω₀.le
    (div_nonneg (by linarith : 0 ≤ 1 - l₁) hω1.le) (div_nonneg h0 V.hω₀.le)
    (by ring : 1 - V.ω + V.ω = 1)
  have hsum : (1 - V.ω) * ((1 - l₁) / (1 - V.ω)) + V.ω * (l₁ / V.ω) = 1 := by
    have := V.hω₀; field_simp; ring
  rw [hsum] at hAM
  have e : V.output l₁ = V.maxOutput * (((1 - l₁) / (1 - V.ω)) ^ (1 - V.ω) * (l₁ / V.ω) ^ V.ω) := by
    simp only [maxOutput, output]
    rw [div_rpow (by linarith) hω1.le, div_rpow h0 V.hω₀.le, mul_rpow V.hA₁.le h0,
      mul_rpow V.hA₁.le V.hω₀.le]
    have := rpow_pos_of_pos hω1 (1 - V.ω)
    have := rpow_pos_of_pos V.hω₀ V.ω
    field_simp
  have hM : 0 ≤ V.maxOutput := by
    simp only [maxOutput, output]
    have := V.hA₂; have := V.hA₁
    exact mul_nonneg (mul_nonneg V.hA₂.le (rpow_nonneg hω1.le _))
      (rpow_nonneg (mul_pos V.hA₁ V.hω₀).le _)
  rw [e]
  calc V.maxOutput * (((1 - l₁) / (1 - V.ω)) ^ (1 - V.ω) * (l₁ / V.ω) ^ V.ω)
      ≤ V.maxOutput * 1 := mul_le_mul_of_nonneg_left hAM hM
    _ = V.maxOutput := mul_one _

/-- A **competitive equilibrium** (final good numeraire): upstream zero profit
`p₁ A₁ = w`; the downstream firm spends shares `ω` on the input and `1 − ω`
on labour; markets clear. -/
structure IsCE (p₁ w Y l₁ : ℝ) : Prop where
  w_pos : 0 < w
  l_mem : 0 ≤ l₁ ∧ l₁ ≤ 1
  zeroProfit : p₁ * V.A₁ = w
  inputDemand : p₁ * (V.A₁ * l₁) = V.ω * Y
  laborDemand : w * (1 - l₁) = (1 - V.ω) * Y
  tech : Y = V.output l₁

/-- **Equilibrium is efficient**, and GDP (= wage bill `w`) equals `Y`. -/
theorem ce_eq {p₁ w Y l₁ : ℝ} (h : V.IsCE p₁ w Y l₁) : l₁ = V.ω ∧ Y = V.maxOutput ∧ w = Y := by
  have h1 : w * l₁ = V.ω * Y := by rw [← h.inputDemand, ← h.zeroProfit]; ring
  have hwY : w = Y := by have := h.laborDemand; linarith
  have hl : l₁ = V.ω := by
    rw [← hwY] at h1
    exact mul_left_cancel₀ h.w_pos.ne' (h1.trans (mul_comm _ _))
  exact ⟨hl, by rw [h.tech, hl]; rfl, hwY⟩

theorem maxOutput_pos : 0 < V.maxOutput := by
  have hω1 : 0 < 1 - V.ω := by linarith [V.hω₁]
  exact mul_pos (mul_pos V.hA₂ (rpow_pos_of_pos hω1 _)) (rpow_pos_of_pos (mul_pos V.hA₁ V.hω₀) _)

/-- **Domar weights:** the upstream sector's sales are the share `ω` of GDP,
the downstream sector's sales are all of GDP; together `1 + ω > 1`. -/
theorem domar {p₁ w Y l₁ : ℝ} (h : V.IsCE p₁ w Y l₁) :
    p₁ * (V.A₁ * l₁) / w = V.ω ∧ Y / w = 1 ∧ 1 < p₁ * (V.A₁ * l₁) / w + Y / w := by
  obtain ⟨-, hY, hwY⟩ := V.ce_eq h
  have hYpos : 0 < Y := hY ▸ V.maxOutput_pos
  rw [hwY, h.inputDemand]
  refine ⟨by field_simp, div_self hYpos.ne', ?_⟩
  rw [mul_div_assoc, div_self hYpos.ne']
  linarith [V.hω₀]

theorem log_maxOutput :
    log V.maxOutput = log V.A₂ + (1 - V.ω) * log (1 - V.ω) + V.ω * log (V.A₁ * V.ω) := by
  have hω1 : 0 < 1 - V.ω := by linarith [V.hω₁]
  simp only [maxOutput, output]
  rw [log_mul (mul_pos V.hA₂ (rpow_pos_of_pos hω1 _)).ne'
      (rpow_pos_of_pos (mul_pos V.hA₁ V.hω₀) _).ne',
    log_mul V.hA₂.ne' (rpow_pos_of_pos hω1 _).ne', log_rpow hω1, log_rpow (mul_pos V.hA₁ V.hω₀)]

/-- **Hulten's theorem (vertical economy).** Scaling `A₁` by `eᵗ` changes
`log Y*` at rate `ω`, scaling `A₂` at rate `1`: in both cases the
equilibrium Domar weight. -/
theorem hulten {p₁ w Y l₁ : ℝ} (h : V.IsCE p₁ w Y l₁) :
    HasDerivAt (fun t => log ({ V with A₁ := V.A₁ * exp t, hA₁ := mul_pos V.hA₁ (exp_pos t) } :
        Vertical).maxOutput) (p₁ * (V.A₁ * l₁) / w) 0 ∧
    HasDerivAt (fun t => log ({ V with A₂ := V.A₂ * exp t, hA₂ := mul_pos V.hA₂ (exp_pos t) } :
        Vertical).maxOutput) (Y / w) 0 := by
  obtain ⟨d1, d2, -⟩ := V.domar h
  rw [d1, d2]
  constructor
  · have heq : (fun t => log ({ V with A₁ := V.A₁ * exp t, hA₁ := mul_pos V.hA₁ (exp_pos t) } :
        Vertical).maxOutput) = fun t => log V.maxOutput + V.ω * t := by
      funext t
      rw [log_maxOutput, log_maxOutput]
      simp only
      rw [show V.A₁ * exp t * V.ω = (V.A₁ * V.ω) * exp t by ring,
        log_mul (mul_pos V.hA₁ V.hω₀).ne' (exp_pos t).ne', log_exp]
      ring
    rw [heq]
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul V.ω).const_add (log V.maxOutput)
  · have heq : (fun t => log ({ V with A₂ := V.A₂ * exp t, hA₂ := mul_pos V.hA₂ (exp_pos t) } :
        Vertical).maxOutput) = fun t => log V.maxOutput + t := by
      funext t
      rw [log_maxOutput, log_maxOutput]
      simp only
      rw [log_mul V.hA₂.ne' (exp_pos t).ne', log_exp]
      ring
    rw [heq]
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (log V.maxOutput)

end Vertical

/-- **Non-vacuity:** a competitive equilibrium of the vertical economy exists
(`A₁ = A₂ = 1`, `ω = 1/2`). -/
example : ∃ p₁ w Y l₁, (⟨1, 1, 1 / 2, one_pos, one_pos, by norm_num, by norm_num⟩ : Vertical).IsCE
    p₁ w Y l₁ := by
  set V : Vertical := ⟨1, 1, 1 / 2, one_pos, one_pos, by norm_num, by norm_num⟩
  have hY := V.maxOutput_pos
  refine ⟨V.maxOutput, V.maxOutput, V.maxOutput, 1 / 2, ⟨hY, by norm_num, ?_, ?_, ?_, rfl⟩⟩
  · simp [V]
  · simp [V]; ring
  · norm_num; ring

end Hulten
end Econ

end
