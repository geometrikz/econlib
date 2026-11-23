/-
# Convergence in probability, consistency from root-n rates, and the delta method

van der Vaart, *Asymptotic Statistics* (1998), Thm 2.7 and Thm 3.1;
Hayashi, *Econometrics* (2000), Lemma 2.4–2.5; Coretto (2026).

**The results.**

* **Convergence in distribution to a constant implies convergence in
  probability** (van der Vaart Thm 2.7(iii)).
* **Continuous mapping at a point**: if `X_n →p c` and `q` is continuous at
  `c`, then `q(X_n) →p q(c)` (Hayashi Lemma 2.3(a), pointwise version).
* **Root-n consistency**: if `√n (T_n − θ) →d Z` then `T_n →p θ`.
* **Delta method** (van der Vaart Thm 3.1; Hayashi Lemma 2.5): if
  `√n (T_n − θ) →d Z` and `g` is differentiable at `θ`, then
  `√n (g(T_n) − g(θ)) →d g'(θ) Z`. With the CLT this gives
  `√n (g(X̄_n) − g(μ)) →d N(0, g'(μ)² σ²)` (`delta_method_clt`).

**Encoding.** Mathlib's `TendstoInDistribution` (weak convergence of laws) and
`TendstoInMeasure` (convergence in probability). The proof of the delta method
follows the textbook one: write `√n (g(T_n) − g(θ)) = q(T_n) · √n (T_n − θ)`
with the difference quotient `q`, continuous at `θ` with `q(θ) = g'(θ)`; then
`q(T_n) →p g'(θ)` and Slutsky's theorem (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`)
finishes. `g` is assumed (Borel) measurable so that `g(T_n)` is a random
variable, which textbooks leave implicit.
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The bounded continuous function `x ↦ min 1 (|x − c| / |ε|)`. -/
noncomputable def bump (c ε : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min 1 (|x - c| / |ε|), by fun_prop⟩ 1 fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hx0 : 0 ≤ min 1 (|x - c| / |ε|) := le_min zero_le_one (by positivity)
      have hy0 : 0 ≤ min 1 (|y - c| / |ε|) := le_min zero_le_one (by positivity)
      have hx1 := min_le_left 1 (|x - c| / |ε|)
      have hy1 := min_le_left 1 (|y - c| / |ε|)
      rw [abs_le]; constructor <;> linarith

lemma bump_apply (c ε x : ℝ) : bump c ε x = min 1 (|x - c| / |ε|) := rfl

/-- **Convergence in distribution to a constant implies convergence in
probability** (van der Vaart Thm 2.7(iii)). -/
theorem tendstoInMeasure_of_tendstoInDistribution_const {ι : Type*} {l : Filter ι}
    {X : ι → Ω → ℝ} {c : ℝ}
    (h : TendstoInDistribution X l (fun _ => c) (fun _ => P) P') :
    TendstoInMeasure P X l (fun _ => c) := by
  have hX := h.forall_aemeasurable
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hint := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX
    h.aemeasurable_limit).mp h (bump c ε)
  simp only [bump_apply, sub_self, abs_zero, zero_div, min_eq_right zero_le_one,
    integral_const, smul_zero] at hint
  -- `P {ε ≤ |X_i − c|} ≤ ∫ bump (X_i)`.
  have hle : ∀ i, P {ω | ε ≤ ‖X i ω - c‖} ≤ ENNReal.ofReal (∫ ω, bump c ε (X i ω) ∂P) := by
    intro i
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (bump c ε (X i ω))) P :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((bump c ε).continuous.measurable.comp_aemeasurable (hX i))
    have hm := mul_meas_ge_le_lintegral₀ hmeas 1
    rw [one_mul] at hm
    have hb01 : ∀ x, 0 ≤ bump c ε x ∧ bump c ε x ≤ 1 := fun x =>
      ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
    have hbi : Integrable (fun ω => bump c ε (X i ω)) P :=
      Integrable.of_bound ((bump c ε).continuous.comp_aestronglyMeasurable
        (hX i).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hb01 (X i ω)])
    rw [ofReal_integral_eq_lintegral_ofReal hbi]
    · refine le_trans (measure_mono fun ω hω => ?_) hm
      simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
      rw [bump_apply, abs_of_pos hε, min_eq_left ((one_le_div hε).mpr hω), ENNReal.ofReal_one]
    · exact Filter.Eventually.of_forall fun ω => le_min zero_le_one (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
  have := (ENNReal.continuous_ofReal.tendsto 0).comp hint
  simp only [ENNReal.ofReal_zero] at this
  exact this

/-- **Convergence in distribution to a constant is convergence in probability**
(van der Vaart Thm 2.7(iii), both directions). -/
theorem tendstoInDistribution_const_iff {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [l.NeBot] {X : ι → Ω → ℝ} {c : ℝ} (hX : ∀ i, AEMeasurable (X i) P) :
    TendstoInDistribution X l (fun _ => c) (fun _ => P) P ↔
      TendstoInMeasure P X l (fun _ => c) :=
  ⟨tendstoInMeasure_of_tendstoInDistribution_const, fun h => h.tendstoInDistribution hX⟩

omit [IsProbabilityMeasure P] in
/-- **Continuous mapping at a point** (Hayashi Lemma 2.3(a)): if `X_n →p c` and
`q` is continuous at `c`, then `q(X_n) →p q(c)`. -/
theorem TendstoInMeasure.comp_continuousAt {ι : Type*} {l : Filter ι} {X : ι → Ω → ℝ}
    {c : ℝ} (h : TendstoInMeasure P X l (fun _ => c)) {q : ℝ → ℝ} (hq : ContinuousAt q c) :
    TendstoInMeasure P (fun i ω => q (X i ω)) l (fun _ => q c) := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hq ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ => zero_le) (fun i => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
  by_contra hlt; push Not at hlt
  have := hball (x := X i ω) (by rw [Real.dist_eq]; exact hlt)
  rw [Real.dist_eq] at this
  linarith

/-- A deterministic sequence tending to `a` converges in probability to `a`. -/
lemma tendstoInMeasure_const_seq {b : ℕ → ℝ} {a : ℝ} (hb : Tendsto b atTop (𝓝 a)) :
    TendstoInMeasure P (fun n (_ : Ω) => b n) atTop (fun _ => a) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall fun _ => hb)

lemma tendsto_inv_sqrt_nat : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Root-n consistency**: if `√n (T_n − θ) →d Z` then `T_n →p θ`. -/
theorem tendstoInMeasure_of_sqrt {T : ℕ → Ω → ℝ} {θ : ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n * (T n ω - θ)) atTop Z
      (fun _ => P) P') :
    TendstoInMeasure P T atTop (fun _ => θ) := by
  have hprod := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop)
    (tendstoInMeasure_const_seq (P := P) tendsto_inv_sqrt_nat) (fun _ => aemeasurable_const)
  simp only [zero_mul] at hprod
  have hp := tendstoInMeasure_of_tendstoInDistribution_const hprod
  rw [tendstoInMeasure_iff_norm] at hp ⊢
  intro ε hε
  refine (hp ε hε).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  congr 1; ext ω
  have hs : Real.sqrt n ≠ 0 := by positivity
  simp only [Set.mem_ofPred_eq, sub_zero, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- The difference quotient of `g` at `θ`, extended by `g'` at `θ`. -/
noncomputable def diffQuot (g : ℝ → ℝ) (g' θ : ℝ) (t : ℝ) : ℝ :=
  if t = θ then g' else (g t - g θ) / (t - θ)

lemma diffQuot_continuousAt {g : ℝ → ℝ} {g' θ : ℝ} (hd : HasDerivAt g g' θ) :
    ContinuousAt (diffQuot g g' θ) θ := by
  have : diffQuot g g' θ = Function.update (slope g θ) θ g' := by
    funext t
    by_cases ht : t = θ
    · subst ht; simp [diffQuot]
    · simp [diffQuot, ht, slope_def_field]
  rw [this, continuousAt_update_same]
  exact hd.tendsto_slope

lemma diffQuot_measurable {g : ℝ → ℝ} (hg : Measurable g) (g' θ : ℝ) :
    Measurable (diffQuot g g' θ) :=
  Measurable.ite (measurableSet_singleton θ) measurable_const
    ((hg.sub measurable_const).div (measurable_id.sub measurable_const))

lemma mul_diffQuot (g : ℝ → ℝ) (g' θ s t : ℝ) :
    s * (g t - g θ) = s * (t - θ) * diffQuot g g' θ t := by
  by_cases ht : t = θ
  · subst ht; simp
  · have : t - θ ≠ 0 := sub_ne_zero.mpr ht
    simp only [diffQuot, ht, ite_false]
    field_simp

/-- **Delta method** (van der Vaart Thm 3.1; Hayashi Lemma 2.5): if
`√n (T_n − θ) →d Z` and `g` is (measurable and) differentiable at `θ`, then
`√n (g(T_n) − g(θ)) →d g'(θ) Z`. -/
theorem delta_method {T : ℕ → Ω → ℝ} {θ : ℝ} {Z : Ω' → ℝ}
    (hT : ∀ n, AEMeasurable (T n) P)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n * (T n ω - θ)) atTop Z
      (fun _ => P) P')
    {g : ℝ → ℝ} (hg : Measurable g) {g' : ℝ} (hd : HasDerivAt g g' θ) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n * (g (T n ω) - g θ)) atTop
      (fun ω => g' * Z ω) (fun _ => P) P' := by
  have hq := TendstoInMeasure.comp_continuousAt (tendstoInMeasure_of_sqrt h)
    (diffQuot_continuousAt hd)
  have hq' : diffQuot g g' θ θ = g' := by simp [diffQuot]
  rw [hq'] at hq
  have := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hq
    (fun n => (diffQuot_measurable hg g' θ).comp_aemeasurable (hT n))
  convert this using 2 with n
  funext ω
  simp only [mul_diffQuot g g' θ (Real.sqrt n) (T n ω)]
  ring

/-- **Delta method with the CLT**: for i.i.d. `X_i` with finite variance `σ²`
and `g` differentiable at `μ = E[X]`, `√n (g(X̄_n) − g(μ))` converges in
distribution to a random variable `g'(μ) Y` whose law is
`N(0, g'(μ)² σ²)`. -/
theorem delta_method_clt {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P') (hX : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {g : ℝ → ℝ} (hg : Measurable g) {g' : ℝ} (hd : HasDerivAt g g' P[X 0]) :
    TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n * (g ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω) - g P[X 0]))
        atTop (fun ω => g' * Y ω) (fun _ => P) P' ∧
      P'.map (fun ω => g' * Y ω)
        = gaussianReal 0 (⟨g' ^ 2, sq_nonneg _⟩ * Var[X 0; P].toNNReal) := by
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident
  have hmeas : ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω) P :=
    fun n => (Finset.aemeasurable_fun_sum _ fun k _ =>
      (hident k).aemeasurable_fst).const_mul _
  refine ⟨delta_method hmeas ?_ hg hd, ?_⟩
  · convert hclt using 2 with n
    funext ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have key : ∀ S m : ℝ, Real.sqrt n * ((Real.sqrt n * Real.sqrt n)⁻¹ * S - m)
          = (Real.sqrt n)⁻¹ * (S - Real.sqrt n * Real.sqrt n * m) := by
        intro S m; field_simp
      have := key (∑ k ∈ Finset.range n, X k ω) P[X 0]
      rwa [Real.mul_self_sqrt (Nat.cast_nonneg n)] at this
  · rw [show (fun ω => g' * Y ω) = (g' * ·) ∘ Y from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY.aemeasurable, hY.map_eq,
      gaussianReal_map_const_mul, mul_zero]
    rfl

end Econ.Asymptotics
