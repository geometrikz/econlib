/-
# Tâtonnement with any number of goods: the max-ratio Lyapunov function

PLAN.md §7.2a (bridge B0). MWG §17.H; Arrow & Hurwicz (1958), Arrow, Block &
Hurwicz (1959).

`Tatonnement.lean` uses the Euclidean distance `‖p − p*‖²`, which needs the
weak axiom `p* · z(p) > 0`; under gross substitutes that is proved there only
for two goods. Arrow and Hurwicz's other Lyapunov function works for **any
number of goods** and needs only gross substitutes and homogeneity:

    M(p) = maxᵢ pᵢ / p*ᵢ        and        m(p) = minᵢ pᵢ / p*ᵢ.

**Static step** (`GrossSubstitutes.excess_nonpos_of_max_ratio`,
`GrossSubstitutes.excess_nonneg_of_min_ratio`): at any `p ≫ 0`, the good whose
price is highest relative to `p*` is in weak excess supply, and the good whose
relative price is lowest is in weak excess demand. Strictly, unless `p` is a
multiple of `p*` (`GrossSubstitutes.excess_neg_of_max_ratio`).

**Dynamic step** (`antitoneOn_sup'_of_hasDerivWithinAt`): the maximum of
finitely many functions is nonincreasing if every function that attains the
maximum has nonpositive derivative there. This is a Danskin-type argument
through Mathlib's barrier lemma.

**Result** (`tatonnement_maxRatio_antitone`, `tatonnement_minRatio_monotone`,
`tatonnement_bounded`): along a tâtonnement path that stays in the positive
orthant, `M` never rises and `m` never falls, so the path stays in the box
`m(p(0)) p* ≤ p(t) ≤ M(p(0)) p*`. Invariance of this box implies Lyapunov
stability of each equilibrium `c p*` (the ε–δ form is not stated formally).
Convergence (LaSalle) is still not claimed.

Scope: positivity of the path is assumed (`hpos`), since gross substitutes and
homogeneity are only defined on `p ≫ 0`; Arrow–Hurwicz derive it from the box.
Adjustment speeds are unit (`ṗ = z(p)`), not the general `ṗᵢ = kᵢ zᵢ`.
-/
module

public import EconLean.Bridges.Aggregation.Tatonnement
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace Econ

open Filter Topology Set Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Static step -/

/-- At the good with the **highest** price relative to `p*`, excess demand is
nonpositive. -/
theorem GrossSubstitutes.excess_nonpos_of_max_ratio {z : (ι → ℝ) → (ι → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) {pstar q : ι → ℝ}
    (hps : PositivePrices pstar) (hq : PositivePrices q) (hzs : z pstar = 0) {k : ι}
    (hk : ∀ i, q i / pstar i ≤ q k / pstar k) : z q k ≤ 0 := by
  set c := q k / pstar k with hc
  have hc0 : 0 < c := div_pos (hq k) (hps k)
  set q' := c • pstar with hq'
  have hzq' : z q' = 0 := by rw [hq', hhom pstar hps c hc0, hzs]
  have hle : q ≤ q' := fun i => by
    have := hk i
    rw [div_le_iff₀ (hps i)] at this
    simpa [hq'] using this
  have hkk : q k = q' k := by
    simp only [hq', Pi.smul_apply, smul_eq_mul, hc]; field_simp [(hps k).ne']
  by_cases hne : q = q'
  · rw [hne, hzq']; rfl
  · have := hGS.lt_of_le hq hle hne hkk
    rw [hzq'] at this
    exact this.le

/-- Strict version: if `q` is not a multiple of `p*`, the good with the highest
relative price is in **strict** excess supply. -/
theorem GrossSubstitutes.excess_neg_of_max_ratio {z : (ι → ℝ) → (ι → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) {pstar q : ι → ℝ}
    (hps : PositivePrices pstar) (hq : PositivePrices q) (hzs : z pstar = 0) {k : ι}
    (hk : ∀ i, q i / pstar i ≤ q k / pstar k) (hne : q ≠ (q k / pstar k) • pstar) :
    z q k < 0 := by
  set c := q k / pstar k with hc
  have hc0 : 0 < c := div_pos (hq k) (hps k)
  have hzq' : z (c • pstar) = 0 := by rw [hhom pstar hps c hc0, hzs]
  have hle : q ≤ c • pstar := fun i => by
    have := hk i
    rw [div_le_iff₀ (hps i)] at this
    simpa using this
  have hkk : q k = (c • pstar) k := by
    simp only [Pi.smul_apply, smul_eq_mul, hc]; field_simp [(hps k).ne']
  have := hGS.lt_of_le hq hle hne hkk
  rwa [hzq'] at this

/-- At the good with the **lowest** price relative to `p*`, excess demand is
nonnegative. -/
theorem GrossSubstitutes.excess_nonneg_of_min_ratio {z : (ι → ℝ) → (ι → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) {pstar q : ι → ℝ}
    (hps : PositivePrices pstar) (hq : PositivePrices q) (hzs : z pstar = 0) {k : ι}
    (hk : ∀ i, q k / pstar k ≤ q i / pstar i) : 0 ≤ z q k := by
  set c := q k / pstar k with hc
  have hc0 : 0 < c := div_pos (hq k) (hps k)
  set q' := c • pstar with hq'
  have hq'pos : PositivePrices q' := fun i => by
    simp only [hq', Pi.smul_apply, smul_eq_mul]; exact mul_pos hc0 (hps i)
  have hzq' : z q' = 0 := by rw [hq', hhom pstar hps c hc0, hzs]
  have hle : q' ≤ q := fun i => by
    have := hk i
    rw [le_div_iff₀ (hps i)] at this
    simpa [hq'] using this
  have hkk : q' k = q k := by
    simp only [hq', Pi.smul_apply, smul_eq_mul, hc]; field_simp [(hps k).ne']
  by_cases hne : q' = q
  · rw [← hne, hzq']; rfl
  · have := hGS.lt_of_le hq'pos hle hne hkk
    rw [hzq'] at this
    exact this.le

/-! ### Dynamic step: the maximum of finitely many functions -/

omit [DecidableEq ι] in
/-- **Danskin-type monotonicity.** Let `f i` (finitely many) have derivatives
`f' i t` within `[0, ∞)` (one-sided at `0`). If at every `t ≥ 0` each `f i` that
attains the maximum has `f' i t ≤ 0`, then `t ↦ maxᵢ f i t` is nonincreasing on
`[0, ∞)`. -/
theorem antitoneOn_sup'_of_hasDerivWithinAt [Nonempty ι] {f f' : ι → ℝ → ℝ}
    (hd : ∀ i t, 0 ≤ t → HasDerivWithinAt (f i) (f' i t) (Ici 0) t)
    (hmax : ∀ t, 0 ≤ t → ∀ i, (∀ j, f j t ≤ f i t) → f' i t ≤ 0) :
    AntitoneOn (fun t => univ.sup' univ_nonempty fun i => f i t) (Ici 0) := by
  set M : ℝ → ℝ := fun t => univ.sup' univ_nonempty fun i => f i t with hM
  have hcont : ∀ i, ContinuousOn (f i) (Ici 0) := fun i t ht =>
    (hd i t ht).continuousWithinAt
  have hMcont : ContinuousOn M (Ici 0) := by
    have : ContinuousOn (fun t => univ.sup' univ_nonempty fun i => f i t) (Ici 0) :=
      ContinuousOn.finset_sup'_apply univ_nonempty fun i _ => hcont i
    exact this
  -- Eventually-to-the-right slope bound at every `x ≥ 0`.
  have hslope : ∀ x, 0 ≤ x → ∀ r, 0 < r → ∀ᶠ y in 𝓝[>] x, M y < M x + r * (y - x) := by
    intro x hx r hr
    have hi : ∀ i, ∀ᶠ y in 𝓝[>] x, f i y < M x + r * (y - x) := by
      intro i
      by_cases hA : ∀ j, f j x ≤ f i x
      · have hfi : f i x = M x :=
          le_antisymm (le_sup' (fun i => f i x) (mem_univ i)) (sup'_le _ _ fun j _ => hA j)
        have hder : HasDerivWithinAt (f i) (f' i x) (Ioi x) x :=
          (hd i x hx).mono fun y hy => le_trans hx (le_of_lt hy)
        have ht := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1 hder
        have hlt : f' i x < r := lt_of_le_of_lt (hmax x hx i hA) hr
        filter_upwards [ht (Iio_mem_nhds hlt), self_mem_nhdsWithin] with y hy hyx
        have hyx' : 0 < y - x := sub_pos.2 hyx
        rw [Set.mem_preimage, Set.mem_Iio, slope_def_field, div_lt_iff₀ hyx'] at hy
        linarith
      · push Not at hA
        obtain ⟨j, hj⟩ := hA
        have hlt : f i x < M x :=
          lt_of_lt_of_le hj (le_sup' (fun i => f i x) (mem_univ j))
        have hc : ContinuousWithinAt (f i) (Ioi x) x :=
          (hcont i x hx).mono fun y hy => le_trans hx (le_of_lt hy)
        filter_upwards [hc (Iio_mem_nhds hlt), self_mem_nhdsWithin] with y hy hyx
        have : 0 < r * (y - x) := mul_pos hr (sub_pos.2 hyx)
        rw [Set.mem_preimage, Set.mem_Iio] at hy
        linarith
    have hall := (Filter.eventually_all (ι := ι)).2 hi
    filter_upwards [hall] with y hy
    exact (sup'_lt_iff _).2 fun i _ => hy i
  intro a ha b hb hab
  -- For every `ε > 0`, `M b ≤ M a + ε (b - a)`.
  have key : ∀ ε, 0 < ε → M b ≤ M a + ε * (b - a) := by
    intro ε hε
    have hbar := image_le_of_liminf_slope_right_lt_deriv_boundary' (f := M) (f' := fun _ => 0)
      (a := a) (b := b) (hMcont.mono fun y hy => le_trans (mem_Ici.1 ha) hy.1)
      (fun x hx r hr => ?_) (B := fun t => M a + ε * (t - a)) (B' := fun _ => ε)
      (by simp) (by fun_prop) (fun x _ => ?_) (fun x _ _ => hε) (x := b)
      ⟨hab, le_rfl⟩
    · exact hbar
    · have hx0 : 0 ≤ x := le_trans (mem_Ici.1 ha) hx.1
      refine Eventually.frequently ?_
      filter_upwards [hslope x hx0 r hr, self_mem_nhdsWithin] with y hy hyx
      have hyx' : 0 < y - x := sub_pos.2 hyx
      rw [slope_def_field, div_lt_iff₀ hyx']
      linarith
    · have : HasDerivAt (fun t => M a + ε * (t - a)) ε x := by
        simpa using ((hasDerivAt_id x).sub_const a).const_mul ε |>.const_add (M a)
      exact this.hasDerivWithinAt
  by_contra hcon
  push Not at hcon
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  rcases hba.eq_or_lt with h0 | hpos
  · have : b = a := by linarith
    subst this; exact lt_irrefl _ hcon
  · have hε : 0 < (M b - M a) / (2 * (b - a)) := div_pos (by linarith) (by linarith)
    have := key _ hε
    have : (M b - M a) / (2 * (b - a)) * (b - a) = (M b - M a) / 2 := by
      field_simp
    linarith

/-! ### Tâtonnement -/

/-- The largest price relative to `p*`. -/
noncomputable def maxRatio [Nonempty ι] (q pstar : ι → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun i => q i / pstar i

/-- The smallest price relative to `p*`. -/
noncomputable def minRatio [Nonempty ι] (q pstar : ι → ℝ) : ℝ :=
  univ.inf' univ_nonempty fun i => q i / pstar i

omit [Fintype ι] [DecidableEq ι] in
theorem IsTatonnementPath.hasDerivWithinAt_ratio {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    (hpath : IsTatonnementPath z p) (pstar : ι → ℝ) (i : ι) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => p t i / pstar i) (z (p t) i / pstar i) (Ici 0) t :=
  (hasDerivWithinAt_pi.1 (hpath t ht) i).div_const _

variable [Nonempty ι]

/-- **Arrow–Hurwicz, upper bound.** Along a tâtonnement path in the positive
orthant, with gross substitutes, homogeneity of degree zero and an equilibrium
`p* ≫ 0`, the largest relative price `maxᵢ pᵢ(t)/p*ᵢ` never rises. Any number
of goods; Walras' law is not needed. -/
theorem tatonnement_maxRatio_antitone {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    {pstar : ι → ℝ} (hpath : IsTatonnementPath z p) (hpos : ∀ t, 0 ≤ t → PositivePrices (p t))
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) (hps : PositivePrices pstar)
    (hzs : z pstar = 0) :
    AntitoneOn (fun t => maxRatio (p t) pstar) (Ici 0) :=
  antitoneOn_sup'_of_hasDerivWithinAt (f := fun i t => p t i / pstar i)
    (f' := fun i t => z (p t) i / pstar i)
    (fun i _ ht => hpath.hasDerivWithinAt_ratio pstar i ht)
    fun t ht i hi => div_nonpos_of_nonpos_of_nonneg
      (hGS.excess_nonpos_of_max_ratio hhom hps (hpos t ht) hzs hi) (hps i).le

/-- **Arrow–Hurwicz, lower bound.** Under the same hypotheses the smallest
relative price `minᵢ pᵢ(t)/p*ᵢ` never falls. -/
theorem tatonnement_minRatio_monotone {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    {pstar : ι → ℝ} (hpath : IsTatonnementPath z p) (hpos : ∀ t, 0 ≤ t → PositivePrices (p t))
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) (hps : PositivePrices pstar)
    (hzs : z pstar = 0) :
    MonotoneOn (fun t => minRatio (p t) pstar) (Ici 0) := by
  have hA := antitoneOn_sup'_of_hasDerivWithinAt (f := fun i t => -(p t i / pstar i))
    (f' := fun i t => -(z (p t) i / pstar i))
    (fun i _ ht => (hpath.hasDerivWithinAt_ratio pstar i ht).neg)
    fun t ht i hi => by
      have hk : ∀ j, p t i / pstar i ≤ p t j / pstar j := fun j => by
        have := hi j; linarith
      have := div_nonneg (hGS.excess_nonneg_of_min_ratio hhom hps (hpos t ht) hzs hk)
        (hps i).le
      linarith
  intro a ha b hb hab
  simp only [minRatio]
  refine le_inf' _ _ fun i _ => ?_
  have h1 : -(p b i / pstar i) ≤ univ.sup' univ_nonempty fun j => -(p b j / pstar j) :=
    le_sup' (fun j => -(p b j / pstar j)) (mem_univ i)
  have h2 := hA ha hb hab
  have h3 : (univ.sup' univ_nonempty fun j => -(p a j / pstar j)) ≤
      -(univ.inf' univ_nonempty fun j => p a j / pstar j) :=
    sup'_le _ _ fun j _ => neg_le_neg (inf'_le _ (mem_univ j))
  simp only at h2
  linarith

/-- **Invariant box around the equilibrium ray** (Arrow & Hurwicz 1958), for any
number of goods: a tâtonnement path in the positive orthant stays in the box
`m p* ≤ p(t) ≤ M p*`, where `m` and `M` are the smallest and largest relative
prices at time `0`. -/
theorem tatonnement_bounded {z : (ι → ℝ) → (ι → ℝ)} {p : ℝ → ι → ℝ}
    {pstar : ι → ℝ} (hpath : IsTatonnementPath z p) (hpos : ∀ t, 0 ≤ t → PositivePrices (p t))
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) (hps : PositivePrices pstar)
    (hzs : z pstar = 0) {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    minRatio (p 0) pstar * pstar i ≤ p t i ∧ p t i ≤ maxRatio (p 0) pstar * pstar i := by
  have hM := tatonnement_maxRatio_antitone hpath hpos hGS hhom hps hzs
    (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  have hm := tatonnement_minRatio_monotone hpath hpos hGS hhom hps hzs
    (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simp only at hM hm
  have hle : p t i / pstar i ≤ maxRatio (p t) pstar := le_sup' (fun j => p t j / pstar j) (mem_univ i)
  have hge : minRatio (p t) pstar ≤ p t i / pstar i := inf'_le (fun j => p t j / pstar j) (mem_univ i)
  constructor
  · rw [← le_div_iff₀ (hps i)]; linarith
  · rw [← div_le_iff₀ (hps i)]; linarith

namespace TatonnementSupExamples

/-- A gross-substitute, degree-zero homogeneous excess demand on two goods:
`z(p) = ((p₁ − p₀)/(p₀ + p₁), (p₀ − p₁)/(p₀ + p₁))`, with equilibrium `(1, 1)`.
It does not satisfy Walras' law (`p · z(p) = −(p₀ − p₁)²/(p₀ + p₁) ≤ 0`), so it is
not the excess demand of any locally nonsatiated economy; the max-ratio
theorems do not use Walras' law. It only witnesses that their hypotheses hold together along a nonconstant path. -/
noncomputable def zEx (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(p 1 - p 0) / (p 0 + p 1), (p 0 - p 1) / (p 0 + p 1)]

/-- The explicit tâtonnement path `p(t) = (1 − e^{−t}/2, 1 + e^{−t}/2)`. -/
noncomputable def pEx (t : ℝ) : Fin 2 → ℝ := ![1 - Real.exp (-t) / 2, 1 + Real.exp (-t) / 2]

theorem grossSubstitutes_zEx : GrossSubstitutes zEx := by
  intro p l t hp hlt k hkl
  have h0 := hp 0; have h1 := hp 1
  fin_cases l <;> fin_cases k <;> simp [zEx] at hkl hlt ⊢
  · -- raise `p₀`, good `1`
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · -- raise `p₁`, good `0`
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem homogeneousZero_zEx : HomogeneousZero zEx := by
  intro p hp c hc
  have h0 := hp 0; have h1 := hp 1
  funext i
  fin_cases i <;> simp [zEx] <;> rw [← mul_add, ← mul_sub, mul_div_mul_left _ _ hc.ne']

theorem zEx_one : zEx (fun _ => 1) = 0 := by
  funext i; fin_cases i <;> simp [zEx]

theorem pEx_pos {t : ℝ} (ht : 0 ≤ t) : PositivePrices (pEx t) := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 := Real.exp_pos (-t)
  intro i; fin_cases i <;> simp [pEx] <;> linarith

theorem zEx_pEx (t : ℝ) : zEx (pEx t) = ![Real.exp (-t) / 2, -(Real.exp (-t) / 2)] := by
  funext i
  fin_cases i <;> simp [zEx, pEx] <;> ring

theorem isTatonnementPath_pEx : IsTatonnementPath zEx pEx := by
  intro t _
  have hd : HasDerivAt (fun t => Real.exp (-t) / 2) (-(Real.exp (-t) / 2)) t := by
    have := ((hasDerivAt_neg t).exp).div_const 2
    convert this using 1; ring
  rw [zEx_pEx]
  refine (hasDerivAt_pi.2 fun i => ?_).hasDerivWithinAt
  fin_cases i
  · convert hd.const_sub 1 using 1
    · funext x; simp [pEx]
    · simp
  · convert hd.const_add 1 using 1
    · funext x; simp [pEx]
    · simp

/-- The hypotheses of `tatonnement_bounded` hold along the nonconstant path
`pEx`, which starts at `(1/2, 3/2)` and moves toward `(1, 1)`. -/
theorem pEx_bounded {t : ℝ} (ht : 0 ≤ t) (i : Fin 2) :
    minRatio (pEx 0) (fun _ => 1) * 1 ≤ pEx t i ∧ pEx t i ≤ maxRatio (pEx 0) (fun _ => 1) * 1 :=
  tatonnement_bounded isTatonnementPath_pEx (fun _ h => pEx_pos h) grossSubstitutes_zEx
    homogeneousZero_zEx (fun _ => one_pos) zEx_one ht i

theorem pEx_nonconstant : pEx 0 ≠ pEx 1 := by
  intro h
  have := congrFun h 0
  simp [pEx] at this
  have : Real.exp (-1) < 1 := by simp
  linarith

end TatonnementSupExamples

end Econ
