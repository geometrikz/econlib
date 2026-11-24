/-
# ESS: uniform invasion barriers and local superiority

References. J. Weibull (1995), *Evolutionary Game Theory*, §2.1,
Propositions 2.5 and 2.6 (Hofbauer, Schuster and Sigmund 1979 for local
superiority).

Notation of `ESS.lean`: a symmetric two-player game with payoff matrix `A`,
`E(x, y) = xᵀ A y`, mixed strategies in the simplex `Δ` (`lotteries`).

**Results.**
* `isESS_iff_uniform` (Weibull Prop. 2.5): `x ∈ Δ` is an ESS iff it has a
  *uniform* invasion barrier: one `ε̄ ∈ (0, 1]` such that, for **every**
  mutant `y ≠ x` and every `ε ∈ (0, ε̄)`, `x` does strictly better than `y`
  against the post-entry population `(1 − ε) x + ε y`. (`IsESS` is the
  payoff-comparison definition; `isESS_iff_invasion` in `ESS.lean` is the
  version with a barrier depending on `y`.)
* `isESS_iff_locallySuperior` (Weibull Prop. 2.6, Hofbauer–Schuster–Sigmund):
  `x` is an ESS iff it is *locally superior*: there is `δ > 0` such that
  `E(y, y) < E(x, y)` for every `y ∈ Δ`, `y ≠ x`, within sup-distance `δ` of
  `x`.
* `hawkDove_uniform_locallySuperior`: non-vacuity, the mixed Hawk–Dove ESS
  `V/C` (`0 < V < C`) has both properties.

**Proof.** Every mutant `y ≠ x` lies on a segment from `x` to a point `z` of
the compact set `Z_x` of strategies that put zero weight on some pure
strategy in the support of `x` (`exists_ray`): `y = (1 − λ) x + λ z` with
`λ ∈ (0, 1]`, and the advantage of `x` over `y` at `ε` is `λ` times the
advantage over `z` at `ελ` (`advantage_ray`). On `Z_x` the continuous
function `max(E(x,x) − E(z,x), E(x,z) − E(z,z))` is positive, so it has a
positive minimum, which gives the uniform barrier.
-/
module

public import EconLean.BoundedRationality.ESS
public import EconLean.Games.Mixed

@[expose] public section

noncomputable section

namespace Econ

namespace ESS

open Finset

variable {n : ℕ} {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}

/-- The post-entry population `(1 − ε) x + ε y`. -/
def post (x y : Fin n → ℝ) (ε : ℝ) : Fin n → ℝ := fun j => (1 - ε) * x j + ε * y j

theorem lotteries_le_one {y : Fin n → ℝ} (hy : y ∈ lotteries (Fin n)) (i : Fin n) : y i ≤ 1 := by
  rw [← hy.2]; exact single_le_sum (fun j _ => hy.1 j) (mem_univ i)

theorem post_mem {x y : Fin n → ℝ} (hx : x ∈ lotteries (Fin n)) (hy : y ∈ lotteries (Fin n))
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : post x y ε ∈ lotteries (Fin n) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold post; have := hx.1 j; have := hy.1 j; nlinarith
  · simp only [post, sum_add_distrib, ← mul_sum, hx.2, hy.2]; ring

/-- **Every mutant lies on a ray from `x` through `Z_x`.** -/
theorem exists_ray (hx : x ∈ lotteries (Fin n)) {y : Fin n → ℝ} (hy : y ∈ lotteries (Fin n))
    (hyx : y ≠ x) :
    ∃ z ∈ lotteries (Fin n), ∃ i0, 0 < x i0 ∧ z i0 = 0 ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧
      y = post x z l ∧ l * x i0 = x i0 - y i0 := by
  classical
  set S := univ.filter fun i => y i < x i
  have hS : S.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hne
    have hle : ∀ i ∈ (univ : Finset (Fin n)), x i ≤ y i := fun i _ => not_lt.1 (hne (mem_univ i))
    have := (sum_eq_sum_iff_of_le hle).1 (by rw [hx.2, hy.2])
    exact hyx (funext fun i => (this i (mem_univ i)).symm)
  have hpos : ∀ i ∈ S, 0 < x i := fun i hi => by
    have := (mem_filter.1 hi).2; linarith [hy.1 i]
  obtain ⟨i0, hi0, hmax⟩ := exists_max_image S (fun i => (x i - y i) / x i) hS
  have hx0 := hpos i0 hi0
  have hlt0 : y i0 < x i0 := (mem_filter.1 hi0).2
  set l := (x i0 - y i0) / x i0
  have hl : 0 < l := div_pos (by linarith) hx0
  have hl1 : l ≤ 1 := by rw [div_le_one hx0]; linarith [hy.1 i0]
  refine ⟨fun i => x i + (y i - x i) / l, ⟨fun i => ?_, ?_⟩, i0, hx0, ?_, l, hl, hl1, ?_, ?_⟩
  · by_cases hi : y i < x i
    · have hxi := hpos i (mem_filter.2 ⟨mem_univ i, hi⟩)
      have h1 : (x i - y i) / x i ≤ l := hmax i (mem_filter.2 ⟨mem_univ i, hi⟩)
      rw [div_le_iff₀ hxi] at h1
      have : (x i - y i) / l ≤ x i := by rw [div_le_iff₀ hl]; linarith
      have : (y i - x i) / l = -((x i - y i) / l) := by ring
      linarith
    · rw [not_lt] at hi
      have := hx.1 i
      have : 0 ≤ (y i - x i) / l := div_nonneg (by linarith) hl.le
      linarith
  · rw [sum_add_distrib, ← sum_div, sum_sub_distrib, hx.2, hy.2]; simp
  · simp only [l]; field_simp; ring
  · funext i; simp only [post]; field_simp; ring
  · simp only [l]; field_simp

/-- Advantage of `x` over `y` against the post-entry population. -/
def adv (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (ε : ℝ) : ℝ :=
  E A x (post x y ε) - E A y (post x y ε)

theorem adv_eq (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (ε : ℝ) :
    adv A x y ε = (1 - ε) * (E A x x - E A y x) + ε * (E A x y - E A y y) :=
  advantage_eq A x y ε

/-- **The advantage scales along a ray.** -/
theorem advantage_ray (A : Fin n → Fin n → ℝ) (x z : Fin n → ℝ) (l ε : ℝ) :
    adv A x (post x z l) ε = l * adv A x z (ε * l) := by
  rw [adv_eq, adv_eq]
  have h1 : E A (post x z l) x = (1 - l) * E A x x + l * E A z x := E_mix_left A x z x _ _
  have h2 : E A x (post x z l) = (1 - l) * E A x x + l * E A x z := E_mix_right A x x z _ _
  have h3 : E A z (post x z l) = (1 - l) * E A z x + l * E A z z := E_mix_right A z x z _ _
  have h4 : E A (post x z l) (post x z l) =
      (1 - l) * E A x (post x z l) + l * E A z (post x z l) := E_mix_left A x z _ _ _
  rw [h4, h1, h2, h3]
  ring

/-- `E` is bounded on the simplex. -/
theorem abs_E_le {u v : Fin n → ℝ} (hu : u ∈ lotteries (Fin n)) (hv : v ∈ lotteries (Fin n)) :
    |E A u v| ≤ ∑ i, ∑ j, |A i j| := by
  unfold E
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hu.1 i), abs_of_nonneg (hv.1 j)]
  have h1 := lotteries_le_one hu i
  have h2 := lotteries_le_one hv j
  have := abs_nonneg (A i j)
  have := hu.1 i
  have := hv.1 j
  nlinarith [mul_le_mul h1 h2 (hv.1 j) zero_le_one]

theorem continuous_E_left (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    Continuous fun u => E A u v := by
  unfold E; fun_prop

theorem continuous_E_right (A : Fin n → Fin n → ℝ) (u : Fin n → ℝ) :
    Continuous fun v => E A u v := by
  unfold E; fun_prop

theorem continuous_E_diag (A : Fin n → Fin n → ℝ) : Continuous fun u => E A u u := by
  unfold E; fun_prop

/-- **Weibull Proposition 2.5: uniform invasion barrier.** -/
theorem isESS_iff_uniform (A : Fin n → Fin n → ℝ) (hx : x ∈ lotteries (Fin n)) :
    IsESS A x ↔ ∃ εbar > 0, εbar ≤ 1 ∧ ∀ y ∈ lotteries (Fin n), y ≠ x → ∀ ε, 0 < ε → ε < εbar →
      E A y (post x y ε) < E A x (post x y ε) := by
  constructor
  · intro hess
    -- the compact set `Z_x`
    set Z : Set (Fin n → ℝ) := lotteries (Fin n) ∩ ⋃ i, {z | 0 < x i ∧ z i = 0}
    have hZ : IsCompact Z := by
      refine (isCompact_lotteries (Fin n)).inter_right (isClosed_iUnion_of_finite fun i => ?_)
      exact isClosed_const.inter (isClosed_eq (continuous_apply i) continuous_const)
    set φ : (Fin n → ℝ) → ℝ := fun z => max (E A x x - E A z x) (E A x z - E A z z)
    have hφc : Continuous φ :=
      (continuous_const.sub (continuous_E_left A x)).max
        ((continuous_E_right A x).sub (continuous_E_diag A))
    have hφpos : ∀ z ∈ Z, 0 < φ z := by
      rintro z ⟨hz, hzi⟩
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion.1 hzi
      have hzx : z ≠ x := fun h => by rw [h] at hzi; linarith
      rcases hess.2 z hz hzx with h | ⟨_, h⟩
      · exact lt_max_of_lt_left (by linarith)
      · exact lt_max_of_lt_right (by linarith)
    -- a positive lower bound `m` on `Z`
    obtain ⟨m, hm, hmZ⟩ : ∃ m > 0, ∀ z ∈ Z, m ≤ φ z := by
      rcases Z.eq_empty_or_nonempty with hZe | hZne
      · exact ⟨1, one_pos, fun z hz => by rw [hZe] at hz; exact absurd hz (Set.notMem_empty z)⟩
      · obtain ⟨z0, hz0, hmin⟩ := hZ.exists_isMinOn hZne hφc.continuousOn
        exact ⟨φ z0, hφpos z0 hz0, fun z hz => hmin hz⟩
    set M := ∑ i, ∑ j, |A i j|
    have hM : 0 ≤ M := sum_nonneg fun i _ => sum_nonneg fun j _ => abs_nonneg _
    refine ⟨m / (m + 2 * M + 1), by positivity,
      (div_le_one (by positivity)).2 (by linarith), fun y hy hyx ε hε hεb => ?_⟩
    obtain ⟨z, hz, i0, hxi0, hzi0, l, hl, hl1, rfl, -⟩ := exists_ray hx hy hyx
    have hzZ : z ∈ Z := ⟨hz, Set.mem_iUnion.2 ⟨i0, hxi0, hzi0⟩⟩
    -- the advantage over `z` is positive at `ε l`
    have hεl : 0 < ε * l := mul_pos hε hl
    have hεl1 : ε * l < m / (m + 2 * M + 1) := lt_of_le_of_lt
      (by nlinarith) hεb
    have hnash := (isNash_of_isESS hess).2 z hz
    have ha_le : |E A x x - E A z x| ≤ 2 * M := by
      have := abs_E_le (A := A) hx hx; have := abs_E_le (A := A) hz hx
      have := abs_sub (E A x x) (E A z x); linarith
    have hc_le : |E A x z - E A z z| ≤ 2 * M := by
      have := abs_E_le (A := A) hx hz; have := abs_E_le (A := A) hz hz
      have := abs_sub (E A x z) (E A z z); linarith
    have hden : 0 < m + 2 * M + 1 := by positivity
    have hε' : ε * l * (m + 2 * M + 1) < m := by rwa [lt_div_iff₀ hden] at hεl1
    have hεl_lt1 : ε * l < 1 := by nlinarith
    have hadv : 0 < adv A x z (ε * l) := by
      rw [adv_eq]
      have hmz := hmZ z hzZ
      set a := E A x x - E A z x
      set c := E A x z - E A z z
      have hc' := neg_abs_le c
      by_cases ha : m ≤ a
      · nlinarith
      · rw [not_le] at ha
        have hcm : m ≤ c := by
          rcases le_max_iff.1 hmz with h | h
          · linarith
          · exact h
        have ha0 : 0 ≤ a := by simp only [a]; linarith
        nlinarith
    have := advantage_ray A x z l ε
    have hpos : 0 < adv A x (post x z l) ε := by rw [this]; exact mul_pos hl hadv
    unfold adv at hpos
    linarith
  · rintro ⟨εbar, hεbar, -, h⟩
    exact (isESS_iff_invasion A hx).2 fun y hy hyx => ⟨εbar, hεbar, h y hy hyx⟩

/-- **Weibull Proposition 2.6 (Hofbauer–Schuster–Sigmund): local
superiority.** -/
theorem isESS_iff_locallySuperior (A : Fin n → Fin n → ℝ) (hx : x ∈ lotteries (Fin n)) :
    IsESS A x ↔ ∃ δ > 0, ∀ y ∈ lotteries (Fin n), y ≠ x → (∀ i, |y i - x i| < δ) →
      E A y y < E A x y := by
  constructor
  · intro hess
    obtain ⟨εbar, hεbar, hεbar1, hunif⟩ := (isESS_iff_uniform A hx).1 hess
    -- a lower bound on the positive coordinates of `x`
    have hne : (univ : Finset (Fin n)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have := hx.2; rw [h, sum_empty] at this; norm_num at this
    obtain ⟨k, -, hk⟩ := exists_min_image univ (fun i => if 0 < x i then x i else 1) hne
    set μ := if 0 < x k then x k else 1
    have hμ : 0 < μ := by simp only [μ]; split_ifs with h <;> linarith
    have hμle : ∀ i, 0 < x i → μ ≤ x i := fun i hi => by
      have := hk i (mem_univ i); simp only [hi, ite_true] at this; exact this
    refine ⟨εbar * μ, mul_pos hεbar hμ, fun y hy hyx hclose => ?_⟩
    obtain ⟨z, hz, i0, hxi0, hzi0, l, hl, hl1, rfl, hli⟩ := exists_ray hx hy hyx
    have hzx : z ≠ x := fun h => by rw [h] at hzi0; linarith
    have hll : l < εbar := by
      have h1 := hclose i0
      have h2 := hμle i0 hxi0
      have h3 : l * x i0 < εbar * x i0 := by
        rw [hli]
        have := le_abs_self (x i0 - post x z l i0)
        have := abs_sub_comm (post x z l i0) (x i0)
        nlinarith
      exact lt_of_mul_lt_mul_right h3 hxi0.le
    have h := hunif z hz hzx l hl hll
    -- `E(x,y) − E(y,y) = l (E(x,y) − E(z,y))`
    have e : E A (post x z l) (post x z l) =
        (1 - l) * E A x (post x z l) + l * E A z (post x z l) := E_mix_left A x z _ _ _
    rw [e]
    nlinarith
  · rintro ⟨δ, hδ, h⟩
    refine (isESS_iff_invasion A hx).2 fun y hy hyx => ⟨min δ 1, lt_min hδ one_pos,
      fun ε hε hεb => ?_⟩
    have hε1 : ε < 1 := lt_of_lt_of_le hεb (min_le_right _ _)
    have hεδ : ε < δ := lt_of_lt_of_le hεb (min_le_left _ _)
    have hw := post_mem hx hy hε.le hε1.le
    have hwx : post x y ε ≠ x := by
      intro hw'
      apply hyx
      funext i
      have := congrFun hw' i
      simp only [post] at this
      have : ε * (y i - x i) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · linarith
    have hclose : ∀ i, |post x y ε i - x i| < δ := fun i => by
      have e : post x y ε i - x i = ε * (y i - x i) := by simp only [post]; ring
      rw [e, abs_mul, abs_of_pos hε]
      have : |y i - x i| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hy.1 i, hx.1 i, lotteries_le_one hy i, lotteries_le_one hx i]
      nlinarith [abs_nonneg (y i - x i)]
    have hsup := h _ hw hwx hclose
    have e : E A (post x y ε) (post x y ε) =
        (1 - ε) * E A x (post x y ε) + ε * E A y (post x y ε) := E_mix_left A x y _ _ _
    rw [e] at hsup
    have : ε * E A y (post x y ε) < ε * E A x (post x y ε) := by nlinarith
    exact lt_of_mul_lt_mul_left this hε.le

/-- Non-vacuity: the Hawk–Dove ESS has a uniform invasion barrier and is
locally superior. -/
theorem hawkDove_uniform_locallySuperior {V C : ℝ} (hV : 0 < V) (hVC : V < C) :
    (∃ εbar > 0, εbar ≤ 1 ∧ ∀ y ∈ lotteries (Fin 2), y ≠ hdMix (V / C) → ∀ ε, 0 < ε →
      ε < εbar → E (hawkDove V C) y (post (hdMix (V / C)) y ε) <
        E (hawkDove V C) (hdMix (V / C)) (post (hdMix (V / C)) y ε)) ∧
    ∃ δ > 0, ∀ y ∈ lotteries (Fin 2), y ≠ hdMix (V / C) → (∀ i, |y i - hdMix (V / C) i| < δ) →
      E (hawkDove V C) y y < E (hawkDove V C) (hdMix (V / C)) y := by
  have h := hawkDove_isESS hV hVC
  exact ⟨(isESS_iff_uniform _ h.1).1 h, (isESS_iff_locallySuperior _ h.1).1 h⟩

end ESS

end Econ
