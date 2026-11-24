/-
# Utility without wealth effects is CARA or linear

References. M. Rabin and G. Weizsäcker (2009), "Narrow Bracketing and
Dominated Choices", *AER* 99(4) (Proposition 1: dominated narrow choices iff
utility is not CARA); M. Nagumo (1930), B. de Finetti (1931) and B. Jessen
(1931) on translation-invariant quasi-arithmetic means; J. Aczél (1966),
*Lectures on Functional Equations*.

This file completes `RabinWeizsacker.lean` for the fair coin.

**Results.**
* `ti_of_not_wealthEffect`: if a continuous strictly increasing `u` has no
  wealth effect for fair coins, its 50–50 certainty equivalents are
  translation invariant (`TI`): if `u z` is the average of `u x` and `u y`,
  then `u (z + w)` is the average of `u (x + w)` and `u (y + w)`.
* `affine_shift_of_ti` (Nagumo–de Finetti–Jessen): then every shift of `u` is
  a positive affine transform of `u`: `u (x + w) = α u x + β`. The proof
  shows this on dyadic points of each interval by midpoints and extends it by
  monotonicity.
* `isCARAorLinear_of_affine_shift` (a Pexider/Vincze-type equation, Aczél
  1966 §3.1): a continuous strictly increasing `u` all of whose shifts are
  affine transforms of it (positivity of the slope is not needed here) is
  linear, `a x + b` with `a > 0`, or exponential, `c + d e^{kx}` with
  `dk > 0` (`IsCARAorLinear`).
* `isCARAorLinear_of_ti`: the composition, translation-invariant 50–50
  certainty equivalents force CARA or linear utility (Nagumo–de
  Finetti–Jessen for the 50–50 mean).
* `rabinWeizsacker` (**Rabin–Weizsäcker Proposition 1 for fair coins**): a
  continuous strictly increasing `u` satisfies `NarrowDominated u coin` iff
  `u` is neither linear nor exponential (CARA). `NarrowDominated` is the class
  of decision pairs used in Rabin–Weizsäcker's construction: each decision is
  a coin-flip lottery against a sure amount, the second lottery is the first
  shifted by a constant, and the narrow choices are strict. So "⇐" exhibits a
  dominated choice inside this class, while "⇒" shows CARA and linear agents
  avoid dominated choices only within this class, not for arbitrary pairs of
  decisions. Continuity of `u` is an extra assumption relative to the paper,
  which assumes only increasing utility. Supporting
  lemmas: `additive_linear` (continuous additive maps are linear),
  `narrowDominated_affine` (dominance survives positive affine transforms of
  utility), `not_narrowDominated_of_isCARAorLinear`.
* Non-vacuity: `kink_not_isCARAorLinear` (the kinked utility of
  `RabinWeizsacker.lean` is neither linear nor CARA), and
  `cara_isCARAorLinear`, `id_isCARAorLinear` for the other side.

`IsCARAorLinear` writes the exponential case as `c + d e^{kx}` with `dk > 0`,
which covers both risk-averse (`k < 0`, `d < 0`) and risk-loving (`k > 0`,
`d > 0`) CARA. Only the fair coin is treated; other probability vectors would
need the corresponding weighted-mean version of `TI`.
-/
module

public import EconLean.Behavioral.RabinWeizsacker
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

noncomputable section

namespace Econ

namespace Bracketing

open Finset Filter Topology Set

/-- Translation invariance of 50–50 certainty equivalents. -/
def TI (u : ℝ → ℝ) : Prop :=
  ∀ x y z w : ℝ, u z = (u x + u y) / 2 → u (z + w) = (u (x + w) + u (y + w)) / 2

/-- `u` is linear (`a x + b`, `a > 0`) or exponential (`c + d e^{kx}`,
`dk > 0`, i.e. CARA, risk averse for `k < 0` and risk loving for `k > 0`).
Strict monotonicity is built in. -/
def IsCARAorLinear (u : ℝ → ℝ) : Prop :=
  (∃ a > 0, ∃ b, ∀ x, u x = a * x + b) ∨
    ∃ c d k : ℝ, 0 < d * k ∧ ∀ x, u x = c + d * Real.exp (k * x)

theorem EU_coin (u : ℝ → ℝ) (z : Fin 2 → ℝ) : EU u coin z = (u (z 0) + u (z 1)) / 2 := by
  simp [EU, coin, Fin.sum_univ_two]; ring

/-! ### No wealth effect ⇒ translation invariance -/

theorem ti_of_not_wealthEffect {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u)
    (h : ¬ WealthEffect u coin) : TI u := by
  intro x y z w hz
  by_contra hne
  apply h
  have hZ : EU u coin ![x, y] = u z := by rw [EU_coin]; simp [hz]
  have hZw : EU u coin (fun i => ![x, y] i + w) = (u (x + w) + u (y + w)) / 2 := by
    rw [EU_coin]; simp
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- raise the sure amount a little
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), u (z + δ + w) < (u (x + w) + u (y + w)) / 2 := by
      have hc' : Continuous fun δ => u (z + δ + w) := by fun_prop
      have := hc'.tendsto 0
      simp only [add_zero] at this
      exact this.eventually (gt_mem_nhds hlt)
    obtain ⟨δ, hδ, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ ∧ δ ∈ Set.Ioi 0).exists
    refine ⟨![x, y], z + δ, w, Or.inr ⟨?_, ?_⟩⟩
    · rw [hZ]; exact hu (by linarith [show (0 : ℝ) < δ from hδ0])
    · rw [hZw]; exact hδ
  · -- lower the sure amount a little
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), (u (x + w) + u (y + w)) / 2 < u (z - δ + w) := by
      have hc' : Continuous fun δ => u (z - δ + w) := by fun_prop
      have := hc'.tendsto 0
      simp only [sub_zero] at this
      exact this.eventually (lt_mem_nhds hgt)
    obtain ⟨δ, hδ, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ ∧ δ ∈ Set.Ioi 0).exists
    refine ⟨![x, y], z - δ, w, Or.inl ⟨?_, ?_⟩⟩
    · rw [hZ]; exact hu (by linarith [show (0 : ℝ) < δ from hδ0])
    · rw [hZw]; exact hδ

/-! ### Translation invariance ⇒ shifts are affine transforms -/

/-- On an interval `[a, b]`, a shift of `u` agrees with the affine transform
of `u` matching it at the endpoints. -/
theorem affine_on_Icc {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u) (hti : TI u)
    (w : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ x ∈ Icc a b, u (x + w) = (u (b + w) - u (a + w)) / (u b - u a) * u x +
      (u (a + w) - (u (b + w) - u (a + w)) / (u b - u a) * u a) := by
  set D := u b - u a
  have hD : 0 < D := sub_pos.2 (hu hab)
  set α := (u (b + w) - u (a + w)) / D
  set β := u (a + w) - α * u a
  have hα : 0 < α := div_pos (sub_pos.2 (hu (by linarith))) hD
  -- dyadic points
  set P : ℕ → ℕ → ℝ := fun n k => u a + (k : ℝ) / 2 ^ n * D
  have hrange : ∀ n k, k ≤ 2 ^ n → ∃ z ∈ Icc a b, u z = P n k := by
    intro n k hk
    have hk' : (k : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hk
    have hk0 : 0 ≤ (k : ℝ) / 2 ^ n := by positivity
    have hmem : P n k ∈ Icc (u a) (u b) := by
      constructor
      · simp only [P]; nlinarith
      · simp only [P]; nlinarith
    obtain ⟨z, hz, hze⟩ := intermediate_value_Icc hab.le hc.continuousOn hmem
    exact ⟨z, hz, hze⟩
  have hdy : ∀ n k, k ≤ 2 ^ n → ∀ z, u z = P n k → u (z + w) = α * u z + β := by
    intro n
    induction n with
    | zero =>
      intro k hk z hz
      rw [pow_zero] at hk
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
      · have : z = a := hu.injective (by rw [hz]; simp [P])
        subst this; simp only [β]; ring
      · have : z = b := hu.injective (by rw [hz]; simp [P, D])
        subst this; simp only [β, α]; field_simp; ring
    | succ n ih =>
      intro k hk z hz
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · refine ih j (by rw [pow_succ] at hk; omega) z ?_
        rw [hz]; simp only [P]; push_cast; rw [pow_succ]; field_simp
      · have hj : j + 1 ≤ 2 ^ n := by rw [pow_succ] at hk; omega
        obtain ⟨z1, -, h1⟩ := hrange n j (by omega)
        obtain ⟨z2, -, h2⟩ := hrange n (j + 1) hj
        have hmid : u z = (u z1 + u z2) / 2 := by
          rw [hz, h1, h2]; simp only [P]; push_cast; rw [pow_succ]; field_simp; ring
        rw [hti z1 z2 z w hmid, ih j (by omega) z1 h1, ih (j + 1) hj z2 h2, hmid]
        ring
  -- squeeze between dyadic points
  intro x hx
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · subst hxb
    exact hdy 0 1 (by simp) x (by simp [P, D])
  set t := (u x - u a) / D
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 (hu.monotone hx.1)) hD.le
  have ht1 : t < 1 := by rw [div_lt_one hD]; linarith [hu hxb]
  have hux : u x = u a + t * D := by simp only [t]; field_simp; ring
  set e := u (x + w) - (α * u x + β)
  have hbound : ∀ n : ℕ, |e| ≤ α * D / 2 ^ n := by
    intro n
    set k := ⌊t * 2 ^ n⌋₊
    have hk1 : (k : ℝ) ≤ t * 2 ^ n := Nat.floor_le (by positivity)
    have hk2 : t * 2 ^ n < k + 1 := Nat.lt_floor_add_one _
    have hkn : k + 1 ≤ 2 ^ n := by
      have : t * 2 ^ n < 2 ^ n := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
      have : (k : ℝ) < 2 ^ n := lt_of_le_of_lt hk1 this
      exact_mod_cast this
    obtain ⟨zL, -, hL⟩ := hrange n k (by omega)
    obtain ⟨zU, -, hU⟩ := hrange n (k + 1) hkn
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hLx : P n k ≤ u x := by
      simp only [P]; rw [hux]
      have : (k : ℝ) / 2 ^ n ≤ t := by rw [div_le_iff₀ h2n]; linarith
      nlinarith
    have hxU : u x ≤ P n (k + 1) := by
      simp only [P]; rw [hux]; push_cast
      have : t ≤ ((k : ℝ) + 1) / 2 ^ n := by rw [le_div_iff₀ h2n]; linarith
      nlinarith
    have hzL : zL ≤ x := hu.le_iff_le.1 (hL ▸ hLx)
    have hzU : x ≤ zU := hu.le_iff_le.1 (hU ▸ hxU)
    have e1 : u (zL + w) ≤ u (x + w) := hu.monotone (by linarith)
    have e2 : u (x + w) ≤ u (zU + w) := hu.monotone (by linarith)
    rw [hdy n k (by omega) zL hL] at e1
    rw [hdy n (k + 1) hkn zU hU] at e2
    have hgap : P n (k + 1) - P n k = D / 2 ^ n := by
      simp only [P]; push_cast; field_simp; ring
    rw [abs_le]
    constructor
    · have : α * (P n (k + 1) - u x) ≤ α * (D / 2 ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hα.le; linarith
      rw [hL] at e1
      simp only [e]
      have : α * D / 2 ^ n = α * (D / 2 ^ n) := by ring
      nlinarith
    · have : α * (u x - P n k) ≤ α * (D / 2 ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hα.le; linarith
      rw [hU] at e2
      simp only [e]
      have : α * D / 2 ^ n = α * (D / 2 ^ n) := by ring
      nlinarith
  by_contra hne
  have hepos : 0 < |e| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (α * D / |e|) (one_lt_two : (1 : ℝ) < 2)
  have := hbound n
  rw [div_lt_iff₀ hepos] at hn
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith

/-- **Nagumo–de Finetti–Jessen**: with translation-invariant 50–50 certainty
equivalents, every shift of `u` is a positive affine transform of `u`. -/
theorem affine_shift_of_ti {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u) (hti : TI u)
    (w : ℝ) : ∃ α β : ℝ, 0 < α ∧ ∀ x, u (x + w) = α * u x + β := by
  have coef : ∀ m : ℝ, 1 ≤ m → ∃ α β : ℝ, ∀ x ∈ Icc (-m) m, u (x + w) = α * u x + β :=
    fun m hm => ⟨_, _, affine_on_Icc hc hu hti w (by linarith)⟩
  obtain ⟨α, β, h1⟩ := coef 1 le_rfl
  have hne : u (-1) ≠ u 1 := (hu (by norm_num : (-1 : ℝ) < 1)).ne
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1) 1 := ⟨le_rfl, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Set.Icc (-1) 1 := ⟨by norm_num, le_rfl⟩
  refine ⟨α, β, ?_, fun x => ?_⟩
  · have e1 := h1 (-1) hm1
    have e2 := h1 1 hp1
    have hlt : u (-1 + w) < u (1 + w) := hu (by linarith)
    have hu1 : u (-1) < u 1 := hu (by norm_num)
    by_contra hα
    rw [not_lt] at hα
    nlinarith
  · obtain ⟨α', β', h2⟩ := coef (max 1 |x|) (le_max_left _ _)
    have hm1' : (-1 : ℝ) ∈ Icc (-max 1 |x|) (max 1 |x|) :=
      ⟨by linarith [le_max_left 1 |x|], by linarith [le_max_left 1 |x|]⟩
    have hp1' : (1 : ℝ) ∈ Icc (-max 1 |x|) (max 1 |x|) :=
      ⟨by linarith [le_max_left 1 |x|], le_max_left _ _⟩
    have hx' : x ∈ Icc (-max 1 |x|) (max 1 |x|) :=
      ⟨by linarith [neg_abs_le x, le_max_right 1 |x|], (le_abs_self x).trans (le_max_right _ _)⟩
    have a1 := h1 (-1) hm1
    have a2 := h1 1 hp1
    have b1 := h2 (-1) hm1'
    have b2 := h2 1 hp1'
    have hαα : α' = α := by
      have : (α' - α) * (u 1 - u (-1)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd (by linarith : u (-1) = u 1) hne
    have hββ : β' = β := by rw [hαα] at b1; linarith
    rw [h2 x hx', hαα, hββ]

/-- Additive continuous functions on `ℝ` are linear. -/
theorem additive_linear {f : ℝ → ℝ} (hf : Continuous f) (hadd : ∀ x y, f (x + y) = f x + f y) :
    ∀ x, f x = x * f 1 := by
  let F : ℝ →+ ℝ := { toFun := f, map_zero' := by
                        have := hadd 0 0; simp only [add_zero] at this; linarith,
                      map_add' := hadd }
  intro x
  have := map_real_smul F hf x 1
  simpa [F] using this

/-- **A Pexider-type equation**: if every shift of a continuous strictly
increasing `u` is an affine transform of `u`, then `u` is linear or
exponential. -/
theorem isCARAorLinear_of_affine_shift {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u)
    (h : ∀ w, ∃ α β : ℝ, ∀ x, u (x + w) = α * u x + β) : IsCARAorLinear u := by
  choose A B hAB using h
  set g : ℝ → ℝ := fun x => u x - u 0
  have hgc : Continuous g := by fun_prop
  have hB : ∀ w, B w = u w - A w * u 0 := fun w => by
    have := hAB w 0; rw [zero_add] at this; linarith
  have hg : ∀ x w, g (x + w) = A w * g x + g w := fun x w => by
    simp only [g]; rw [hAB w x, hB w]; ring
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : 0 < g 1 := by simp only [g]; exact sub_pos.2 (hu one_pos)
  by_cases hA : ∀ w, A w = 1
  · left
    have hadd : ∀ x y, g (x + y) = g x + g y := fun x y => by rw [hg, hA]; ring
    have hlin := additive_linear hgc hadd
    exact ⟨g 1, hg1, u 0, fun x => by have := hlin x; simp only [g] at this ⊢; linarith⟩
  · right
    push Not at hA
    obtain ⟨w0, hw0⟩ := hA
    have hw0' : A w0 - 1 ≠ 0 := sub_ne_zero.2 hw0
    set κ := g w0 / (A w0 - 1)
    -- `g x = κ (A x − 1)`
    have hsym : ∀ x, g x * (A w0 - 1) = g w0 * (A x - 1) := fun x => by
      have h1 := hg x w0
      have h2 := hg w0 x
      rw [add_comm] at h2
      linarith
    have hgk : ∀ x, g x = κ * (A x - 1) := fun x => by
      simp only [κ]; field_simp; linarith [hsym x]
    have hκ : κ ≠ 0 := fun h0 => by
      have := hgk 1; rw [h0, zero_mul] at this; linarith
    have hAx : ∀ x, A x = 1 + g x / κ := fun x => by rw [hgk x]; field_simp; ring
    have hAc : Continuous A := by
      have : A = fun x => 1 + g x / κ := funext hAx
      rw [this]; fun_prop
    have hmul : ∀ x w, A (x + w) = A x * A w := fun x w => by
      have := hg x w
      rw [hgk, hgk, hgk] at this
      have : κ * (A (x + w) - (A x * A w)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hκ
      · linarith
    have hA0 : A 0 = 1 := by rw [hAx, hg0]; simp
    have hApos : ∀ x, 0 < A x := fun x => by
      have hsq : A x = A (x / 2) * A (x / 2) := by rw [← hmul]; ring_nf
      have hne : A x ≠ 0 := fun h0 => by
        have := hmul x (-x)
        rw [add_neg_cancel, hA0, h0, zero_mul] at this
        exact one_ne_zero this
      rcases lt_or_gt_of_ne hne with h | h
      · nlinarith [mul_self_nonneg (A (x / 2))]
      · exact h
    set L : ℝ → ℝ := fun x => Real.log (A x)
    have hLc : Continuous L := hAc.log fun x => (hApos x).ne'
    have hLadd : ∀ x y, L (x + y) = L x + L y := fun x y => by
      simp only [L]; rw [hmul, Real.log_mul (hApos x).ne' (hApos y).ne']
    have hLlin := additive_linear hLc hLadd
    set k := L 1
    have hAexp : ∀ x, A x = Real.exp (k * x) := fun x => by
      rw [← Real.exp_log (hApos x)]
      show Real.exp (L x) = _
      rw [hLlin x, mul_comm]
    have hu' : ∀ x, u x = (u 0 - κ) + κ * Real.exp (k * x) := fun x => by
      have := hgk x; simp only [g] at this; rw [hAexp] at this; linarith
    refine ⟨u 0 - κ, κ, k, ?_, hu'⟩
    have h1 : u 0 < u 1 := hu one_pos
    rw [hu' 0, hu' 1, mul_zero, Real.exp_zero, mul_one, mul_one] at h1
    have hk : k ≠ 0 := fun hk0 => by
      apply hw0; rw [hAexp, hk0, zero_mul, Real.exp_zero]
    rcases lt_or_gt_of_ne hk with hk | hk
    · have : Real.exp k < 1 := by simpa using Real.exp_lt_exp.2 hk
      have : κ < 0 := by nlinarith
      nlinarith
    · have : 1 < Real.exp k := by simpa using Real.exp_lt_exp.2 hk
      have : 0 < κ := by nlinarith
      nlinarith

/-- Translation-invariant 50–50 certainty equivalents force CARA or linear
utility. -/
theorem isCARAorLinear_of_ti {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u)
    (hti : TI u) : IsCARAorLinear u :=
  isCARAorLinear_of_affine_shift hc hu fun w => by
    obtain ⟨α, β, -, h⟩ := affine_shift_of_ti hc hu hti w
    exact ⟨α, β, h⟩

/-! ### Rabin–Weizsäcker for fair coins -/

/-- Narrow-bracketing dominance is invariant under positive affine transforms
of utility. -/
theorem narrowDominated_affine {v : ℝ → ℝ} {c d : ℝ} (hd : 0 < d) {n : ℕ} {p : Fin n → ℝ}
    (h : NarrowDominated (fun x => c + d * v x) p) : NarrowDominated v p := by
  obtain ⟨hp, z₁, s₁, s₂, c', δ, hδ, h⟩ := h
  have hEU : ∀ z : Fin n → ℝ, EU (fun x => c + d * v x) p z = c + d * EU v p z := fun z => by
    have hpc : ∑ i, p i * c = c := by rw [← sum_mul, hp.2, one_mul]
    simp only [EU, mul_add, sum_add_distrib, hpc, mul_sum]
    exact congrArg _ (sum_congr rfl fun i _ => by ring)
  refine ⟨hp, z₁, s₁, s₂, c', δ, hδ, ?_⟩
  simp only [hEU] at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨lt_of_mul_lt_mul_left (by linarith) hd.le,
      lt_of_mul_lt_mul_left (by linarith) hd.le, h3⟩
  · exact Or.inr ⟨lt_of_mul_lt_mul_left (by linarith) hd.le,
      lt_of_mul_lt_mul_left (by linarith) hd.le, h3⟩

theorem not_narrowDominated_of_isCARAorLinear {u : ℝ → ℝ} (h : IsCARAorLinear u) :
    ¬ NarrowDominated u coin := by
  rcases h with ⟨a, ha, b, hu⟩ | ⟨c, d, k, hdk, hu⟩
  · have : u = fun x => a * x + b := funext hu
    rw [this]; exact linear_not_narrowDominated ha coin_isProb
  · rcases lt_or_gt_of_ne (show k ≠ 0 by rintro rfl; simp at hdk) with hk | hk
    · -- risk averse: `u = c + (−d) · cara (−k)`
      have hd : 0 < -d := by nlinarith
      have : u = fun x => c + (-d) * cara (-k) x := by
        funext x; rw [hu x]; simp only [cara]; ring_nf
      rw [this]
      exact fun hnd => cara_not_narrowDominated (by linarith) coin (narrowDominated_affine hd hnd)
    · have hd : 0 < d := by nlinarith
      have : u = fun x => c + d * caraLove k x := by
        funext x; rw [hu x]; simp only [caraLove]
      rw [this]
      exact fun hnd => caraLove_not_narrowDominated hk coin (narrowDominated_affine hd hnd)

/-- **Rabin–Weizsäcker Proposition 1 (fair coins)**: a continuous strictly
increasing utility leads a narrow bracketer to a state-wise dominated
combined choice in some pair of coin-flip decisions iff it is neither
linear nor CARA. -/
theorem rabinWeizsacker {u : ℝ → ℝ} (hc : Continuous u) (hu : StrictMono u) :
    NarrowDominated u coin ↔ ¬ IsCARAorLinear u := by
  refine ⟨fun h hcl => not_narrowDominated_of_isCARAorLinear hcl h, fun hn => ?_⟩
  by_cases hw : WealthEffect u coin
  · exact narrowDominated_of_wealthEffect hc coin_isProb hw
  · exact absurd (isCARAorLinear_of_ti hc hu (ti_of_not_wealthEffect hc hu hw)) hn

/-- Non-vacuity: the kinked utility is neither linear nor CARA. -/
theorem kink_not_isCARAorLinear : ¬ IsCARAorLinear kink :=
  (rabinWeizsacker kink_continuous kink_strictMono).1 kink_narrowDominated

/-- Non-vacuity: risk-averse CARA utility satisfies `IsCARAorLinear`. -/
theorem cara_isCARAorLinear {α : ℝ} (hα : 0 < α) : IsCARAorLinear (cara α) :=
  Or.inr ⟨0, -1, -α, by nlinarith, fun x => by simp only [cara]; ring⟩

/-- Non-vacuity: the identity satisfies `IsCARAorLinear`. -/
theorem id_isCARAorLinear : IsCARAorLinear (fun x : ℝ => x) :=
  Or.inl ⟨1, one_pos, 0, fun x => by ring⟩

end Bracketing

end Econ
