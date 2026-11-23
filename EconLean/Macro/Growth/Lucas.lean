/-
# Lucas (1988): human capital, an externality, and too little growth

Lucas, "On the Mechanics of Economic Development", JME 1988, §4; Acemoglu,
*Introduction to Modern Economic Growth*, §11.4 and §13.2 on externalities;
Barro–Sala-i-Martin ch. 5.

**The model** (discrete time, human capital only). A worker with human capital
`h` spends a fraction `u ∈ (0, 1]` of time producing and the rest accumulating
skills:

    y_t = A u_t h_t h̄_t^γ,      h_{t+1} = (1 + B (1 − u_t)) h_t,

where `h̄` is average human capital in the economy and `γ ≥ 0` measures Lucas's
external effect of human capital. Output is consumed, and utility is
`Σ βᵗ log c_t`.

* **The planner** internalizes `h̄ = h`, so consumption is `A u h^{1+γ}`.
* **A private worker** takes the path `h̄` as given.

**Results.** Write `κ = w β/(1 − β)`, where `w` is the weight on `log h` in
the period payoff (`w = 1 + γ` for the planner, `w = 1` for a private worker).
The best constant time allocation is `u*(κ) = (1 + B)/(B (1 + κ))`.

* `isEquilibrium_iff`: the (symmetric) competitive equilibrium is the
  constant path `u_eq = (1 − β)(1 + B)/B`, the same as without the
  externality.
* `isEfficient_iff`: the efficient path is the constant
  `u_P = (1 + B)/(B (1 + (1 + γ) β/(1 − β)))`.
* `lucas`: with a positive externality (`γ > 0`), workers spend too much
  time producing and too little learning (`u_P < u_eq`), so **the
  equilibrium growth rate `B (1 − u_eq)` is strictly below the efficient
  one**.

Optimality compares paths whose lifetime utility converges (`HasSum`). This
is harmless: `log u ≤ 0` and `h` grows at most geometrically, so the positive
part always converges, and a path without a sum has utility `−∞`.

**The Lean.** Since `log h_t = log h₀ + Σ_{s<t} log(1 + B(1 − u_s))`, lifetime
utility separates into per-period terms
`βˢ (log u_s + κ log(1 + B(1 − u_s)))`, up to a horizon correction of order
`T βᵀ` (`core_finite`). Each term is maximized at `u*(κ)` by concavity of
`log`.

**Deviations.** No physical capital; log utility; discrete time; the
interior case `u* ≤ 1` (assumed via `1 − β ≤ β B`; when it fails the private
optimum is the corner `u = 1`, which is not covered).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

noncomputable section

namespace Econ
namespace Lucas

open Filter Topology Real Finset

/-- The environment. -/
structure Economy where
  /-- Productivity. -/
  A : ℝ
  /-- Productivity of time spent learning. -/
  B : ℝ
  /-- Strength of the human-capital externality. -/
  γ : ℝ
  /-- Discount factor. -/
  β : ℝ
  hA : 0 < A
  hB : 0 < B
  hγ : 0 ≤ γ
  hβ₀ : 0 < β
  hβ₁ : β < 1

/-- A time-allocation path is feasible if `u_t ∈ (0, 1]`. -/
def Feasible (u : ℕ → ℝ) : Prop := ∀ t, 0 < u t ∧ u t ≤ 1

namespace Economy

variable (E : Economy)

/-- Gross growth factor of human capital at time allocation `u`. -/
def growth (u : ℝ) : ℝ := 1 + E.B * (1 - u)

/-- Human capital along a path, from `h₀`. -/
def hpath (h₀ : ℝ) (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => h₀
  | t + 1 => E.growth (u t) * hpath h₀ u t

/-- The optimal constant time allocation for weight `κ`. -/
def uStar (κ : ℝ) : ℝ := (1 + E.B) / (E.B * (1 + κ))

/-- Planner's period utility: `log (A u h^{1+γ})`. -/
def planU (h₀ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ := log (E.A * u t * E.hpath h₀ u t ^ (1 + E.γ))

/-- A private worker's period utility given average human capital `h̄`:
`log (A u h h̄^γ)`. -/
def privU (h₀ : ℝ) (hbar : ℕ → ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  log (E.A * u t * E.hpath h₀ u t * hbar t ^ E.γ)

/-- `u` maximizes a private worker's lifetime utility, given `h̄`. -/
def IsPrivOptimal (h₀ : ℝ) (hbar u : ℕ → ℝ) : Prop :=
  Feasible u ∧ Summable (fun t => E.β ^ t * E.privU h₀ hbar u t) ∧
    ∀ u' W, Feasible u' → HasSum (fun t => E.β ^ t * E.privU h₀ hbar u' t) W →
      W ≤ ∑' t, E.β ^ t * E.privU h₀ hbar u t

/-- **Competitive equilibrium:** each worker's time allocation is privately
optimal given average human capital, which (by symmetry) is its own path. -/
def IsEquilibrium (h₀ : ℝ) (u : ℕ → ℝ) : Prop := E.IsPrivOptimal h₀ (E.hpath h₀ u) u

/-- **Efficiency:** `u` maximizes the planner's lifetime utility. -/
def IsEfficient (h₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  Feasible u ∧ Summable (fun t => E.β ^ t * E.planU h₀ u t) ∧
    ∀ u' W, Feasible u' → HasSum (fun t => E.β ^ t * E.planU h₀ u' t) W →
      W ≤ ∑' t, E.β ^ t * E.planU h₀ u t

/-! ### Basic facts -/

theorem growth_ge_one {u : ℝ} (hu : u ≤ 1) : 1 ≤ E.growth u := by
  have := E.hB; unfold growth; nlinarith

theorem growth_le {u : ℝ} (hu : 0 < u) : E.growth u ≤ 1 + E.B := by
  have := E.hB; unfold growth; nlinarith

theorem hpath_pos {h₀ : ℝ} (hh : 0 < h₀) {u : ℕ → ℝ} (hu : Feasible u) (t : ℕ) :
    0 < E.hpath h₀ u t := by
  induction t with
  | zero => exact hh
  | succ t ih => exact mul_pos (lt_of_lt_of_le one_pos (E.growth_ge_one (hu t).2)) ih

/-- `log h_t = log h₀ + Σ_{s<t} log(1 + B (1 − u_s))`. -/
theorem log_hpath {h₀ : ℝ} (hh : 0 < h₀) {u : ℕ → ℝ} (hu : Feasible u) (t : ℕ) :
    log (E.hpath h₀ u t) = log h₀ + ∑ s ∈ range t, log (E.growth (u s)) := by
  induction t with
  | zero => simp [hpath]
  | succ t ih =>
    rw [sum_range_succ, show E.hpath h₀ u (t + 1) = E.growth (u t) * E.hpath h₀ u t from rfl,
      log_mul (lt_of_lt_of_le one_pos (E.growth_ge_one (hu t).2)).ne' (E.hpath_pos hh hu t).ne', ih]
    ring

theorem log_growth_mem {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    0 ≤ log (E.growth u) ∧ log (E.growth u) ≤ log (1 + E.B) :=
  ⟨log_nonneg (E.growth_ge_one h1),
    log_le_log (lt_of_lt_of_le one_pos (E.growth_ge_one h1)) (E.growth_le h0)⟩

/-! ### The per-period problem -/

/-- Per-period objective `φ(u) = log u + κ log(1 + B(1 − u))`. -/
def phi (κ u : ℝ) : ℝ := log u + κ * log (E.growth u)

theorem uStar_pos {κ : ℝ} (hκ : 0 < κ) : 0 < E.uStar κ := by
  have := E.hB; unfold uStar; positivity

/-- `u*` maximizes `φ` on `(0, 1]`, strictly. -/
theorem phi_le {κ : ℝ} (hκ : 0 < κ) {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    E.phi κ u ≤ E.phi κ (E.uStar κ) ∧ (u ≠ E.uStar κ → E.phi κ u < E.phi κ (E.uStar κ)) := by
  have hB := E.hB
  set us := E.uStar κ
  have hus : 0 < us := E.uStar_pos hκ
  have hms : E.growth us = (1 + E.B) * κ / (1 + κ) := by
    simp only [growth, us, uStar]; field_simp; ring
  have hm : 0 < E.growth us := by rw [hms]; positivity
  have hmu : 0 < E.growth u := lt_of_lt_of_le one_pos (E.growth_ge_one h1)
  -- first-order condition: `1/u* = κ B / m*`
  have hfoc : (u - us) / us - κ * (E.B * (u - us) / E.growth us) = 0 := by
    rw [hms]; simp only [us, uStar]; field_simp; ring
  have hgr : E.growth u / E.growth us - 1 = -(E.B * (u - us) / E.growth us) := by
    rw [div_sub_one hm.ne', ← neg_div]; congr 1; simp only [growth]; ring
  have hlu : u / us - 1 = (u - us) / us := by field_simp
  have key : E.phi κ u - E.phi κ us =
      log (u / us) + κ * log (E.growth u / E.growth us) := by
    simp only [phi]; rw [log_div h0.ne' hus.ne', log_div hmu.ne' hm.ne']; ring
  constructor
  · have h1' := log_le_sub_one_of_pos (div_pos h0 hus)
    have h2' := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hmu hm)) hκ.le
    rw [hgr] at h2'; rw [hlu] at h1'
    linarith
  · intro hne
    have h1' := log_lt_sub_one_of_pos (div_pos h0 hus) (by
      intro h; apply hne; field_simp at h; linarith)
    have h2' := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hmu hm)) hκ.le
    rw [hgr] at h2'; rw [hlu] at h1'
    linarith

/-! ### Separating lifetime utility into per-period terms -/

/-- `Σ_{t<T} βᵗ Σ_{s<t} a_s = Σ_{s<T} a_s (β^{s+1} − β^T)/(1 − β)`. -/
theorem sum_geom_cumsum (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ range T, E.β ^ t * ∑ s ∈ range t, a s =
      ∑ s ∈ range T, a s * (E.β ^ (s + 1) - E.β ^ T) / (1 - E.β) := by
  have h1 : (1 - E.β) ≠ 0 := by linarith [E.hβ₁]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih, sum_range_succ, sub_self, mul_zero, zero_div, add_zero, mul_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    field_simp
    ring

/-- **Separation.** For weight `w` and `κ = w β/(1 − β)`:
`Σ_{t<T} βᵗ (log u_t + w log h_t) = w log h₀ Σ_{t<T} βᵗ + Σ_{s<T} βˢ φ(u_s)
 − (w β^T/(1 − β)) Σ_{s<T} log(1 + B(1 − u_s))`. -/
theorem separate {h₀ : ℝ} (hh : 0 < h₀) {u : ℕ → ℝ} (hu : Feasible u) (w : ℝ) (T : ℕ) :
    ∑ t ∈ range T, E.β ^ t * (log (u t) + w * log (E.hpath h₀ u t)) =
      w * log h₀ * ∑ t ∈ range T, E.β ^ t +
        ∑ s ∈ range T, E.β ^ s * E.phi (w * E.β / (1 - E.β)) (u s) -
        w * E.β ^ T / (1 - E.β) * ∑ s ∈ range T, log (E.growth (u s)) := by
  have h1 : (1 - E.β) ≠ 0 := by linarith [E.hβ₁]
  simp_rw [E.log_hpath hh hu]
  have hc := E.sum_geom_cumsum (fun s => log (E.growth (u s))) T
  have e1 : ∑ t ∈ range T, E.β ^ t * (log (u t) + w * (log h₀ + ∑ s ∈ range t, log (E.growth (u s)))) =
      ∑ t ∈ range T, E.β ^ t * log (u t) + w * log h₀ * ∑ t ∈ range T, E.β ^ t +
        w * ∑ t ∈ range T, E.β ^ t * ∑ s ∈ range t, log (E.growth (u s)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => by ring
  rw [e1, hc]
  have h2 : ∑ s ∈ range T, E.β ^ s * E.phi (w * E.β / (1 - E.β)) (u s) =
      ∑ s ∈ range T, E.β ^ s * log (u s) +
        ∑ s ∈ range T, E.β ^ s * (w * E.β / (1 - E.β)) * log (E.growth (u s)) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun s _ => ?_; simp only [phi]; ring
  have h3 : w * ∑ s ∈ range T, log (E.growth (u s)) * (E.β ^ (s + 1) - E.β ^ T) / (1 - E.β) =
      ∑ s ∈ range T, E.β ^ s * (w * E.β / (1 - E.β)) * log (E.growth (u s)) -
        w * E.β ^ T / (1 - E.β) * ∑ s ∈ range T, log (E.growth (u s)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    field_simp
    ring
  linarith

/-- **Finite-horizon comparison** with the constant path `u*`. For `w > 0`
and `κ = wβ/(1 − β)`, any feasible path satisfies, for every `T`,
`Σ_{t<T} βᵗ (log u_t + w log h_t) ≤ Σ_{t<T} βᵗ (log u* + w log h*_t)
 + Σ_{s<T} βˢ (φ(u_s) − φ(u*)) + w T β^T log(1 + B)/(1 − β)`. -/
theorem core_finite {h₀ : ℝ} (hh : 0 < h₀) {w : ℝ} (hw : 0 < w)
    (hus : E.uStar (w * E.β / (1 - E.β)) ≤ 1) {u : ℕ → ℝ} (hu : Feasible u) (T : ℕ) :
    ∑ t ∈ range T, E.β ^ t * (log (u t) + w * log (E.hpath h₀ u t)) ≤
      ∑ t ∈ range T, E.β ^ t * (log (E.uStar (w * E.β / (1 - E.β))) +
          w * log (E.hpath h₀ (fun _ => E.uStar (w * E.β / (1 - E.β))) t)) +
        ∑ s ∈ range T, E.β ^ s * (E.phi (w * E.β / (1 - E.β)) (u s) -
          E.phi (w * E.β / (1 - E.β)) (E.uStar (w * E.β / (1 - E.β)))) +
        w * T * E.β ^ T * log (1 + E.B) / (1 - E.β) := by
  have h1β : 0 < 1 - E.β := by linarith [E.hβ₁]
  have hκ : 0 < w * E.β / (1 - E.β) := by have := E.hβ₀; positivity
  have hsf : Feasible fun _ => E.uStar (w * E.β / (1 - E.β)) := fun _ => ⟨E.uStar_pos hκ, hus⟩
  rw [E.separate hh hu w T, E.separate hh hsf w T]
  set κ := w * E.β / (1 - E.β)
  have ha : ∑ s ∈ range T, log (E.growth (u s)) ≥ 0 :=
    sum_nonneg fun s _ => (E.log_growth_mem (hu s).1 (hu s).2).1
  have hb : ∑ s ∈ range T, log (E.growth (E.uStar κ)) ≤ T * log (1 + E.B) := by
    rw [sum_const, card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (E.log_growth_mem (E.uStar_pos hκ) hus).2 (Nat.cast_nonneg _)
  have hwβ : 0 ≤ w * E.β ^ T / (1 - E.β) := by have := E.hβ₀; positivity
  have h3 := mul_le_mul_of_nonneg_left ha hwβ
  have h4 := mul_le_mul_of_nonneg_left hb hwβ
  have hsplit : ∑ s ∈ range T, E.β ^ s * (E.phi κ (u s) - E.phi κ (E.uStar κ)) =
      ∑ s ∈ range T, E.β ^ s * E.phi κ (u s) - ∑ s ∈ range T, E.β ^ s * E.phi κ (E.uStar κ) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
  rw [hsplit]
  have e : w * E.β ^ T / (1 - E.β) * (T * log (1 + E.B)) =
      w * T * E.β ^ T * log (1 + E.B) / (1 - E.β) := by ring
  linarith

/-- The horizon correction vanishes. -/
theorem tendsto_correction (w : ℝ) :
    Tendsto (fun T : ℕ => w * T * E.β ^ T * log (1 + E.B) / (1 - E.β)) atTop (𝓝 0) := by
  have hn : ‖E.β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos E.hβ₀]; exact E.hβ₁
  have h := tendsto_self_mul_const_pow_of_abs_lt_one (by rwa [Real.norm_eq_abs] at hn)
  have := ((h.const_mul w).mul_const (log (1 + E.B))).div_const (1 - E.β)
  simpa [mul_assoc] using this

/-- Lifetime `Σ βᵗ log h_t` converges along any feasible path. -/
theorem summable_log_hpath {h₀ : ℝ} (hh : 0 < h₀) {u : ℕ → ℝ} (hu : Feasible u) :
    Summable fun t => E.β ^ t * log (E.hpath h₀ u t) := by
  have hn : ‖E.β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos E.hβ₀]; exact E.hβ₁
  refine Summable.of_norm_bounded (((summable_geometric_of_lt_one E.hβ₀.le E.hβ₁).mul_left
    |log h₀|).add ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left (log (1 + E.B))))
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos E.hβ₀ t), E.log_hpath hh hu]
  have hs0 : 0 ≤ ∑ s ∈ range t, log (E.growth (u s)) :=
    sum_nonneg fun s _ => (E.log_growth_mem (hu s).1 (hu s).2).1
  have hs1 : ∑ s ∈ range t, log (E.growth (u s)) ≤ t * log (1 + E.B) := by
    calc _ ≤ ∑ s ∈ range t, log (1 + E.B) := sum_le_sum fun s _ => (E.log_growth_mem (hu s).1 (hu s).2).2
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have : |log h₀ + ∑ s ∈ range t, log (E.growth (u s))| ≤ |log h₀| + t * log (1 + E.B) := by
    calc _ ≤ |log h₀| + |∑ s ∈ range t, log (E.growth (u s))| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hs0]; linarith
  have hb := pow_pos E.hβ₀ t
  simp only [pow_one]
  nlinarith

/-- **Infinite-horizon comparison.** Let `e` be any summable sequence (payoff
terms the worker does not control). If a feasible path's lifetime utility
`Σ (e_t + βᵗ (log u_t + w log h_t))` converges to `W`, then
`W ≤ W* + βˢ (φ(u_s) − φ(u*))` for every `s`, where `W*` is lifetime utility
under the constant path `u*`. -/
theorem core_limit {h₀ : ℝ} (hh : 0 < h₀) {w : ℝ} (hw : 0 < w)
    (hus : E.uStar (w * E.β / (1 - E.β)) ≤ 1) {e : ℕ → ℝ} (he : Summable e)
    {u : ℕ → ℝ} (hu : Feasible u) {W : ℝ}
    (hW : HasSum (fun t => e t + E.β ^ t * (log (u t) + w * log (E.hpath h₀ u t))) W) (s : ℕ) :
    Summable (fun t => e t + E.β ^ t * (log (E.uStar (w * E.β / (1 - E.β))) +
        w * log (E.hpath h₀ (fun _ => E.uStar (w * E.β / (1 - E.β))) t))) ∧
    W ≤ ∑' t, (e t + E.β ^ t * (log (E.uStar (w * E.β / (1 - E.β))) +
        w * log (E.hpath h₀ (fun _ => E.uStar (w * E.β / (1 - E.β))) t))) +
      E.β ^ s * (E.phi (w * E.β / (1 - E.β)) (u s) -
        E.phi (w * E.β / (1 - E.β)) (E.uStar (w * E.β / (1 - E.β)))) := by
  set κ := w * E.β / (1 - E.β)
  have h1β : 0 < 1 - E.β := by linarith [E.hβ₁]
  have hκ : 0 < κ := by have := E.hβ₀; positivity
  have hsf : Feasible fun _ => E.uStar κ := fun _ => ⟨E.uStar_pos hκ, hus⟩
  have hsum : Summable (fun t => e t + E.β ^ t * (log (E.uStar κ) +
      w * log (E.hpath h₀ (fun _ => E.uStar κ) t))) := by
    refine he.add ?_
    simp_rw [mul_add]
    exact ((summable_geometric_of_lt_one E.hβ₀.le E.hβ₁).mul_right _).add
      (by simp_rw [mul_left_comm _ w]; exact (E.summable_log_hpath hh hsf).mul_left w)
  refine ⟨hsum, ?_⟩
  have hlim := (hsum.hasSum.tendsto_sum_nat.add (E.tendsto_correction w)).add_const
    (E.β ^ s * (E.phi κ (u s) - E.phi κ (E.uStar κ)))
  rw [add_zero] at hlim
  refine le_of_tendsto_of_tendsto hW.tendsto_sum_nat hlim ?_
  filter_upwards [eventually_gt_atTop s] with T hT
  have hc := E.core_finite hh hw hus hu T
  have hphi : ∑ s' ∈ range T, E.β ^ s' * (E.phi κ (u s') - E.phi κ (E.uStar κ)) ≤
      E.β ^ s * (E.phi κ (u s) - E.phi κ (E.uStar κ)) := by
    rw [← add_sum_erase _ _ (mem_range.2 hT)]
    have : ∑ x ∈ (range T).erase s, E.β ^ x * (E.phi κ (u x) - E.phi κ (E.uStar κ)) ≤ 0 :=
      sum_nonpos fun x _ => mul_nonpos_of_nonneg_of_nonpos (pow_pos E.hβ₀ x).le
        (sub_nonpos.2 (E.phi_le hκ (hu x).1 (hu x).2).1)
    linarith
  simp only [sum_add_distrib]
  linarith

/-! ### Equilibrium and efficiency -/

theorem privU_eq {h₀ : ℝ} (hh : 0 < h₀) {hbar : ℕ → ℝ} (hpos : ∀ t, 0 < hbar t)
    {u : ℕ → ℝ} (hu : Feasible u) (t : ℕ) :
    E.β ^ t * E.privU h₀ hbar u t =
      E.β ^ t * (log E.A + E.γ * log (hbar t)) +
        E.β ^ t * (log (u t) + 1 * log (E.hpath h₀ u t)) := by
  have := E.hA; have := (hu t).1; have := E.hpath_pos hh hu t; have := hpos t
  simp only [privU]
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_rpow (hpos t)]
  ring

theorem planU_eq {h₀ : ℝ} (hh : 0 < h₀) {u : ℕ → ℝ} (hu : Feasible u) (t : ℕ) :
    E.β ^ t * E.planU h₀ u t =
      E.β ^ t * log E.A + E.β ^ t * (log (u t) + (1 + E.γ) * log (E.hpath h₀ u t)) := by
  have := E.hA; have := (hu t).1; have := E.hpath_pos hh hu t
  simp only [planU]
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_rpow (E.hpath_pos hh hu t)]
  ring

/-- The equilibrium allocation `u_eq = (1 − β)(1 + B)/B`. -/
theorem uStar_priv : E.uStar (1 * E.β / (1 - E.β)) = (1 - E.β) * (1 + E.B) / E.B := by
  have h1 : (1 - E.β) ≠ 0 := by linarith [E.hβ₁]
  have := E.hB
  simp only [uStar]; field_simp; ring

/-- **Private optimality.** Whatever the path of average human capital
`h̄ > 0` (with `Σ βᵗ log h̄_t` convergent), the constant allocation
`u_eq = (1 − β)(1 + B)/B` is privately optimal, and any feasible path that
differs from it in some period is strictly worse. -/
theorem privOptimal {h₀ : ℝ} (hh : 0 < h₀) (hint : 1 - E.β ≤ E.β * E.B) {hbar : ℕ → ℝ}
    (hpos : ∀ t, 0 < hbar t) (hsum : Summable fun t => E.β ^ t * log (hbar t)) :
    E.IsPrivOptimal h₀ hbar (fun _ => E.uStar (1 * E.β / (1 - E.β))) ∧
    ∀ u W, Feasible u → HasSum (fun t => E.β ^ t * E.privU h₀ hbar u t) W →
      (∃ s, u s ≠ E.uStar (1 * E.β / (1 - E.β))) →
      W < ∑' t, E.β ^ t * E.privU h₀ hbar (fun _ => E.uStar (1 * E.β / (1 - E.β))) t := by
  have h1β : 0 < 1 - E.β := by linarith [E.hβ₁]
  have hκ : 0 < 1 * E.β / (1 - E.β) := by have := E.hβ₀; positivity
  have hus : E.uStar (1 * E.β / (1 - E.β)) ≤ 1 := by
    rw [uStar_priv, div_le_one E.hB]; nlinarith [E.hB]
  have hsf : Feasible fun _ => E.uStar (1 * E.β / (1 - E.β)) :=
    fun _ => ⟨E.uStar_pos hκ, hus⟩
  set e : ℕ → ℝ := fun t => E.β ^ t * (log E.A + E.γ * log (hbar t))
  have he : Summable e := by
    simp only [e, mul_add]
    exact ((summable_geometric_of_lt_one E.hβ₀.le E.hβ₁).mul_right _).add
      (by simp_rw [mul_left_comm _ E.γ]; exact hsum.mul_left _)
  have key : ∀ u W, Feasible u → HasSum (fun t => E.β ^ t * E.privU h₀ hbar u t) W → ∀ s,
      W ≤ ∑' t, E.β ^ t * E.privU h₀ hbar (fun _ => E.uStar (1 * E.β / (1 - E.β))) t +
        E.β ^ s * (E.phi (1 * E.β / (1 - E.β)) (u s) -
          E.phi (1 * E.β / (1 - E.β)) (E.uStar (1 * E.β / (1 - E.β)))) := by
    intro u W hu hW s
    have hW' : HasSum (fun t => e t + E.β ^ t * (log (u t) + 1 * log (E.hpath h₀ u t))) W := by
      convert hW using 1; funext t; rw [E.privU_eq hh hpos hu t]
    have := (E.core_limit hh one_pos hus he hu hW' s).2
    have e2 : (fun t => e t + E.β ^ t * (log (E.uStar (1 * E.β / (1 - E.β))) +
        1 * log (E.hpath h₀ (fun _ => E.uStar (1 * E.β / (1 - E.β))) t))) =
        fun t => E.β ^ t * E.privU h₀ hbar (fun _ => E.uStar (1 * E.β / (1 - E.β))) t := by
      funext t; rw [E.privU_eq hh hpos hsf t]
    rwa [e2] at this
  have hsumStar : Summable fun t =>
      E.β ^ t * E.privU h₀ hbar (fun _ => E.uStar (1 * E.β / (1 - E.β))) t := by
    have := (E.core_limit (W := ∑' t, (e t + E.β ^ t * (log (E.uStar (1 * E.β / (1 - E.β))) +
      1 * log (E.hpath h₀ (fun _ => E.uStar (1 * E.β / (1 - E.β))) t)))) hh one_pos hus he hsf
      ?_ 0).1
    · convert this using 1; funext t; rw [E.privU_eq hh hpos hsf t]
    · refine Summable.hasSum ?_
      refine he.add ?_
      simp_rw [mul_add]
      exact ((summable_geometric_of_lt_one E.hβ₀.le E.hβ₁).mul_right _).add
        (by simp_rw [mul_left_comm _ (1 : ℝ)]; exact (E.summable_log_hpath hh hsf).mul_left 1)
  refine ⟨⟨hsf, hsumStar, fun u W hu hW => ?_⟩, fun u W hu hW ⟨s, hs⟩ => ?_⟩
  · have := key u W hu hW 0
    have := mul_nonpos_of_nonneg_of_nonpos (pow_pos E.hβ₀ 0).le
      (sub_nonpos.2 (E.phi_le hκ (hu 0).1 (hu 0).2).1)
    linarith
  · have := key u W hu hW s
    have := mul_neg_of_pos_of_neg (pow_pos E.hβ₀ s)
      (sub_neg.2 ((E.phi_le hκ (hu s).1 (hu s).2).2 hs))
    linarith

/-- **The competitive equilibrium** is the constant path
`u_eq = (1 − β)(1 + B)/B`. -/
theorem isEquilibrium_iff {h₀ : ℝ} (hh : 0 < h₀) (hint : 1 - E.β ≤ E.β * E.B) (u : ℕ → ℝ) :
    E.IsEquilibrium h₀ u ↔ u = fun _ => (1 - E.β) * (1 + E.B) / E.B := by
  rw [← E.uStar_priv]
  have h1β : 0 < 1 - E.β := by linarith [E.hβ₁]
  have hκ : 0 < 1 * E.β / (1 - E.β) := by have := E.hβ₀; positivity
  constructor
  · rintro ⟨hu, hsu, hopt⟩
    by_contra hne
    obtain ⟨s, hs⟩ : ∃ s, u s ≠ E.uStar (1 * E.β / (1 - E.β)) := by
      by_contra h; push Not at h; exact hne (funext h)
    have hpos := E.hpath_pos hh hu
    have hsum := E.summable_log_hpath hh hu
    obtain ⟨h1, h2⟩ := E.privOptimal hh hint hpos hsum
    have := h2 u _ hu hsu.hasSum ⟨s, hs⟩
    have := hopt _ _ h1.1 h1.2.1.hasSum
    linarith
  · rintro rfl
    have hus := (E.privOptimal hh hint (fun t => E.hpath_pos hh (fun _ => ⟨E.uStar_pos hκ, by
      rw [uStar_priv, div_le_one E.hB]; nlinarith [E.hB]⟩) t) (E.summable_log_hpath hh
      (fun _ => ⟨E.uStar_pos hκ, by rw [uStar_priv, div_le_one E.hB]; nlinarith [E.hB]⟩))).1
    exact hus

/-- **The efficient allocation** is the constant path `u_P = u*((1 + γ)β/(1 − β))`. -/
theorem isEfficient_iff {h₀ : ℝ} (hh : 0 < h₀) (hint : 1 - E.β ≤ E.β * E.B) (u : ℕ → ℝ) :
    E.IsEfficient h₀ u ↔ u = fun _ => E.uStar ((1 + E.γ) * E.β / (1 - E.β)) := by
  have h1β : 0 < 1 - E.β := by linarith [E.hβ₁]
  have hw : 0 < 1 + E.γ := by linarith [E.hγ]
  have hκ : 0 < (1 + E.γ) * E.β / (1 - E.β) := by have := E.hβ₀; positivity
  have hus : E.uStar ((1 + E.γ) * E.β / (1 - E.β)) ≤ 1 := by
    have hB := E.hB
    simp only [uStar]
    rw [div_le_one (by positivity)]
    have : E.β / (1 - E.β) ≤ (1 + E.γ) * E.β / (1 - E.β) := by
      apply div_le_div_of_nonneg_right _ h1β.le; nlinarith [E.hβ₀, E.hγ]
    have : 1 ≤ E.B * (E.β / (1 - E.β)) := by
      rw [mul_div_assoc', le_div_iff₀ h1β]; linarith
    nlinarith
  have hsf : Feasible fun _ => E.uStar ((1 + E.γ) * E.β / (1 - E.β)) :=
    fun _ => ⟨E.uStar_pos hκ, hus⟩
  set e : ℕ → ℝ := fun t => E.β ^ t * log E.A
  have he : Summable e := (summable_geometric_of_lt_one E.hβ₀.le E.hβ₁).mul_right _
  have hconv : ∀ v, Feasible v → (fun t => E.β ^ t * E.planU h₀ v t) =
      fun t => e t + E.β ^ t * (log (v t) + (1 + E.γ) * log (E.hpath h₀ v t)) :=
    fun v hv => funext fun t => E.planU_eq hh hv t
  have key : ∀ v W, Feasible v → HasSum (fun t => E.β ^ t * E.planU h₀ v t) W → ∀ s,
      (Summable fun t => E.β ^ t * E.planU h₀ (fun _ => E.uStar ((1 + E.γ) * E.β / (1 - E.β))) t) ∧
      W ≤ ∑' t, E.β ^ t * E.planU h₀ (fun _ => E.uStar ((1 + E.γ) * E.β / (1 - E.β))) t +
        E.β ^ s * (E.phi ((1 + E.γ) * E.β / (1 - E.β)) (v s) -
          E.phi ((1 + E.γ) * E.β / (1 - E.β)) (E.uStar ((1 + E.γ) * E.β / (1 - E.β)))) := by
    intro v W hv hW s
    rw [hconv v hv] at hW
    rw [hconv _ hsf]
    exact E.core_limit hh hw hus he hv hW s
  have hsumStar := (key _ _ hsf (Summable.hasSum (by
    rw [hconv _ hsf]
    refine he.add ?_
    simp_rw [mul_add]
    exact ((summable_geometric_of_lt_one E.hβ₀.le E.hβ₁).mul_right _).add
      (by simp_rw [mul_left_comm _ (1 + E.γ)]; exact (E.summable_log_hpath hh hsf).mul_left _)))
    0).1
  constructor
  · rintro ⟨hv, hsv, hopt⟩
    by_contra hne
    obtain ⟨s, hs⟩ : ∃ s, u s ≠ E.uStar ((1 + E.γ) * E.β / (1 - E.β)) := by
      by_contra h; push Not at h; exact hne (funext h)
    have h1 := (key u _ hv hsv.hasSum s).2
    have h2 := hopt _ _ hsf hsumStar.hasSum
    have := mul_neg_of_pos_of_neg (pow_pos E.hβ₀ s)
      (sub_neg.2 ((E.phi_le hκ (hv s).1 (hv s).2).2 hs))
    linarith
  · rintro rfl
    refine ⟨hsf, hsumStar, fun v W hv hW => ?_⟩
    have h1 := (key v W hv hW 0).2
    have := mul_nonpos_of_nonneg_of_nonpos (pow_pos E.hβ₀ 0).le
      (sub_nonpos.2 (E.phi_le hκ (hv 0).1 (hv 0).2).1)
    linarith

/-- Comparison of the closed forms: `u_P ≤ u_eq`, strictly if `γ > 0`, with
equality if `γ = 0`. -/
theorem uStar_comparison :
    E.uStar ((1 + E.γ) * E.β / (1 - E.β)) ≤ (1 - E.β) * (1 + E.B) / E.B ∧
    (0 < E.γ → E.uStar ((1 + E.γ) * E.β / (1 - E.β)) < (1 - E.β) * (1 + E.B) / E.B ∧
      E.growth ((1 - E.β) * (1 + E.B) / E.B) <
        E.growth (E.uStar ((1 + E.γ) * E.β / (1 - E.β)))) ∧
    (E.γ = 0 → E.uStar ((1 + E.γ) * E.β / (1 - E.β)) = (1 - E.β) * (1 + E.B) / E.B) := by
  have h1β : 0 < 1 - E.β := by linarith [E.hβ₁]
  have hB := E.hB; have hβ := E.hβ₀; have hγ := E.hγ
  rw [← E.uStar_priv]
  have hmono : ∀ {a b : ℝ}, 0 < a → a < b → E.uStar b < E.uStar a := fun ha hab => by
    simp only [uStar]
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    nlinarith
  have hle : 1 * E.β / (1 - E.β) ≤ (1 + E.γ) * E.β / (1 - E.β) :=
    div_le_div_of_nonneg_right (by nlinarith) h1β.le
  have hpos : 0 < 1 * E.β / (1 - E.β) := by positivity
  refine ⟨?_, fun hγ' => ?_, fun h0 => by rw [h0, add_zero]⟩
  · rcases hle.eq_or_lt with h | h
    · rw [h]
    · exact (hmono hpos h).le
  · have hlt : 1 * E.β / (1 - E.β) < (1 + E.γ) * E.β / (1 - E.β) :=
      div_lt_div_of_pos_right (by nlinarith) h1β
    have := hmono hpos hlt
    refine ⟨this, ?_⟩
    simp only [growth]; nlinarith

/-- **Lucas (1988): the externality makes equilibrium growth too low.** Under
the interiority condition `1 − β ≤ βB`, let `u_eq` be a competitive
equilibrium and `u_P` an efficient path. If `γ > 0`, then in every period the
equilibrium grows strictly more slowly than the efficient path, because
workers spend too little time learning. If `γ = 0` the two paths coincide. -/
theorem lucas {h₀ : ℝ} (hh : 0 < h₀) (hint : 1 - E.β ≤ E.β * E.B) {ue up : ℕ → ℝ}
    (he : E.IsEquilibrium h₀ ue) (hp : E.IsEfficient h₀ up) :
    (0 < E.γ → ∀ t, up t < ue t ∧ E.growth (ue t) < E.growth (up t)) ∧
    (E.γ = 0 → ue = up) := by
  rw [E.isEquilibrium_iff hh hint] at he
  rw [E.isEfficient_iff hh hint] at hp
  subst he; subst hp
  obtain ⟨-, h1, h2⟩ := E.uStar_comparison
  exact ⟨fun hγ _ => h1 hγ, fun hγ => funext fun _ => (h2 hγ).symm⟩

end Economy

/-- **Non-vacuity.** `β = 9/10`, `B = 1`, `γ = 1` satisfies the interiority
condition `1 − β ≤ βB` with a positive externality. -/
example : ∃ E : Economy, 1 - E.β ≤ E.β * E.B ∧ 0 < E.γ :=
  ⟨⟨1, 1, 1, 9 / 10, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

end Lucas
end Econ

end
