/-
# Rubinstein alternating-offers bargaining (Rubinstein 1982; Shaked–Sutton 1984)

Rubinstein (1982); Shaked and Sutton (1984); Osborne–Rubinstein, *Bargaining and Markets*, Ch. 3;
MWG §9.AA; Binmore, Rubinstein and Wolinsky (1986). Two players split a pie of size `1`.
Player `1` proposes in even periods, player `2` in odd periods; the responder accepts or
rejects; agreement on the share `x` at period `t` gives player `i` the payoff `δᵢᵗ · xᵢ`,
with `0 ≤ δᵢ < 1`.

Rubinstein's theorem is that the unique subgame perfect equilibrium is stationary: the proposer
`i` keeps the share `(1 − δⱼ)/(1 − δ₁δ₂)` and the responder accepts at once. This file proves
the algebraic results the theorem rests on; the game, strategies, SPE and the theorem itself
are in `Bargaining/RubinsteinGame`.

* `rubinstein_stationary`: the proposer shares `x*`, `y*` are the unique solution of the
  indifference conditions `x = 1 − δ₂ y`, `y = 1 − δ₁ x` (each responder is offered exactly
  the discounted value of proposing tomorrow).
* `shaked_sutton_bounds`: the algebraic core of the uniqueness argument. Let `M₁, m₁` be the sup and inf of player 1's SPE
  payoffs in subgames where she proposes, and `M₂, m₂` the same for player 2. Subgame
  perfection gives `m₁ ≥ 1 − δ₂ M₂`, `M₁ ≤ 1 − δ₂ m₂` and symmetrically; these force
  `M₁ = m₁ = x*` and `M₂ = m₂ = y*`. We formalize this algebraic core here; the four
  inequalities are derived from strategies on infinite histories in `Bargaining/RubinsteinGame`
  (`spePay_eq`, `bargSPE_eq_stationary`).
* `rubinstein_first_mover`, `rubinstein_patience`: with equal discounting the first mover gets
  more than half; a player's share rises with her own patience and falls with her opponent's.
* `rubinstein_symmetric_limit`, `rubinstein_limit`: as offers become frequent
  (`δᵢ = exp(−rᵢ Δ)`, `Δ → 0⁺`), player 1's share tends to `r₂/(r₁ + r₂)`, which is the
  asymmetric Nash bargaining split with bargaining powers `1/rᵢ` (Binmore–Rubinstein–Wolinsky
  1986; that identification is not formalized). Player 2's proposer share
  `rubinsteinShare δ₂ δ₁` tends to `r₁/(r₁ + r₂)`, so in the limit it does not matter who
  proposes first.

The model has `0 ≤ δᵢ < 1`. `one_sub_mul_pos` and `rubinstein_stationary` omit `0 ≤ δ₂`,
which they do not need.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Filter Topology

/-- Player 1's equilibrium share when she proposes. -/
noncomputable def rubinsteinShare (δ₁ δ₂ : ℝ) : ℝ := (1 - δ₂) / (1 - δ₁ * δ₂)

lemma one_sub_mul_pos {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂' : δ₂ < 1) :
    0 < 1 - δ₁ * δ₂ := by nlinarith

/-- **Stationary equilibrium shares**: `(x*, y*) = (rubinsteinShare δ₁ δ₂, rubinsteinShare δ₂ δ₁)`
is the unique solution of the responders' indifference conditions. -/
theorem rubinstein_stationary {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1)
    (h₂' : δ₂ < 1) (x y : ℝ) :
    (x = 1 - δ₂ * y ∧ y = 1 - δ₁ * x) ↔ (x = rubinsteinShare δ₁ δ₂ ∧ y = rubinsteinShare δ₂ δ₁) := by
  have hpos := one_sub_mul_pos h₁ h₁' h₂'
  have hpos' : 1 - δ₂ * δ₁ ≠ 0 := by rw [mul_comm]; exact hpos.ne'
  unfold rubinsteinShare
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · rw [eq_div_iff hpos.ne']; rw [hy] at hx; linarith
    · rw [eq_div_iff hpos']; rw [hx] at hy; linarith
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp <;> ring

/-- **Algebraic core of the Shaked–Sutton uniqueness argument.** If the sup and inf of the two players' SPE payoffs
(as proposers) satisfy the four subgame-perfection inequalities, they all coincide with the
Rubinstein shares. -/
theorem shaked_sutton_bounds {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂) (h₂' : δ₂ < 1)
    {M₁ m₁ M₂ m₂ : ℝ} (hlo₁ : 1 - δ₂ * M₂ ≤ m₁) (hhi₁ : M₁ ≤ 1 - δ₂ * m₂)
    (hlo₂ : 1 - δ₁ * M₁ ≤ m₂) (hhi₂ : M₂ ≤ 1 - δ₁ * m₁) (h₁m : m₁ ≤ M₁) (h₂m : m₂ ≤ M₂) :
    M₁ = rubinsteinShare δ₁ δ₂ ∧ m₁ = rubinsteinShare δ₁ δ₂ ∧
      M₂ = rubinsteinShare δ₂ δ₁ ∧ m₂ = rubinsteinShare δ₂ δ₁ := by
  have hpos := one_sub_mul_pos h₁ h₁' h₂'
  have hpos' : 0 < 1 - δ₂ * δ₁ := by rw [mul_comm]; exact hpos
  -- `M₁ ≤ 1 − δ₂ (1 − δ₁ M₁)` and `m₁ ≥ 1 − δ₂ (1 − δ₁ m₁)`
  have a1 : M₁ * (1 - δ₁ * δ₂) ≤ 1 - δ₂ := by nlinarith [mul_le_mul_of_nonneg_left hlo₂ h₂]
  have b1 : 1 - δ₂ ≤ m₁ * (1 - δ₁ * δ₂) := by nlinarith [mul_le_mul_of_nonneg_left hhi₂ h₂]
  have a2 : M₂ * (1 - δ₂ * δ₁) ≤ 1 - δ₁ := by nlinarith [mul_le_mul_of_nonneg_left hlo₁ h₁]
  have b2 : 1 - δ₁ ≤ m₂ * (1 - δ₂ * δ₁) := by nlinarith [mul_le_mul_of_nonneg_left hhi₁ h₁]
  have e1 : M₁ = m₁ := le_antisymm (le_of_mul_le_mul_right (a1.trans b1) hpos) h₁m
  have e2 : M₂ = m₂ := le_antisymm (le_of_mul_le_mul_right (a2.trans b2) hpos') h₂m
  have x1 : m₁ = rubinsteinShare δ₁ δ₂ := by
    unfold rubinsteinShare; rw [eq_div_iff hpos.ne']; rw [e1] at a1; linarith
  have x2 : m₂ = rubinsteinShare δ₂ δ₁ := by
    unfold rubinsteinShare; rw [eq_div_iff hpos'.ne']; rw [e2] at a2; linarith
  exact ⟨e1.trans x1, x1, e2.trans x2, x2⟩

/-- The equilibrium shares are between `0` and `1`, so the stationary offers are feasible. -/
theorem rubinsteinShare_mem {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₁' : δ₁ < 1) (h₂ : 0 ≤ δ₂)
    (h₂' : δ₂ < 1) : 0 < rubinsteinShare δ₁ δ₂ ∧ rubinsteinShare δ₁ δ₂ ≤ 1 := by
  have hpos := one_sub_mul_pos h₁ h₁' h₂'
  unfold rubinsteinShare
  exact ⟨div_pos (by linarith) hpos, (div_le_one hpos).2 (by nlinarith)⟩

/-- **First-mover advantage**: with a common discount factor `δ < 1` the proposer gets
`1/(1 + δ) > 1/2`. -/
theorem rubinstein_first_mover {δ : ℝ} (h : 0 ≤ δ) (h' : δ < 1) :
    rubinsteinShare δ δ = 1 / (1 + δ) ∧ 1 / 2 < rubinsteinShare δ δ := by
  have e : rubinsteinShare δ δ = 1 / (1 + δ) := by
    unfold rubinsteinShare
    have : (1 : ℝ) - δ * δ = (1 - δ) * (1 + δ) := by ring
    have h1 : (1 : ℝ) - δ ≠ 0 := by linarith
    have h2 : (1 : ℝ) + δ ≠ 0 := by linarith
    rw [this]; field_simp
  refine ⟨e, ?_⟩
  rw [e, lt_div_iff₀ (by linarith)]
  linarith

/-- **Patience is bargaining power**: player 1's share is increasing in her own discount
factor and decreasing in her opponent's. -/
theorem rubinstein_patience {δ₁ δ₁' δ₂ δ₂' : ℝ} (h₁ : 0 ≤ δ₁) (h₁₁ : δ₁ ≤ δ₁') (h₁' : δ₁' < 1)
    (h₂ : 0 ≤ δ₂) (h₂₂ : δ₂ ≤ δ₂') (h₂' : δ₂' < 1) :
    rubinsteinShare δ₁ δ₂ ≤ rubinsteinShare δ₁' δ₂ ∧ rubinsteinShare δ₁ δ₂' ≤ rubinsteinShare δ₁ δ₂ := by
  have p1 := one_sub_mul_pos h₁ (h₁₁.trans_lt h₁') (h₂₂.trans_lt h₂')
  have p2 := one_sub_mul_pos (h₁.trans h₁₁) h₁' (h₂₂.trans_lt h₂')
  have p3 := one_sub_mul_pos h₁ (h₁₁.trans_lt h₁') h₂'
  unfold rubinsteinShare
  constructor
  · rw [div_le_div_iff₀ p1 p2]; nlinarith [mul_le_mul_of_nonneg_right h₁₁ h₂]
  · rw [div_le_div_iff₀ p3 p1]
    nlinarith [mul_le_mul_of_nonneg_left h₂₂ h₁, mul_nonneg h₁ (sub_nonneg.2 h₂₂)]

/-- `(1 − exp(−a Δ))/Δ → a` as `Δ → 0`, `Δ ≠ 0`. -/
lemma tendsto_one_sub_exp_div (a : ℝ) :
    Tendsto (fun t : ℝ => (1 - Real.exp (-(a * t))) / t) (𝓝[≠] 0) (𝓝 a) := by
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(a * t))) a 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(a * t)) (-a) 0 := by
      have := (hasDerivAt_id (0 : ℝ)).const_mul (-a)
      simp only [id, mul_one] at this
      exact this.congr_of_eventuallyEq (Eventually.of_forall fun t => by ring)
    have h2 := (Real.hasDerivAt_exp (-(a * 0))).comp 0 h1
    have h3 := h2.const_sub 1
    simpa using h3
  have := hd.tendsto_slope_zero
  refine this.congr' (Eventually.of_forall fun t => ?_)
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- **Frequent offers** (Binmore–Rubinstein–Wolinsky 1986). With discount rates `r₁, r₂ > 0`
and time `Δ` between offers, `δᵢ = exp(−rᵢ Δ)`; as `Δ → 0⁺` player 1's share tends to
`r₂ / (r₁ + r₂)` (the asymmetric Nash bargaining split with bargaining powers proportional to
`1/rᵢ`; that identification is not formalized). -/
theorem rubinstein_limit {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    Tendsto (fun Δ : ℝ => rubinsteinShare (Real.exp (-(r₁ * Δ))) (Real.exp (-(r₂ * Δ))))
      (𝓝[>] 0) (𝓝 (r₂ / (r₁ + r₂))) := by
  have hlim := ((tendsto_one_sub_exp_div r₂).div (tendsto_one_sub_exp_div (r₁ + r₂))
    (by linarith)).mono_left (nhdsGT_le_nhdsNE 0)
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun Δ (hΔ : 0 < Δ) => ?_)
  simp only [Pi.div_apply]
  unfold rubinsteinShare
  rw [← Real.exp_add, show -(r₁ * Δ) + -(r₂ * Δ) = -((r₁ + r₂) * Δ) by ring]
  rw [div_div_div_cancel_right₀ hΔ.ne']

/-- Equal discount rates: the split tends to `1/2`. -/
theorem rubinstein_symmetric_limit {r : ℝ} (hr : 0 < r) :
    Tendsto (fun Δ : ℝ => rubinsteinShare (Real.exp (-(r * Δ))) (Real.exp (-(r * Δ))))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have := rubinstein_limit hr hr
  rwa [show r / (r + r) = 1 / 2 by field_simp; ring] at this

end Econ
