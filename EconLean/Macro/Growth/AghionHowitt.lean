/-
# Schumpeterian growth through creative destruction (Aghion–Howitt)

Aghion and Howitt (1992), "A Model of Growth Through Creative Destruction",
Econometrica; Aghion–Howitt, *The Economics of Growth* (2009), ch. 4;
Acemoglu, *Introduction to Modern Economic Growth*, ch. 14.

**Setting (stationary equilibrium).** Labor `L > 0` is split between
manufacturing `L − n` and research `n`. Research yields innovations at
Poisson rate `λ n` (`λ > 0`); each innovation raises productivity by the
factor `γ > 1` and makes the incumbent's monopoly obsolete (creative
destruction). With Cobb–Douglas final-good technology (intermediate share
`α ∈ (0, 1)`), monopoly profit per unit of the wage is `θ (L − n)` with
`θ = (1 − α)/α`. The value of an innovation is the next monopolist's
profit discounted at `r + λ n` (interest plus the hazard of being displaced),
so the **research arbitrage** condition equating the wage to the expected
value of a unit of research is (`IsArbitrage`)
`r + λ n = λ γ θ (L − n)`.
The long-run growth rate is `g = λ n log γ` (`growth`).

**Results.**
* `existsUnique_arbitrage`, `nStar_mem`: the arbitrage equation has the
  unique solution `n* = (λγθL − r)/(λ(1 + γθ))`, in `(0, L)` when `λγθL > r`.
* `isEquilibrium_iff`, `existsUnique_equilibrium`: allowing the corner
  (`IsEquilibrium`: `n ≥ 0`, value of research ≤ cost, with equality when
  `n > 0`), the unique equilibrium is `n = max 0 n*`; `interior`: it is
  `n*` when `λγθL > r`; `no_research`: it is `0` when `λγθL ≤ r`.
* Comparative statics: `n*` (hence `g`) is strictly increasing in the labor
  force `L` (the scale effect), in the step size `γ`, and strictly decreasing
  in the interest rate `r` (`nStar_strictMono_L`, `nStar_strictMono_γ`,
  `nStar_strictAnti_r`); `growth_pos`: growth is positive.

**Deviations.** Stationary equilibrium only (no transitional dynamics); the
derivation of the profit flow `θ(L − n)` from the monopolist's problem is
taken as given; welfare comparisons (business stealing vs. intertemporal
spillovers) are not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace AghionHowitt

/-- Parameters. -/
structure Params where
  L : ℝ
  lam : ℝ
  γ : ℝ
  θ : ℝ
  r : ℝ
  hL : 0 < L
  hlam : 0 < lam
  hγ : 1 < γ
  hθ : 0 < θ
  hr : 0 < r

namespace Params

variable (P : Params)

/-- The research arbitrage condition. -/
def IsArbitrage (n : ℝ) : Prop := P.r + P.lam * n = P.lam * P.γ * P.θ * (P.L - n)

/-- The equilibrium research level. -/
def nStar : ℝ := (P.lam * P.γ * P.θ * P.L - P.r) / (P.lam * (1 + P.γ * P.θ))

/-- The growth rate of output at research level `n`. -/
def growth (n : ℝ) : ℝ := P.lam * n * Real.log P.γ

theorem den_pos : 0 < P.lam * (1 + P.γ * P.θ) := by
  have := P.hlam; have := P.hθ; have : 0 < P.γ := by linarith [P.hγ]
  positivity

theorem isArbitrage_iff (n : ℝ) : P.IsArbitrage n ↔ n = P.nStar := by
  unfold IsArbitrage nStar
  rw [eq_div_iff P.den_pos.ne']
  constructor <;> intro h <;> linarith

theorem existsUnique_arbitrage : ∃! n, P.IsArbitrage n :=
  ⟨P.nStar, (P.isArbitrage_iff _).2 rfl, fun _ h => (P.isArbitrage_iff _).1 h⟩

/-- With a large enough market, research is interior: `0 < n* < L`. -/
theorem nStar_mem (h : P.r < P.lam * P.γ * P.θ * P.L) : 0 < P.nStar ∧ P.nStar < P.L := by
  have hd := P.den_pos
  refine ⟨div_pos (by linarith) hd, ?_⟩
  rw [nStar, div_lt_iff₀ hd]
  have := P.hlam; have := P.hL; have := P.hr
  nlinarith

theorem nStar_lt_L : P.nStar < P.L := by
  rw [nStar, div_lt_iff₀ P.den_pos]
  have := P.hlam; have := P.hL; have := P.hr
  nlinarith

theorem nStar_nonpos_iff : P.nStar ≤ 0 ↔ P.lam * P.γ * P.θ * P.L ≤ P.r := by
  rw [nStar, div_le_iff₀ P.den_pos, zero_mul, sub_nonpos]

/-- A stationary **equilibrium** research level, allowing the corner `n = 0`:
research is non-negative and at most `L`, the value of research never exceeds
its cost, and it equals the cost whenever research is undertaken. -/
def IsEquilibrium (n : ℝ) : Prop :=
  0 ≤ n ∧ n ≤ P.L ∧ P.lam * P.γ * P.θ * (P.L - n) ≤ P.r + P.lam * n ∧
    (0 < n → P.IsArbitrage n)

/-- **Existence and uniqueness of equilibrium**: `n = max 0 n*`. -/
theorem isEquilibrium_iff (n : ℝ) : P.IsEquilibrium n ↔ n = max 0 P.nStar := by
  have hL := P.nStar_lt_L
  constructor
  · rintro ⟨h0, -, hle, hpos⟩
    rcases h0.eq_or_lt with rfl | hn
    · have : P.lam * P.γ * P.θ * P.L ≤ P.r := by linarith
      rw [max_eq_left (P.nStar_nonpos_iff.2 this)]
    · have := (P.isArbitrage_iff n).1 (hpos hn)
      subst this
      rw [max_eq_right hn.le]
  · intro h
    by_cases hs : P.nStar ≤ 0
    · rw [max_eq_left hs] at h
      subst h
      have := P.nStar_nonpos_iff.1 hs
      refine ⟨le_rfl, P.hL.le, by linarith, fun h => absurd h (lt_irrefl 0)⟩
    · push Not at hs
      rw [max_eq_right hs.le] at h
      subst h
      have ha := (P.isArbitrage_iff P.nStar).2 rfl
      exact ⟨hs.le, hL.le, ha.symm.le, fun _ => ha⟩

theorem existsUnique_equilibrium : ∃! n, P.IsEquilibrium n :=
  ⟨max 0 P.nStar, (P.isEquilibrium_iff _).2 rfl, fun _ h => (P.isEquilibrium_iff _).1 h⟩

/-- **No research** when the market is too small relative to the interest
rate: the unique equilibrium is `n = 0`. -/
theorem no_research (h : P.lam * P.γ * P.θ * P.L ≤ P.r) (n : ℝ) :
    P.IsEquilibrium n ↔ n = 0 := by
  rw [P.isEquilibrium_iff, max_eq_left (P.nStar_nonpos_iff.2 h)]

/-- With a large enough market the equilibrium is interior, `n = n* > 0`. -/
theorem interior (h : P.r < P.lam * P.γ * P.θ * P.L) (n : ℝ) :
    P.IsEquilibrium n ↔ n = P.nStar := by
  rw [P.isEquilibrium_iff, max_eq_right (P.nStar_mem h).1.le]

theorem growth_pos (h : P.r < P.lam * P.γ * P.θ * P.L) : 0 < P.growth P.nStar :=
  mul_pos (mul_pos P.hlam (P.nStar_mem h).1) (Real.log_pos P.hγ)

/-- **Scale effect.** A larger labor force raises research and growth. -/
theorem nStar_strictMono_L (P' : Params) (hlam : P'.lam = P.lam) (hγ : P'.γ = P.γ)
    (hθ : P'.θ = P.θ) (hr : P'.r = P.r) (hL : P.L < P'.L) : P.nStar < P'.nStar := by
  simp only [nStar, hlam, hγ, hθ, hr]
  apply div_lt_div_of_pos_right _ P.den_pos
  have : 0 < P.lam * P.γ * P.θ := by
    have := P.hlam; have := P.hθ; have : 0 < P.γ := by linarith [P.hγ]
    positivity
  nlinarith

/-- A higher interest rate lowers research (the value of an innovation falls). -/
theorem nStar_strictAnti_r (P' : Params) (hlam : P'.lam = P.lam) (hγ : P'.γ = P.γ)
    (hθ : P'.θ = P.θ) (hL : P'.L = P.L) (hr : P.r < P'.r) : P'.nStar < P.nStar := by
  simp only [nStar, hlam, hγ, hθ, hL]
  exact div_lt_div_of_pos_right (by linarith) P.den_pos

/-- Larger innovations raise research. -/
theorem nStar_strictMono_γ (P' : Params) (hlam : P'.lam = P.lam) (hθ : P'.θ = P.θ)
    (hL : P'.L = P.L) (hr : P'.r = P.r) (hγ : P.γ < P'.γ) : P.nStar < P'.nStar := by
  simp only [nStar, hlam, hθ, hL, hr]
  have hd := P.den_pos
  have hd' : 0 < P.lam * (1 + P'.γ * P.θ) := by
    have := P.hlam; have := P.hθ; have : 0 < P'.γ := by linarith [P.hγ]
    positivity
  rw [div_lt_div_iff₀ hd hd']
  have := P.hlam; have := P.hθ; have := P.hL; have := P.hr
  have h1 : 0 < P'.γ - P.γ := by linarith
  -- difference = λ² θ (γ' − γ)(L + r/λ) > 0
  have key : (P.lam * P'.γ * P.θ * P.L - P.r) * (P.lam * (1 + P.γ * P.θ)) -
      (P.lam * P.γ * P.θ * P.L - P.r) * (P.lam * (1 + P'.γ * P.θ)) =
      P.lam * P.θ * (P'.γ - P.γ) * (P.lam * P.L + P.r) := by ring
  have : 0 < P.lam * P.θ * (P'.γ - P.γ) * (P.lam * P.L + P.r) := by positivity
  linarith

end Params
end AghionHowitt
end Econ

end
