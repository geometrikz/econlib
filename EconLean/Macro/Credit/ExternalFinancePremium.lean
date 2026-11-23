/-
# The external finance premium (Bernanke–Gertler–Gilchrist)

Bernanke, Gertler and Gilchrist (1999), "The Financial Accelerator in a
Quantitative Business Cycle Framework", Handbook of Macroeconomics,
§3 and Appendix A; Bernanke–Gertler (1989), AER.

**Setting.** An entrepreneur with net worth `N` finances a project of size
`I` (normalized returns `ω ≥ 0` per unit), borrowing `L = I − N` under the
standard debt contract that is optimal with costly state verification
(`Econ.CSV.debt_optimal_pc`). With face value `D`, the lender's expected
return net of monitoring costs is `g(D)`; competitive lenders require
`g(D) = L` (risk-free rate normalized to zero). In BGG, `g` is increasing
and concave on the relevant range with `g(0) = 0`
(`Schedule`; e.g. `ω` uniform on `[0, 1]` with monitoring cost a fraction
`μ` of the verified return gives `g(D) = D − (1 + μ)D²/2`, `uniform`).
Expected monitoring costs are `m(D) ≥ 0`. The safe rate is normalized to
zero (gross `1`), so `L = I − N` (BGG: `R(QK − N)`).

**Results.**
* `existsUnique_face`: every loan `0 < L ≤ g(D_max)` has a unique face value
  `D ∈ (0, D_max]` with `g(D) = L`.
* `face_strictMono`: larger loans need strictly larger face values.
* `contractRate_strictMono`: the promised rate `D/L` rises with the loan
  (a default spread, present even without monitoring costs).
* `efp`, `efp_eq_one_iff`, `one_lt_efp`: the **external finance premium**,
  expected payment per unit borrowed `(g(D) + m(D))/L = 1 + m(D)/L`, equals
  the riskless cost `1` iff monitoring costs vanish (Modigliani–Miller) and
  exceeds it otherwise.
* `uniform`: the uniform-returns schedule satisfies the assumptions;
  `uniform_efp_zero`: with `μ = 0` the premium is `1`.
* `uniform_efp_strictMono`, `uniform_efp_anti_netWorth`: with `μ > 0` the
  premium strictly rises with the loan, so it strictly **falls with net
  worth**, the core of the financial accelerator.

**Deviations.** Static, partial-equilibrium contract; returns are normalized
to `[0, 1]` in the uniform case, so feasible loans are at most `g(D_max)`; the general-equilibrium
accelerator (net worth dynamics feeding investment) is not formalized; the
monotonicity and concavity of `g` are reduced-form assumptions (verified for
the uniform example) rather than derived from BGG's hazard-rate condition,
and the premium's monotonicity is proved for the uniform case only.
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace BGG

open Set

/-- The lender's net expected-return schedule as a function of face value. -/
structure Schedule where
  g : ℝ → ℝ
  Dmax : ℝ
  hDmax : 0 < Dmax
  g0 : g 0 = 0
  cont : ContinuousOn g (Icc 0 Dmax)
  mono : StrictMonoOn g (Icc 0 Dmax)
  concave : StrictConcaveOn ℝ (Icc 0 Dmax) g
  /-- Expected monitoring (verification) cost at face value `D`. -/
  m : ℝ → ℝ
  m_nonneg : ∀ D, 0 ≤ m D

namespace Schedule

variable (S : Schedule)

/-- `D` is the face value financing loan `L`. -/
def IsFace (L D : ℝ) : Prop := D ∈ Icc 0 S.Dmax ∧ S.g D = L

theorem existsUnique_face {L : ℝ} (hL : 0 < L) (hLm : L ≤ S.g S.Dmax) :
    ∃! D, S.IsFace L D := by
  have hI : Icc (S.g 0) (S.g S.Dmax) ⊆ S.g '' Icc 0 S.Dmax :=
    intermediate_value_Icc S.hDmax.le S.cont
  obtain ⟨D, hD, hgD⟩ := hI ⟨by rw [S.g0]; exact hL.le, hLm⟩
  refine ⟨D, ⟨hD, hgD⟩, fun D' ⟨hD', hg'⟩ => S.mono.injOn hD' hD (hg'.trans hgD.symm)⟩

theorem face_pos {L D : ℝ} (hL : 0 < L) (h : S.IsFace L D) : 0 < D := by
  rcases h.1.1.eq_or_lt with h0 | h0
  · have := h.2; rw [← h0, S.g0] at this; linarith
  · exact h0

theorem face_strictMono {L L' D D' : ℝ} (hLL : L < L') (h : S.IsFace L D)
    (h' : S.IsFace L' D') : D < D' := by
  by_contra hle; push Not at hle
  have := S.mono.monotoneOn h'.1 h.1 hle
  linarith [h.2, h'.2]

/-- Average return `g(D)/D` falls with `D` (strict concavity and `g(0) = 0`). -/
theorem avg_anti {D D' : ℝ} (hD : 0 < D) (hDD : D < D') (hD' : D' ≤ S.Dmax) :
    S.g D' / D' < S.g D / D := by
  have hD'0 : 0 < D' := hD.trans hDD
  set t := D / D'
  have ht0 : 0 < t := div_pos hD hD'0
  have ht1 : t < 1 := (div_lt_one hD'0).2 hDD
  have hconv := S.concave.2 (x := D') (y := 0) ⟨hD'0.le, hD'⟩ ⟨le_rfl, S.hDmax.le⟩
    hD'0.ne' ht0 (by linarith : 0 < 1 - t) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, S.g0] at hconv
  have hx : t * D' = D := div_mul_cancel₀ D hD'0.ne'
  rw [hx] at hconv
  rw [div_lt_div_iff₀ hD'0 hD]
  have : t * S.g D' * D' = S.g D' * D := by rw [← hx]; ring
  nlinarith

/-- **The promised contract rate rises with the loan.** `D/L` is a default
spread: it exists even without monitoring costs. -/
theorem contractRate_strictMono {L L' D D' : ℝ} (hL : 0 < L) (hLL : L < L')
    (h : S.IsFace L D) (h' : S.IsFace L' D') : D / L < D' / L' := by
  have hD := S.face_pos hL h
  have hDD := S.face_strictMono hLL h h'
  have hD'0 : 0 < D' := hD.trans hDD
  have := S.avg_anti hD hDD h'.1.2
  rw [h.2, h'.2] at this
  rw [div_lt_div_iff₀ hL (hL.trans hLL)]
  rw [div_lt_div_iff₀ hD'0 hD] at this
  linarith

/-- The **external finance premium**: the entrepreneur's expected payment to
the lender (`g(D) + m(D)`, i.e. the lender's net return plus the monitoring
costs it must recoup) per unit borrowed, relative to the riskless cost `1`. -/
def efp (L D : ℝ) : ℝ := (S.g D + S.m D) / L

theorem efp_eq {L D : ℝ} (hL : 0 < L) (h : S.IsFace L D) : S.efp L D = 1 + S.m D / L := by
  rw [efp, h.2]; field_simp

/-- **No agency cost, no premium** (Modigliani–Miller): the premium is `1`
iff expected monitoring costs vanish, and exceeds `1` otherwise. -/
theorem efp_eq_one_iff {L D : ℝ} (hL : 0 < L) (h : S.IsFace L D) :
    S.efp L D = 1 ↔ S.m D = 0 := by
  rw [S.efp_eq hL h]
  constructor
  · intro h'; have : S.m D / L = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h1 | h1
    · exact h1
    · linarith
  · intro h'; rw [h']; simp

theorem one_lt_efp {L D : ℝ} (hL : 0 < L) (h : S.IsFace L D) (hm : 0 < S.m D) :
    1 < S.efp L D := by
  rw [S.efp_eq hL h]; have := div_pos hm hL; linarith

end Schedule

/-- **Uniform returns.** With `ω` uniform on `[0, 1]` and monitoring cost
`μ ω` on verified states, `E min(ω, D) = D − D²/2` and expected monitoring
cost is `μ D²/2`, so `g(D) = D − (1 + μ)D²/2`, increasing up to
`D_max = 1/(1 + μ)`. -/
def uniform (μ : ℝ) (hμ : 0 ≤ μ) : Schedule where
  g D := D - (1 + μ) * D ^ 2 / 2
  Dmax := 1 / (1 + μ)
  hDmax := by positivity
  g0 := by simp
  cont := (continuous_id.sub ((continuous_const.mul (continuous_pow 2)).div_const _)).continuousOn
  mono := by
    intro x hx y hy hxy
    have h1 : (1 + μ) * (x + y) < 2 := by
      have hx' : (1 + μ) * x ≤ 1 := by
        have := hx.2; rw [le_div_iff₀ (by linarith)] at this; linarith
      have hy' : (1 + μ) * y ≤ 1 := by
        have := hy.2; rw [le_div_iff₀ (by linarith)] at this; linarith
      nlinarith
    simp only
    nlinarith
  concave := by
    refine ⟨convex_Icc _ _, fun x _ y _ hxy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have : 0 < (x - y) ^ 2 := by have := sub_ne_zero.2 hxy; positivity
    nlinarith [mul_pos (mul_pos ha hb) this]
  m D := μ * D ^ 2 / 2
  m_nonneg D := by positivity

/-- Without monitoring costs the premium is exactly `1` at every loan. -/
theorem uniform_efp_zero {L D : ℝ} (hL : 0 < L) (h : (uniform 0 le_rfl).IsFace L D) :
    (uniform 0 le_rfl).efp L D = 1 :=
  ((uniform 0 le_rfl).efp_eq_one_iff hL h).2 (by simp [uniform])

/-- **The external finance premium rises with the loan** (uniform returns,
`μ > 0`): `efp = 1 + μD/(2 − (1 + μ)D)`, increasing in the face value. -/
theorem uniform_efp_strictMono {μ : ℝ} (hμ : 0 < μ) {L L' D D' : ℝ} (hL : 0 < L) (hLL : L < L')
    (h : (uniform μ hμ.le).IsFace L D) (h' : (uniform μ hμ.le).IsFace L' D') :
    (uniform μ hμ.le).efp L D < (uniform μ hμ.le).efp L' D' := by
  set S := uniform μ hμ.le
  have hD := S.face_pos hL h
  have hDD := S.face_strictMono hLL h h'
  have hL' : 0 < L' := hL.trans hLL
  rw [S.efp_eq hL h, S.efp_eq hL' h', ← h.2, ← h'.2]
  have hx : (1 + μ) * D' ≤ 1 := by
    have := h'.1.2; simp only [S, uniform] at this; rw [le_div_iff₀ (by linarith)] at this; linarith
  simp only [S, uniform]
  have hg : 0 < D - (1 + μ) * D ^ 2 / 2 := by nlinarith
  have hg' : 0 < D' - (1 + μ) * D' ^ 2 / 2 := by nlinarith
  rw [add_lt_add_iff_left, div_lt_div_iff₀ hg hg']
  nlinarith [mul_pos hμ hD, mul_pos (mul_pos hμ hD) (hD.trans hDD)]

/-- **The financial accelerator.** With uniform returns and `μ > 0`, higher
entrepreneurial net worth strictly lowers the external finance premium. -/
theorem uniform_efp_anti_netWorth {μ : ℝ} (hμ : 0 < μ) {I N N' D D' : ℝ} (hNN : N < N')
    (hN' : N' < I) (h : (uniform μ hμ.le).IsFace (I - N) D)
    (h' : (uniform μ hμ.le).IsFace (I - N') D') :
    (uniform μ hμ.le).efp (I - N') D' < (uniform μ hμ.le).efp (I - N) D :=
  uniform_efp_strictMono hμ (by linarith) (by linarith) h' h

end BGG
end Econ

end
