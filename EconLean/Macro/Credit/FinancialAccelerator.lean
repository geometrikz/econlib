/-
# The financial accelerator in general equilibrium (BGG)

Bernanke, Gertler and Gilchrist (1999), Handbook of Macroeconomics, §4;
Bernanke–Gertler (1989), AER; Gertler–Kiyotaki (2010), Handbook of Monetary
Economics, §2.

**Setting.** Entrepreneurs with aggregate net worth `N > 0` choose the
capital stock `K > 0`. Capital earns `A f'(K)` with productivity `A > 0` and
marginal product `f'` positive and strictly decreasing. External finance
costs the safe rate `R > 0` times the **external finance premium**
`s(N/K)`, a strictly decreasing function of the net-worth-to-assets ratio
(the contracting result `Econ.EFP.Schedule.uniform_efp_anti_netWorth`: more
skin in the game, cheaper credit). The capital market clears when
`A f'(K) = R s(N/K)` (`IsEq`; BGG eq. 4.3–4.4 in steady state).

**Results.**
* `K_strictMono_N`: **net worth matters**: higher net worth means strictly
  more capital (no Modigliani–Miller separation).
* `premium_anti_N`: at given productivity the equilibrium premium **falls**
  with net worth. (Whether it is countercyclical over the cycle depends on
  whether net worth rises faster than capital in a boom; this static model
  does not guarantee it, e.g. with `κ = 0` the premium rises with `A`.)
* `K_indep_N`: without the friction (`s` constant) capital does not depend
  on net worth.
* `K_strictMono_A`: capital rises with productivity at given net worth.
* `amplification`: if net worth itself rises with productivity
  (`N = N₀ + κ A`, `κ > 0`, retained profits), capital after a productivity
  increase is strictly higher than with net worth held fixed: the
  net-worth channel adds to the direct effect (the static core of the
  financial accelerator).
* `existsUnique_K`: under boundary conditions there is a unique
  equilibrium; `premium_example`: `s(x) = 1 + m/x` with `m > 0` satisfies
  the assumptions.

**Deviations.** Static (steady-state) partial-equilibrium capital market
with the price of capital fixed at `Q = 1`: BGG's asset-price channel and
intertemporal net-worth dynamics (persistence) are not modelled; the
net-worth response is summarized by `N = N₀ + κ A`; the premium `s ≥ 1` is
a reduced-form gross premium
(its monotonicity in net worth is proved for the uniform CSV example in
`ExternalFinancePremium`).
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

noncomputable section

namespace Econ
namespace BGG

open Set

/-- Primitives: marginal product `f'`, premium schedule `s`, safe rate `R`. -/
structure Env where
  f' : ℝ → ℝ
  s : ℝ → ℝ
  R : ℝ
  hR : 0 < R
  hf'pos : ∀ K, 0 < K → 0 < f' K
  hf'anti : StrictAntiOn f' (Ioi 0)
  hs : AntitoneOn s (Ioi 0)
  hs1 : ∀ x, 0 < x → 1 ≤ s x

namespace Env

variable (E : Env)

/-- Capital-market equilibrium. -/
def IsEq (A N K : ℝ) : Prop := 0 < K ∧ A * E.f' K = E.R * E.s (N / K)

/-- **Net worth matters.** With a strictly decreasing premium, higher net worth
means strictly more capital. -/
theorem K_strictMono_N (hs : StrictAntiOn E.s (Ioi 0)) {A N₁ N₂ K₁ K₂ : ℝ} (hA : 0 < A)
    (hN₁ : 0 < N₁) (hN : N₁ < N₂) (h₁ : E.IsEq A N₁ K₁) (h₂ : E.IsEq A N₂ K₂) : K₁ < K₂ := by
  by_contra hK
  push Not at hK
  obtain ⟨hK₁, e₁⟩ := h₁; obtain ⟨hK₂, e₂⟩ := h₂
  have hx : N₁ / K₁ < N₂ / K₂ :=
    (div_lt_div_of_pos_right hN hK₁).trans_le (div_le_div_of_nonneg_left (by linarith) hK₂ hK)
  have hs' : E.s (N₂ / K₂) < E.s (N₁ / K₁) :=
    hs (mem_Ioi.2 (div_pos hN₁ hK₁)) (mem_Ioi.2 (div_pos (by linarith) hK₂)) hx
  have hf : E.f' K₁ ≤ E.f' K₂ := E.hf'anti.antitoneOn (mem_Ioi.2 hK₂) (mem_Ioi.2 hK₁) hK
  have := mul_le_mul_of_nonneg_left hf hA.le
  have := mul_lt_mul_of_pos_left hs' E.hR
  linarith

/-- **A countercyclical premium**: the equilibrium premium falls with net
worth. -/
theorem premium_anti_N (hs : StrictAntiOn E.s (Ioi 0)) {A N₁ N₂ K₁ K₂ : ℝ} (hA : 0 < A)
    (hN₁ : 0 < N₁) (hN : N₁ < N₂) (h₁ : E.IsEq A N₁ K₁) (h₂ : E.IsEq A N₂ K₂) :
    E.s (N₂ / K₂) < E.s (N₁ / K₁) := by
  have hK := E.K_strictMono_N hs hA hN₁ hN h₁ h₂
  have hf := E.hf'anti (mem_Ioi.2 h₁.1) (mem_Ioi.2 h₂.1) hK
  have := mul_lt_mul_of_pos_left hf hA
  rw [h₁.2, h₂.2] at this
  exact lt_of_mul_lt_mul_left this E.hR.le

/-- **No friction, no role for net worth.** -/
theorem K_indep_N (hconst : ∀ x y, 0 < x → 0 < y → E.s x = E.s y) {A N₁ N₂ K₁ K₂ : ℝ}
    (hA : 0 < A) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (h₁ : E.IsEq A N₁ K₁) (h₂ : E.IsEq A N₂ K₂) :
    K₁ = K₂ := by
  have e : A * E.f' K₁ = A * E.f' K₂ := by
    rw [h₁.2, h₂.2, hconst _ _ (div_pos hN₁ h₁.1) (div_pos hN₂ h₂.1)]
  exact E.hf'anti.injOn (mem_Ioi.2 h₁.1) (mem_Ioi.2 h₂.1) (mul_left_cancel₀ hA.ne' e)

/-- Capital rises with productivity at given net worth. -/
theorem K_strictMono_A {A₁ A₂ N K₁ K₂ : ℝ} (hA₁ : 0 < A₁) (hA : A₁ < A₂) (hN : 0 < N)
    (h₁ : E.IsEq A₁ N K₁) (h₂ : E.IsEq A₂ N K₂) : K₁ < K₂ := by
  by_contra hK
  push Not at hK
  obtain ⟨hK₁, e₁⟩ := h₁; obtain ⟨hK₂, e₂⟩ := h₂
  have hf : E.f' K₁ ≤ E.f' K₂ := E.hf'anti.antitoneOn (mem_Ioi.2 hK₂) (mem_Ioi.2 hK₁) hK
  have hx : N / K₁ ≤ N / K₂ := div_le_div_of_nonneg_left hN.le hK₂ hK
  have hs' : E.s (N / K₂) ≤ E.s (N / K₁) :=
    E.hs (mem_Ioi.2 (div_pos hN hK₁)) (mem_Ioi.2 (div_pos hN hK₂)) hx
  have h1 : A₁ * E.f' K₁ < A₂ * E.f' K₁ := mul_lt_mul_of_pos_right hA (E.hf'pos _ hK₁)
  have h2 : A₂ * E.f' K₁ ≤ A₂ * E.f' K₂ := mul_le_mul_of_nonneg_left hf (by linarith)
  have := mul_le_mul_of_nonneg_left hs' E.hR.le
  linarith

/-- **The financial accelerator.** With net worth `N₀ + κ A` rising in
productivity, the capital response to `A₁ → A₂` exceeds the response at net
worth held at its initial level. -/
theorem amplification (hs : StrictAntiOn E.s (Ioi 0)) {N₀ κ A₁ A₂ K₁ K₂ K₂' : ℝ}
    (hA₁ : 0 < A₁) (hA : A₁ < A₂) (hκ : 0 < κ) (hN : 0 < N₀ + κ * A₁)
    (h₁ : E.IsEq A₁ (N₀ + κ * A₁) K₁) (h₂ : E.IsEq A₂ (N₀ + κ * A₂) K₂)
    (h₂' : E.IsEq A₂ (N₀ + κ * A₁) K₂') : K₁ < K₂' ∧ K₂' < K₂ :=
  ⟨E.K_strictMono_A hA₁ hA hN h₁ h₂', E.K_strictMono_N hs (hA₁.trans hA) hN (by nlinarith) h₂' h₂⟩

/-- **Existence and uniqueness.** If the excess return `A f'(K) − R s(N/K)`
is positive at `K_lo` and negative at `K_hi`, and `f'`, `s` are continuous,
there is a unique equilibrium. -/
theorem existsUnique_K (hf'c : ContinuousOn E.f' (Ioi 0)) (hsc : ContinuousOn E.s (Ioi 0))
    {A N K_lo K_hi : ℝ} (hA : 0 < A) (hN : 0 < N) (hlo : 0 < K_lo) (hle : K_lo ≤ K_hi)
    (h_lo : E.R * E.s (N / K_lo) < A * E.f' K_lo)
    (h_hi : A * E.f' K_hi < E.R * E.s (N / K_hi)) : ∃! K, E.IsEq A N K := by
  set g : ℝ → ℝ := fun K => A * E.f' K - E.R * E.s (N / K)
  have hsub : Icc K_lo K_hi ⊆ Ioi 0 := fun K hK => hlo.trans_le hK.1
  have hgc : ContinuousOn g (Icc K_lo K_hi) := by
    apply ContinuousOn.sub (continuousOn_const.mul (hf'c.mono hsub))
    apply continuousOn_const.mul
    apply hsc.comp (continuousOn_const.div continuousOn_id fun K hK => (hsub hK).ne')
    intro K hK; exact div_pos hN (hsub hK)
  have h0 : (0 : ℝ) ∈ Icc (g K_hi) (g K_lo) := ⟨by simp only [g]; linarith, by simp only [g]; linarith⟩
  obtain ⟨K, hK, hgK⟩ := intermediate_value_Icc' hle hgc h0
  have hKpos : 0 < K := hsub hK
  refine ⟨K, ⟨hKpos, by simp only [g] at hgK; linarith⟩, fun K' hK' => ?_⟩
  -- uniqueness: `g` is strictly decreasing
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hf := E.hf'anti (mem_Ioi.2 hK'.1) (mem_Ioi.2 hKpos) hlt
    have hs' : E.s (N / K') ≤ E.s (N / K) :=
      E.hs (mem_Ioi.2 (div_pos hN hKpos)) (mem_Ioi.2 (div_pos hN hK'.1))
        (div_le_div_of_nonneg_left hN.le hK'.1 hlt.le)
    have := mul_lt_mul_of_pos_left hf hA
    have := mul_le_mul_of_nonneg_left hs' E.hR.le
    simp only [g] at hgK
    linarith [hK'.2]
  · have hf := E.hf'anti (mem_Ioi.2 hKpos) (mem_Ioi.2 hK'.1) hlt
    have hs' : E.s (N / K) ≤ E.s (N / K') :=
      E.hs (mem_Ioi.2 (div_pos hN hK'.1)) (mem_Ioi.2 (div_pos hN hKpos))
        (div_le_div_of_nonneg_left hN.le hKpos hlt.le)
    have := mul_lt_mul_of_pos_left hf hA
    have := mul_le_mul_of_nonneg_left hs' E.hR.le
    simp only [g] at hgK
    linarith [hK'.2]

end Env

/-- The premium schedule `s(x) = 1 + m/x` (`m > 0`) is strictly decreasing
in the net-worth ratio and at least one on `(0, ∞)`, so it satisfies the
hypotheses above. -/
theorem premium_example {m : ℝ} (hm : 0 < m) : StrictAntiOn (fun x : ℝ => 1 + m / x) (Ioi 0) := by
  intro x hx y hy hxy
  simp only
  have := div_lt_div_of_pos_left hm (mem_Ioi.1 hx) hxy
  linarith

theorem premium_example_ge {m : ℝ} (hm : 0 < m) {x : ℝ} (hx : 0 < x) : 1 ≤ 1 + m / x := by
  have := div_pos hm hx; linarith

end BGG
end Econ

end
