/-
# Moral hazard: the finite-outcome principal–agent problem

MWG §14.B (Props. 14.B.1–14.B.2, 14.B.4); Grossman–Hart (1983), Holmström (1979). A
risk-neutral principal hires an agent whose effort `e ∈ {low, high}` shifts the distribution
of a finite outcome `ω ∈ Ω`: `fL`, `fH` are lotteries over `Ω`, and `π ω` is the principal's
gross profit. Effort costs the agent `gL < gH` utils; the agent's outside option is `ū`.

Contracts are described by the **utility** `ν ω` they give in each outcome (the
Grossman–Hart parametrization). Paying `ν` utils costs the principal `φ ν` money, where `φ`
is the inverse of the agent's Bernoulli utility: increasing, and convex when the agent is
risk averse (linear when risk neutral).

Main results:
* `fullInsurance_optimal` (MWG Prop. 14.B.2, observable effort): any contract that gives the
  agent at least `ū + g` in expectation under `f` costs at least the constant contract
  `φ(ū + g)`: with observable effort the risk-averse agent is fully insured. Convexity and
  monotonicity of `φ = u⁻¹` are required only on an interval `U` of utility levels.
* `implementsHigh_nonconstant`, `implementsHigh_cost_gt` (MWG Prop. 14.B.4, hidden effort):
  if `fH` has full support, a contract implementing high effort cannot be constant, and if
  `φ` is strictly convex it costs strictly more than the first-best `φ(ū + gH)`.
* `sellTheFirm` (MWG Prop. 14.B.1): with a risk-neutral agent (`φ = id`), selling the firm
  (`w ω = π ω − α`) implements high effort whenever it is efficient, meets the participation
  constraint with equality, and gives the principal the first-best profit.
-/
module

public import EconLean.Uncertainty.VNM
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

namespace Econ

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Expectation of `x` under the outcome distribution `f`. -/
def outcomeMean (f x : Ω → ℝ) : ℝ := ∑ ω, f ω * x ω

/-- A utility contract `ν` **implements high effort** with participation level `ū`: the agent
accepts (IR) and prefers high to low effort (IC). -/
def ImplementsHigh (fL fH : Ω → ℝ) (gL gH ū : ℝ) (ν : Ω → ℝ) : Prop :=
  ū ≤ outcomeMean fH ν - gH ∧ outcomeMean fL ν - gL ≤ outcomeMean fH ν - gH

theorem outcomeMean_const {f : Ω → ℝ} (hf : f ∈ lotteries Ω) (k : ℝ) :
    outcomeMean f (fun _ => k) = k := by
  simp [outcomeMean, ← Finset.sum_mul, hf.2]

/-- **Observable effort: full insurance is optimal** (MWG Prop. 14.B.2). Let `U` be an
interval containing the agent's attainable utility levels (the range of `u`), on which
`φ = u⁻¹` is convex and monotone. Any contract with utilities `ν ω ∈ U` giving expected
utility at least `ū + g ∈ U` under `f` costs at least `φ(ū + g)`, the cost of the constant
contract. (Only `U` matters, so CARA utility, with range `(−∞, 0)`, and `√w`, with range
`[0, ∞)`, are covered.) -/
theorem fullInsurance_optimal {f : Ω → ℝ} (hf : f ∈ lotteries Ω) {U : Set ℝ} {φ : ℝ → ℝ}
    (hconv : ConvexOn ℝ U φ) (hmono : MonotoneOn φ U) {ν : Ω → ℝ} (hν : ∀ ω, ν ω ∈ U)
    {ū g : ℝ} (hU : ū + g ∈ U)
    (hIR : ū + g ≤ outcomeMean f ν) : φ (ū + g) ≤ outcomeMean f (fun ω => φ (ν ω)) := by
  have hJ := hconv.map_sum_le (t := univ) (w := f) (p := ν) (fun ω _ => hf.1 ω) hf.2
    (fun ω _ => hν ω)
  have hmem : ∑ ω, f ω • ν ω ∈ U :=
    hconv.1.sum_mem (fun ω _ => hf.1 ω) hf.2 (fun ω _ => hν ω)
  simp only [smul_eq_mul] at hJ hmem
  exact (hmono hU hmem hIR).trans hJ

/-- **Hidden effort: incentives require risk.** If `gL < gH` and the outcome distributions
are lotteries, no constant contract implements high effort. -/
theorem implementsHigh_nonconstant {fL fH : Ω → ℝ} (hfL : fL ∈ lotteries Ω)
    (hfH : fH ∈ lotteries Ω) {gL gH ū k : ℝ} (hg : gL < gH) :
    ¬ ImplementsHigh fL fH gL gH ū (fun _ => k) := by
  rintro ⟨-, hIC⟩
  rw [outcomeMean_const hfL, outcomeMean_const hfH] at hIC
  linarith

/-- **Hidden effort is costly** (MWG Prop. 14.B.4). If the agent is strictly risk averse
(`φ = u⁻¹` strictly convex and monotone on an interval `U` containing the attainable utility
levels), `fH` has full support and `gL < gH`, every contract with utilities in `U`
implementing high effort costs strictly more than the first-best `φ(ū + gH)`. -/
theorem implementsHigh_cost_gt {fL fH : Ω → ℝ} (hfL : fL ∈ lotteries Ω)
    (hfH : fH ∈ lotteries Ω) (hfull : ∀ ω, 0 < fH ω) {U : Set ℝ} {φ : ℝ → ℝ}
    (hconv : StrictConvexOn ℝ U φ) (hmono : MonotoneOn φ U) {gL gH ū : ℝ} (hg : gL < gH)
    (hU : ū + gH ∈ U) {ν : Ω → ℝ} (hν : ∀ ω, ν ω ∈ U)
    (h : ImplementsHigh fL fH gL gH ū ν) :
    φ (ū + gH) < outcomeMean fH (fun ω => φ (ν ω)) := by
  -- `ν` is not constant, so Jensen's inequality is strict.
  have hnc : ∃ j ∈ (univ : Finset Ω), ∃ k ∈ (univ : Finset Ω), ν j ≠ ν k := by
    by_contra hc
    push Not at hc
    obtain ⟨ω₀⟩ : Nonempty Ω := by
      by_contra hE
      rw [not_nonempty_iff] at hE
      have := hfH.2
      simp at this
    have : ν = fun _ => ν ω₀ := funext fun ω => hc ω (mem_univ _) ω₀ (mem_univ _)
    exact implementsHigh_nonconstant hfL hfH hg (this ▸ h)
  have hJ := hconv.map_sum_lt (t := univ) (w := fH) (p := ν) (fun ω _ => hfull ω) hfH.2
    (fun ω _ => hν ω) hnc
  have hmem : ∑ ω, fH ω • ν ω ∈ U :=
    hconv.1.sum_mem (fun ω _ => (hfull ω).le) hfH.2 (fun ω _ => hν ω)
  simp only [smul_eq_mul] at hJ hmem
  have hIR : ū + gH ≤ ∑ ω, fH ω * ν ω := by
    have := h.1; simp only [outcomeMean] at this; linarith
  exact (hmono hU hmem hIR).trans_lt hJ

/-- **Risk-neutral agent: sell the firm** (MWG Prop. 14.B.1). With `φ = id`, if high effort
is efficient (`E_L[π] − gL ≤ E_H[π] − gH`), the contract `w = π − α` with
`α = E_H[π] − gH − ū` implements high effort, leaves the agent exactly `ū`, and gives the
principal the first-best profit `E_H[π] − gH − ū`. -/
theorem sellTheFirm {fL fH : Ω → ℝ} (hfL : fL ∈ lotteries Ω) (hfH : fH ∈ lotteries Ω)
    {π : Ω → ℝ} {gL gH ū : ℝ}
    (heff : outcomeMean fL π - gL ≤ outcomeMean fH π - gH) :
    let α := outcomeMean fH π - gH - ū
    ImplementsHigh fL fH gL gH ū (fun ω => π ω - α) ∧
      outcomeMean fH (fun ω => π ω - α) - gH = ū ∧
      outcomeMean fH (fun ω => π ω - (π ω - α)) = outcomeMean fH π - gH - ū := by
  intro α
  have hsub : ∀ f : Ω → ℝ, f ∈ lotteries Ω →
      outcomeMean f (fun ω => π ω - α) = outcomeMean f π - α := fun f hf => by
    simp only [outcomeMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf.2, one_mul]
  have hconst : outcomeMean fH (fun ω => π ω - (π ω - α)) = α := by
    simp only [sub_sub_cancel]
    exact outcomeMean_const hfH α
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hsub fH hfH]; simp only [α]; linarith
  · rw [hsub fL hfL, hsub fH hfH]; linarith
  · rw [hsub fH hfH]; simp only [α]; ring
  · rw [hconst]

end Econ
