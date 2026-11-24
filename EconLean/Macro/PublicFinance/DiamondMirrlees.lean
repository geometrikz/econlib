/-
# Production efficiency (Diamond–Mirrlees)

Diamond and Mirrlees (1971), "Optimal Taxation and Public Production I:
Production Efficiency", AER; Atkinson–Stiglitz, *Lectures on Public
Economics*, Lecture 15; Mas-Colell–Whinston–Green, §22.

**Setting.** The government chooses consumer prices `q` in an admissible
set `Q` (equivalently commodity taxes; with a **full set of commodity taxes
and no untaxed profits**, consumers' choices and welfare depend on `q`
alone, so neither producer prices nor profit income appear). Private net
demand is `x(q)`, government consumption `g`, and the aggregate production
set `Z ⊆ ℝⁿ`. Social welfare is `W(q)`. The planner maximizes `W(q)` over
`q ∈ Q` subject to feasibility `x(q) + g ∈ Z` (`IsOptimum`); the government
budget constraint is implied by feasibility and Walras' law.

**Results.**
* `not_interior`: if demand is continuous at the optimum `q* ∈ interior Q`
  and every neighbourhood of `q*` contains prices with strictly higher
  welfare, aggregate production is not in the interior of `Z`, so it lies on
  the topological boundary (`mem_frontier`).
* `weakly_efficient`: with **free disposal** in `Z`, the optimum is
  (weakly) **production efficient**: no feasible production plan exceeds
  `x(q*) + g` in every good — even though consumer prices are distorted.
* `weakly_efficient_of_price_decrease`: the nonsatiation hypothesis holds if
  a small cut in the price of some good `k` strictly raises welfare at the
  optimum — in particular if this holds at every price vector (by Roy's
  identity, when good `k` is consumed and the welfare function is increasing
  in utilities), so it need not be checked at the unknown optimum.
* `example_one_good`: the hypotheses are jointly satisfiable.

Scope: demand and welfare depending on consumer prices alone corresponds to
constant returns or 100% profit taxation; "weakly efficient" means not
strictly dominated, i.e. on the frontier under free disposal.

**Deviations.** The welfare gain from a price cut is a hypothesis on `W`
(not derived from household utilities and Roy's identity); public and
private production are aggregated into one technology `Z`.
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

noncomputable section

namespace Econ
namespace DiamondMirrlees

open Set Filter Topology

variable {ι : Type*}

/-- `q*` is an optimum of the Diamond–Mirrlees problem over admissible
prices `Q`. -/
def IsOptimum (Q : Set (ι → ℝ)) (W : (ι → ℝ) → ℝ) (x : (ι → ℝ) → ι → ℝ) (g : ι → ℝ)
    (Z : Set (ι → ℝ)) (q : ι → ℝ) : Prop :=
  q ∈ Q ∧ x q + g ∈ Z ∧ ∀ q' ∈ Q, x q' + g ∈ Z → W q' ≤ W q

/-- **Production is not interior.** -/
theorem not_interior {Q : Set (ι → ℝ)} {W : (ι → ℝ) → ℝ} {x : (ι → ℝ) → ι → ℝ} {g : ι → ℝ}
    {Z : Set (ι → ℝ)} {q : ι → ℝ} (hopt : IsOptimum Q W x g Z q) (hQ : q ∈ interior Q)
    (hx : ContinuousAt x q) (hns : ∀ U ∈ 𝓝 q, ∃ q' ∈ U, W q < W q') :
    x q + g ∉ interior Z := by
  intro hint
  have hcont : ContinuousAt (fun q' => x q' + g) q := hx.add continuousAt_const
  have hU : (fun q' => x q' + g) ⁻¹' interior Z ∈ 𝓝 q :=
    hcont.preimage_mem_nhds (isOpen_interior.mem_nhds hint)
  obtain ⟨q', ⟨hq', hq'Q⟩, hW⟩ := hns _ (Filter.inter_mem hU (mem_interior_iff_mem_nhds.1 hQ))
  have := hopt.2.2 q' hq'Q (interior_subset hq')
  linarith

theorem mem_frontier {Q : Set (ι → ℝ)} {W : (ι → ℝ) → ℝ} {x : (ι → ℝ) → ι → ℝ} {g : ι → ℝ}
    {Z : Set (ι → ℝ)} {q : ι → ℝ} (hopt : IsOptimum Q W x g Z q) (hQ : q ∈ interior Q)
    (hx : ContinuousAt x q) (hns : ∀ U ∈ 𝓝 q, ∃ q' ∈ U, W q < W q') : x q + g ∈ frontier Z :=
  ⟨subset_closure hopt.2.1, not_interior hopt hQ hx hns⟩

/-- **Production efficiency** under free disposal: no feasible plan
strictly exceeds `x(q*) + g` in every good. -/
theorem weakly_efficient [Finite ι] {Q : Set (ι → ℝ)} {W : (ι → ℝ) → ℝ}
    {x : (ι → ℝ) → ι → ℝ} {g : ι → ℝ} {Z : Set (ι → ℝ)} {q : ι → ℝ}
    (hfd : ∀ z ∈ Z, ∀ z', z' ≤ z → z' ∈ Z) (hopt : IsOptimum Q W x g Z q)
    (hQ : q ∈ interior Q) (hx : ContinuousAt x q) (hns : ∀ U ∈ 𝓝 q, ∃ q' ∈ U, W q < W q') :
    ¬ ∃ z ∈ Z, ∀ i, x q i + g i < z i := by
  rintro ⟨z, hz, hlt⟩
  apply not_interior hopt hQ hx hns
  have hopen : IsOpen (Set.pi univ fun i => Iio (z i)) :=
    isOpen_set_pi finite_univ fun i _ => isOpen_Iio
  refine interior_maximal (fun w hw => hfd z hz w fun i => (hw i (mem_univ i)).le) hopen ?_
  exact fun i _ => hlt i

/-- **Production efficiency from price cuts.** If at every price vector a
small cut in the price of good `k` strictly raises welfare, the optimum is
production efficient. -/
theorem weakly_efficient_of_price_decrease [Finite ι] [DecidableEq ι] {Q : Set (ι → ℝ)}
    {W : (ι → ℝ) → ℝ} {x : (ι → ℝ) → ι → ℝ} {g : ι → ℝ} {Z : Set (ι → ℝ)} {q : ι → ℝ}
    (hfd : ∀ z ∈ Z, ∀ z', z' ≤ z → z' ∈ Z) (hopt : IsOptimum Q W x g Z q)
    (hQ : q ∈ interior Q) (hx : ContinuousAt x q) (k : ι)
    (hdec : ∀ᶠ ε in 𝓝[>] (0 : ℝ), W q < W (q - Pi.single k ε)) :
    ¬ ∃ z ∈ Z, ∀ i, x q i + g i < z i := by
  apply weakly_efficient hfd hopt hQ hx
  intro U hU
  have hc : Tendsto (fun ε : ℝ => q - Pi.single k ε) (𝓝[>] 0) (𝓝 q) := by
    have : Continuous (fun ε : ℝ => q - Pi.single k ε) :=
      continuous_const.sub (continuous_single (A := fun _ : ι => ℝ) k)
    have h := this.tendsto 0
    simp only [Pi.single_zero, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hε1, hε2⟩ := ((hc.eventually hU).and hdec).exists
  exact ⟨_, hε1, hε2⟩

/-- **Non-vacuity.** One good, demand `x(q) = 2 − q`, `g = 0`,
`Z = {z ≤ 1}` (free disposal), welfare `W(q) = −q`, `Q = univ`: the optimum
is `q = 1` and every hypothesis holds (price cuts raise welfare at every
price); production `x(1) = 1` is on the frontier (`example_efficient`). -/
theorem example_one_good :
    IsOptimum (ι := Unit) univ (fun q => -q ()) (fun q _ => 2 - q ()) 0 {z | z () ≤ 1}
      (fun _ => 1) ∧
    (∀ z ∈ ({z | z () ≤ 1} : Set (Unit → ℝ)), ∀ z', z' ≤ z → z' ∈ {z : Unit → ℝ | z () ≤ 1}) ∧
    ContinuousAt (fun (q : Unit → ℝ) (_ : Unit) => 2 - q ()) (fun _ => 1) ∧
    (∀ q₀ : Unit → ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (fun q : Unit → ℝ => -q ()) q₀ < (fun q : Unit → ℝ => -q ()) (q₀ - Pi.single () ε)) := by
  refine ⟨⟨mem_univ _, by simp; norm_num, fun q' _ h => ?_⟩, fun z hz z' hz' => ?_, ?_, ?_⟩
  · simp only [mem_ofPred_eq, add_zero] at h; linarith
  · exact (hz' ()).trans hz
  · exact (continuous_pi fun _ => continuous_const.sub (continuous_apply ())).continuousAt
  · intro q₀
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Pi.sub_apply, Pi.single_eq_same]
    linarith [mem_Ioi.1 hε]

/-- The theorem applies to the example. -/
theorem example_efficient :
    ¬ ∃ z ∈ ({z | z () ≤ 1} : Set (Unit → ℝ)), ∀ i, (fun _ => 2 - (1 : ℝ)) i + (0 : Unit → ℝ) i < z i := by
  obtain ⟨hopt, hfd, hx, hdec⟩ := example_one_good
  exact weakly_efficient_of_price_decrease hfd hopt (by rw [interior_univ]; exact mem_univ _) hx ()
    (by simpa using hdec (fun _ => 1))

end DiamondMirrlees
end Econ

end
