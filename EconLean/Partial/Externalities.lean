/-
# Externalities: the Coase theorem and Pigouvian taxes; partial-equilibrium welfare

MWG §10.D and §11.B. Two agents with quasilinear utility: agent 1 chooses an activity level
`h ∈ H` worth `φ₁ h` to her and `φ₂ h` to agent 2 (an externality); money transfers `T`
(from agent 2 to agent 1) are unrestricted.

Main results:
* `coase_pareto_iff`: an outcome `(h, T)` is Pareto efficient iff `h` maximizes the joint
  surplus `φ₁ + φ₂`, whatever the transfer.
* `coase_theorem` (MWG §11.B): whatever the initial assignment of rights (a disagreement level
  `h₀ ∈ H`), bargaining can reach an efficient and individually rational outcome, and every
  efficient outcome has the same, surplus-maximising activity level; only the transfer
  depends on the rights.
* `pigou_tax` (MWG §11.B): with concave private benefit, a per-unit tax equal to the
  marginal external harm at the optimum, `t = −φ₂'(h*)`, makes the efficient level `h*`
  privately optimal.
* `competitive_maximizes_surplus` (MWG Prop. 10.D.1): in a partial-equilibrium market with
  quasilinear consumers and price-taking firms, a competitive equilibrium maximizes
  Marshallian aggregate surplus among all feasible allocations.
-/
module

public import EconLean.Partial.PublicGoods

@[expose] public section

namespace Econ

open Finset Set Filter

section Coase

variable {H : Set ℝ} {φ₁ φ₂ : ℝ → ℝ}

/-- `(h, T)` is **Pareto efficient**: it is feasible (`h ∈ H`) and no feasible `(h', T')`
makes one agent strictly better off and the other no worse off. Agent 1 gets `φ₁ h + T`,
agent 2 gets `φ₂ h − T`. -/
def IsParetoExt (H : Set ℝ) (φ₁ φ₂ : ℝ → ℝ) (h T : ℝ) : Prop :=
  h ∈ H ∧ ¬ ∃ h' ∈ H, ∃ T', φ₁ h + T ≤ φ₁ h' + T' ∧ φ₂ h - T ≤ φ₂ h' - T' ∧
    (φ₁ h + T < φ₁ h' + T' ∨ φ₂ h - T < φ₂ h' - T')

/-- **Efficiency with transfers = surplus maximization.** -/
theorem coase_pareto_iff {h T : ℝ} :
    IsParetoExt H φ₁ φ₂ h T ↔ h ∈ H ∧ ∀ h' ∈ H, φ₁ h' + φ₂ h' ≤ φ₁ h + φ₂ h := by
  constructor
  · rintro ⟨hh, hP⟩
    refine ⟨hh, fun h' hh' => ?_⟩
    by_contra hlt
    push Not at hlt
    -- Split the gain equally.
    set g := φ₁ h' + φ₂ h' - (φ₁ h + φ₂ h)
    refine hP ⟨h', hh', φ₁ h + T - φ₁ h' + g / 2, ?_, ?_, Or.inl ?_⟩ <;>
      simp only [g] <;> linarith
  · rintro ⟨hh, hmax⟩
    refine ⟨hh, ?_⟩
    rintro ⟨h', hh', T', h1, h2, h3⟩
    have := hmax h' hh'
    rcases h3 with h3 | h3 <;> linarith

/-- **The Coase theorem** (MWG §11.B), in its efficiency form. Bargaining itself is not
modelled: the theorem says what any bargaining procedure that ends in an efficient and
individually rational agreement must deliver. For any assignment of rights, summarized by the
disagreement level `h₀ ∈ H`, if `hstar ∈ H` maximizes joint surplus then some transfer makes
`(hstar, T)` efficient and individually rational relative to `h₀`; and every efficient
outcome has a surplus-maximizing activity level, so the rights `h₀` can only affect the
transfer (this half does not involve `h₀`, which is the point: it is the same for every
assignment of rights). -/
theorem coase_theorem {hstar : ℝ} (hH : hstar ∈ H)
    (hmax : ∀ h' ∈ H, φ₁ h' + φ₂ h' ≤ φ₁ hstar + φ₂ hstar)
    (h₀ : ℝ) (hh₀ : h₀ ∈ H) :
    (∃ T, IsParetoExt H φ₁ φ₂ hstar T ∧ φ₁ h₀ ≤ φ₁ hstar + T ∧ φ₂ h₀ ≤ φ₂ hstar - T) ∧
      ∀ h T, h ∈ H → IsParetoExt H φ₁ φ₂ h T →
        φ₁ h + φ₂ h = φ₁ hstar + φ₂ hstar := by
  refine ⟨⟨φ₁ h₀ - φ₁ hstar, coase_pareto_iff.2 ⟨hH, hmax⟩, by linarith, ?_⟩,
    fun h T hh hP => ?_⟩
  · linarith [hmax h₀ hh₀]
  · exact le_antisymm (hmax h hh) ((coase_pareto_iff.1 hP).2 hstar hH)

end Coase

/-- **Pigouvian taxation** (MWG §11.B). Suppose agent 1's benefit `φ₁` is concave on `[0, ∞)`
and `hstar > 0` maximizes joint surplus `φ₁ + φ₂` on `[0, ∞)`. Then a per-unit tax equal to
the marginal external harm at the optimum, `t = −φ₂'(hstar)`, makes `hstar` optimal for
agent 1 alone. -/
theorem pigou_tax {φ₁ φ₂ : ℝ → ℝ} {hstar d₁ d₂ : ℝ} (hc : ConcaveOn ℝ (Ici 0) φ₁)
    (hpos : 0 < hstar) (hmax : ∀ h, 0 ≤ h → φ₁ h + φ₂ h ≤ φ₁ hstar + φ₂ hstar)
    (hd₁ : HasDerivAt φ₁ d₁ hstar) (hd₂ : HasDerivAt φ₂ d₂ hstar) :
    ∀ h, 0 ≤ h → φ₁ h - (-d₂) * h ≤ φ₁ hstar - (-d₂) * hstar := by
  have hloc : IsLocalMax (fun h => φ₁ h + φ₂ h) hstar :=
    Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun h hh => hmax h (le_of_lt hh)
  have hfoc := hloc.hasDerivAt_eq_zero (hd₁.add hd₂)
  intro h hh
  have := concaveOn_le_tangent hc (le_of_lt hpos) hh hd₁
  nlinarith

section PartialEq

variable {I J : Type*} [Fintype I] [Fintype J]

/-- **Competitive equilibrium** of a partial-equilibrium market (MWG §10.C): consumers `i`
with quasilinear benefit `φ i` buy `x i ≥ 0`, firms `j` with cost `c j` sell `q j ≥ 0`, all
taking the price `p` as given, and the market clears. -/
def IsPartialEq (φ : I → ℝ → ℝ) (c : J → ℝ → ℝ) (p : ℝ) (x : I → ℝ) (q : J → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ ∀ y, 0 ≤ y → φ i y - p * y ≤ φ i (x i) - p * x i) ∧
    (∀ j, 0 ≤ q j ∧ ∀ y, 0 ≤ y → p * y - c j y ≤ p * q j - c j (q j)) ∧
    ∑ i, x i = ∑ j, q j

/-- **The first welfare theorem in partial equilibrium** (MWG Prop. 10.D.1): a competitive
equilibrium maximizes Marshallian aggregate surplus `∑ φᵢ(xᵢ) − ∑ cⱼ(qⱼ)` over all
nonnegative allocations with total consumption equal to total production. -/
theorem competitive_maximizes_surplus {φ : I → ℝ → ℝ} {c : J → ℝ → ℝ} {p : ℝ} {x : I → ℝ}
    {q : J → ℝ} (h : IsPartialEq φ c p x q) (x' : I → ℝ) (q' : J → ℝ) (hx' : ∀ i, 0 ≤ x' i)
    (hq' : ∀ j, 0 ≤ q' j) (hfeas : ∑ i, x' i = ∑ j, q' j) :
    ∑ i, φ i (x' i) - ∑ j, c j (q' j) ≤ ∑ i, φ i (x i) - ∑ j, c j (q j) := by
  have hc := sum_le_sum fun i (_ : i ∈ Finset.univ) => (h.1 i).2 (x' i) (hx' i)
  have hf := sum_le_sum fun j (_ : j ∈ Finset.univ) => (h.2.1 j).2 (q' j) (hq' j)
  simp only [sum_sub_distrib, ← mul_sum] at hc hf
  rw [hfeas] at hc
  rw [h.2.2] at hc
  linarith

end PartialEq

end Econ
