/-
# Envelope results: Shephard's lemma, Roy's identity, the Slutsky equation

MWG §3.G (Props. 3.G.1, 3.G.3, 3.G.4).

**The economics.** These are the "derivative" results of consumer theory:
* **Shephard's lemma**: `∂e/∂pⱼ (p, ū) = hⱼ(p, ū)`. The price gradient of
  the expenditure function is Hicksian demand.
* **Roy's identity**: `xⱼ(p, w) = -(∂v/∂pⱼ) / (∂v/∂w)`.
* **Slutsky equation**: `∂hᵢ/∂pⱼ = ∂xᵢ/∂pⱼ + xⱼ · ∂xᵢ/∂w`. A compensated
  price effect equals the uncompensated effect plus an income effect.

**The proof idea (envelope theorem without the calculus mess).**
For Shephard: fix a Hicksian bundle `h` at `p`. For every other price `q`,
`h` still reaches `ū`, so `e(q) ≤ q · h`, with equality at `q = p`. Hence the
function `g(q) = q · h - e(q)` has a *minimum* at `p`. If `e` is
differentiable there, its derivative must vanish (Fermat's theorem,
`IsLocalMin.hasFDerivAt_eq_zero` in Mathlib), so `De(p) = (δ ↦ δ · h)`.

Notice what this argument does *not* need: no differentiability of `h`, and
not even uniqueness of `h`. In fact it *proves* that if `e` is differentiable
at `p`, every Hicksian bundle is the same (all equal the gradient).

Roy's identity is the same trick applied to `q ↦ v(q, q · x)`.

**The Lean.** Derivatives in Mathlib are *Fréchet derivatives*: we write
`HasFDerivAt f L a` for "f is differentiable at a with derivative the
continuous linear map L". A partial derivative `∂f/∂pⱼ` is `L` applied to
the j-th basis vector `Pi.single j 1`. We assume differentiability as a
hypothesis, exactly as MWG does.
-/
module

public import EconLean.Consumer.Duality
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace Econ

open Filter Topology Set

variable {ι : Type*} [Fintype ι]

/-! ### Cost as a continuous linear map in prices -/

/-- `δ ↦ δ · x`, packaged as a continuous linear map (a finite sum of
coordinate projections). -/
noncomputable def costCLM (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, x i • ContinuousLinearMap.proj i

@[simp] theorem costCLM_apply (x δ : ι → ℝ) : costCLM x δ = cost δ x := by
  simp [costCLM, cost, mul_comm]

/-- The cost of the j-th unit vector is the j-th quantity. -/
theorem cost_single [DecidableEq ι] (x : ι → ℝ) (j : ι) : cost (Pi.single j 1) x = x j := by
  simp [cost, Pi.single_apply]

/-- Near a strictly positive price vector, prices stay strictly positive. -/
theorem eventually_pos {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    ∀ᶠ q in 𝓝 p, ∀ i, 0 < q i :=
  eventually_all.2 fun i =>
    (continuous_apply i).continuousAt.eventually (lt_mem_nhds (hp i))

variable {u : (ι → ℝ) → ℝ}

/-! ### Shephard's lemma -/

/-- For nonnegative prices, any bundle reaching `ū` bounds expenditure. -/
theorem expenditure_le {q : ι → ℝ} (hq : 0 ≤ q) {ū : ℝ} {x : ι → ℝ}
    (hx : x ∈ upperSet u ū) : expenditure u q ū ≤ cost q x :=
  csInf_le ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact cost_nonneg hq hy.1⟩ (mem_image_of_mem _ hx)

/-- **Shephard's lemma** (MWG Prop. 3.G.1). If `h` is a Hicksian bundle at
`(p, ū)` and `e(·, ū)` is differentiable at `p ≫ 0` with derivative `E'`,
then `E' δ = δ · h` for every direction `δ`. -/
theorem shephard {p : ι → ℝ} (hp : ∀ i, 0 < p i) {ū : ℝ} {h : ι → ℝ}
    (hh : h ∈ hicksian u p ū) {E' : (ι → ℝ) →L[ℝ] ℝ}
    (hE : HasFDerivAt (fun q => expenditure u q ū) E' p) :
    ∀ δ, E' δ = cost δ h := by
  -- `g q = q · h - e(q, ū)` has a local minimum (of value 0) at `p`.
  have hmin : IsLocalMin (fun q => cost q h - expenditure u q ū) p := by
    filter_upwards [eventually_pos hp] with q hq
    rw [expenditure_eq hh, sub_self, sub_nonneg]
    exact expenditure_le (fun i => (hq i).le) hh.1
  -- Its derivative is `costCLM h - E'`, which therefore vanishes.
  have hg : HasFDerivAt (fun q => cost q h - expenditure u q ū) (costCLM h - E') p := by
    have hc : HasFDerivAt (fun q => cost q h) (costCLM h) p :=
      (costCLM h).hasFDerivAt.congr_of_eventuallyEq
        (Eventually.of_forall fun q => (costCLM_apply h q).symm)
    exact hc.sub hE
  have hzero := hmin.hasFDerivAt_eq_zero hg
  intro δ
  have := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L δ) hzero
  simp at this
  linarith

/-- Shephard's lemma, coordinate form: `∂e/∂pⱼ = hⱼ`. -/
theorem shephard_partial [DecidableEq ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {ū : ℝ} {h : ι → ℝ}
    (hh : h ∈ hicksian u p ū) {E' : (ι → ℝ) →L[ℝ] ℝ}
    (hE : HasFDerivAt (fun q => expenditure u q ū) E' p) (j : ι) :
    E' (Pi.single j 1) = h j := by
  rw [shephard hp hh hE, cost_single]

/-- A corollary that is surprising at first: if `e` is differentiable at `p`,
Hicksian demand is a *single* bundle. -/
theorem hicksian_unique [DecidableEq ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {ū : ℝ} {h h' : ι → ℝ}
    (hh : h ∈ hicksian u p ū) (hh' : h' ∈ hicksian u p ū) {E' : (ι → ℝ) →L[ℝ] ℝ}
    (hE : HasFDerivAt (fun q => expenditure u q ū) E' p) : h = h' := by
  funext j
  rw [← shephard_partial hp hh hE j, shephard_partial hp hh' hE j]

/-! ### Roy's identity -/

/-- `v(q, q · x) ≥ u x` for any `q ≫ 0` and `x ≥ 0`: `x` is affordable at
wealth `q · x`. (Uses continuity of `u` to know `v` is a genuine maximum.) -/
theorem le_indirectUtility (hu : Continuous u) {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    {x : ι → ℝ} (hx : 0 ≤ x) : u x ≤ indirectUtility u q (cost q x) := by
  obtain ⟨y, hy⟩ := demand_nonempty hu hq (cost_nonneg (fun i => (hq i).le) hx)
  rw [indirectUtility_eq hy]
  exact hy.2 x ⟨hx, le_rfl⟩

/-- **Roy's identity** (MWG Prop. 3.G.4), derivative form. Let `x` be demanded
at `(p, w)` with locally nonsatiated, continuous utility. If `v` is
differentiable at `(p, w)` with derivative `V'`, then for every direction `δ`,

    V' (δ, δ · x) = 0,

i.e. raising prices by `δ` while compensating wealth by `δ · x` leaves
utility unchanged to first order. -/
theorem roy (hu : Continuous u) (hlns : LocallyNonsatiated (prefOf u))
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {w : ℝ} {x : ι → ℝ}
    (hx : x ∈ demand (prefOf u) p w) {V' : ((ι → ℝ) × ℝ) →L[ℝ] ℝ}
    (hV : HasFDerivAt (fun pw : (ι → ℝ) × ℝ => indirectUtility u pw.1 pw.2) V' (p, w)) :
    ∀ δ, V' (δ, cost δ x) = 0 := by
  have hwal : cost p x = w := walras_law hlns hx
  -- `φ q = v(q, q · x)` has a local minimum at `p`, with value `u x`.
  set φ : (ι → ℝ) → ℝ := fun q => indirectUtility u q (cost q x) with hφ
  have hmin : IsLocalMin φ p := by
    filter_upwards [eventually_pos hp] with q hq
    simp only [hφ, hwal, indirectUtility_eq hx]
    exact le_indirectUtility hu hq hx.1.1
  -- Chain rule: `Dφ(p) δ = V' (δ, δ · x)`.
  have hin : HasFDerivAt (fun q : ι → ℝ => (q, cost q x))
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (costCLM x)) p := by
    have h2 : HasFDerivAt (fun q => cost q x) (costCLM x) p :=
      (costCLM x).hasFDerivAt.congr_of_eventuallyEq
        (Eventually.of_forall fun q => (costCLM_apply x q).symm)
    exact (hasFDerivAt_id p).prodMk h2
  have hV' : HasFDerivAt (fun pw : (ι → ℝ) × ℝ => indirectUtility u pw.1 pw.2) V'
      (p, cost p x) := by rwa [hwal]
  have hφd' := hV'.comp p hin
  have hφd : HasFDerivAt φ (V'.comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (costCLM x))) p :=
    hφd'
  have hzero := hmin.hasFDerivAt_eq_zero hφd
  intro δ
  have := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ => L δ) hzero
  simpa using this

/-- **Roy's identity**, textbook form: `xⱼ · ∂v/∂w = -∂v/∂pⱼ`. Dividing by
`∂v/∂w ≠ 0` gives `xⱼ = -(∂v/∂pⱼ)/(∂v/∂w)`. -/
theorem roy_partial [DecidableEq ι] (hu : Continuous u) (hlns : LocallyNonsatiated (prefOf u))
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {w : ℝ} {x : ι → ℝ}
    (hx : x ∈ demand (prefOf u) p w) {V' : ((ι → ℝ) × ℝ) →L[ℝ] ℝ}
    (hV : HasFDerivAt (fun pw : (ι → ℝ) × ℝ => indirectUtility u pw.1 pw.2) V' (p, w))
    (j : ι) (hw : V' (0, 1) ≠ 0) :
    x j = -V' (Pi.single j 1, 0) / V' (0, 1) := by
  have h := roy hu hlns hp hx hV (Pi.single j 1)
  rw [cost_single] at h
  -- Split `(eⱼ, xⱼ) = (eⱼ, 0) + xⱼ • (0, 1)` and use linearity of `V'`.
  have hsplit : ((Pi.single j 1 : ι → ℝ), x j) = (Pi.single j 1, 0) + x j • ((0 : ι → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at h
  field_simp
  linarith

/-! ### The Slutsky equation -/

/-- **Slutsky equation** (MWG Prop. 3.G.3), derivative form.

Let `X (q, w)` be a (Walrasian) demand function, `H q` the Hicksian demand
at utility `ū`, and `E q` the expenditure function at `ū`. Suppose that near
`p` the duality identity `H q = X (q, E q)` holds, and that all three are
differentiable, with `E' δ = δ · H p` (Shephard's lemma, proved above).
Then for every direction `δ`,

    H' δ = X' (δ, 0) + (δ · H p) • X' (0, 1),

which in coordinates (`δ = eⱼ`) reads
`∂hᵢ/∂pⱼ = ∂xᵢ/∂pⱼ + hⱼ · ∂xᵢ/∂w`. -/
theorem slutsky {X : (ι → ℝ) × ℝ → (ι → ℝ)} {H : (ι → ℝ) → (ι → ℝ)} {E : (ι → ℝ) → ℝ}
    {p : ι → ℝ} {X' : ((ι → ℝ) × ℝ) →L[ℝ] (ι → ℝ)} {H' : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    {E' : (ι → ℝ) →L[ℝ] ℝ}
    (hdual : ∀ᶠ q in 𝓝 p, H q = X (q, E q))
    (hX : HasFDerivAt X X' (p, E p)) (hH : HasFDerivAt H H' p) (hE : HasFDerivAt E E' p)
    (hshep : ∀ δ, E' δ = cost δ (H p)) :
    ∀ δ, H' δ = X' (δ, 0) + cost δ (H p) • X' (0, 1) := by
  -- Chain rule for `q ↦ X (q, E q)`.
  have hcomp : HasFDerivAt (fun q => X (q, E q))
      (X'.comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod E')) p :=
    hX.comp p ((hasFDerivAt_id p).prodMk hE)
  -- `H` agrees with it near `p`, so the derivatives coincide.
  have heq : H' = X'.comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod E') :=
    hH.unique (hcomp.congr_of_eventuallyEq hdual)
  intro δ
  rw [heq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, hshep]
  -- `(δ, c) = (δ, 0) + c • (0, 1)`.
  have hsplit : (δ, cost δ (H p)) = (δ, 0) + cost δ (H p) • ((0 : ι → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul]

end Econ
