/-
# Cost minimization, conditional factor demand, Shephard's lemma for cost

MWG §5.C (Prop. 5.C.2, Shephard's lemma for the cost function) and the
link between profit maximization and cost minimization.

**The economics.** A single-output firm with production function
`f : ℝᴸ₊ → ℝ` (inputs `z ≥ 0` give output `f z`) facing input prices `w`
solves the **cost minimization problem**

    c(w, q) = min { w · z | z ≥ 0, f z ≥ q }.

The minimizers are the **conditional factor demands** `z(w, q)`.

**Shared abstraction.** This is *the same problem* as the consumer's
expenditure minimization (MWG §3.E), with `f` in place of `u`, input
prices `w` in place of `p`, and output target `q` in place of `ū`. So we
define `costFunction f = expenditure f` and `factorDemand f = hicksian f`,
and every duality result proved for the consumer transfers verbatim:
Shephard's lemma, homogeneity, concavity. This is a small instance of the
unification programme (PLAN §7): one optimization result, two economic
readings. MWG makes the same remark after Prop. 5.C.2.

**Junk values.** `costFunction` is a real `sInf`, so it is `0` where MWG
would write `+∞` (output `q` infeasible) and also when costs are unbounded
below (some `wᵢ < 0`). Every theorem whose content depends on the value
assumes feasibility, nonnegative prices or an attained minimum.
`costFunction_smul` and `costFunction_crs` hold unconditionally, but
off the feasible set only as `0 = α · 0`.
-/
module

public import EconLean.Producer.Production

@[expose] public section

namespace Econ

open Filter Topology Set
open scoped Pointwise

variable {ι : Type*} [Fintype ι]

/-- The **cost function** `c(w, q) = inf { w · z | z ≥ 0, f z ≥ q }`. It is
the expenditure function of `f` (same problem, different names). -/
noncomputable def costFunction (f : (ι → ℝ) → ℝ) (w : ι → ℝ) (q : ℝ) : ℝ :=
  expenditure f w q

/-- **Conditional factor demand** `z(w, q)`: cheapest input bundles that
produce at least `q`. -/
def factorDemand (f : (ι → ℝ) → ℝ) (w : ι → ℝ) (q : ℝ) : Set (ι → ℝ) :=
  hicksian f w q

variable {f : (ι → ℝ) → ℝ}

/-- Unfolded membership in conditional factor demand. -/
theorem mem_factorDemand {w : ι → ℝ} {q : ℝ} {z : ι → ℝ} :
    z ∈ factorDemand f w q ↔
      (0 ≤ z ∧ q ≤ f z) ∧ ∀ z', 0 ≤ z' ∧ q ≤ f z' → cost w z ≤ cost w z' := Iff.rfl

/-- At a cost-minimizing bundle, `c(w, q) = w · z`. -/
theorem costFunction_eq {w : ι → ℝ} {q : ℝ} {z : ι → ℝ} (hz : z ∈ factorDemand f w q) :
    costFunction f w q = cost w z :=
  expenditure_eq hz

/-- **Conditional factor demand is homogeneous of degree zero in `w`**
(MWG Prop. 5.C.2 (iii)). -/
theorem factorDemand_smul {α : ℝ} (hα : 0 < α) (w : ι → ℝ) (q : ℝ) :
    factorDemand f (α • w) q = factorDemand f w q :=
  hicksian_smul hα w q

/-- **The cost function is homogeneous of degree one in `w`**
(MWG Prop. 5.C.2 (i)). -/
theorem costFunction_smul {α : ℝ} (hα : 0 ≤ α) (w : ι → ℝ) (q : ℝ) :
    costFunction f (α • w) q = α * costFunction f w q := by
  unfold costFunction expenditure
  rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg hα, ← image_smul, image_image]
  simp only [cost_smul_left, smul_eq_mul]

/-- **The cost function is concave in `w`** (MWG Prop. 5.C.2 (iii)), on
nonnegative input prices, whenever output `q` is feasible. No cost-minimizing
bundle needs to exist: `c(·, q)` is an infimum of linear functions of `w`. -/
theorem concaveOn_costFunction {q : ℝ} (hfeas : ∃ z, 0 ≤ z ∧ q ≤ f z) :
    ConcaveOn ℝ {w : ι → ℝ | 0 ≤ w} (fun w => costFunction f w q) := by
  obtain ⟨z₀, hz₀, hq⟩ := hfeas
  have hbdd : ∀ w : ι → ℝ, 0 ≤ w → BddBelow (cost w '' upperSet f q) := fun w hw =>
    ⟨0, by rintro _ ⟨z, hz, rfl⟩; exact cost_nonneg hw hz.1⟩
  refine ⟨fun w hw w' hw' a b ha hb _ => ?_, fun w hw w' hw' a b ha hb _ => ?_⟩
  · exact add_nonneg (smul_nonneg ha (show (0 : ι → ℝ) ≤ w from hw))
      (smul_nonneg hb (show (0 : ι → ℝ) ≤ w' from hw'))
  · simp only [smul_eq_mul, costFunction, expenditure]
    refine le_csInf ⟨_, z₀, ⟨hz₀, hq⟩, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [cost_add_left, cost_smul_left, cost_smul_left]
    exact add_le_add (mul_le_mul_of_nonneg_left (csInf_le (hbdd w hw) ⟨z, hz, rfl⟩) ha)
      (mul_le_mul_of_nonneg_left (csInf_le (hbdd w' hw') ⟨z, hz, rfl⟩) hb)

/-- Superadditivity form of concavity, at prices where cost minimizers
exist: `a c(w) + b c(w') ≤ c(a w + b w')` for `a, b ≥ 0`. -/
theorem costFunction_concave {w w' : ι → ℝ} {q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {z z' zm : ι → ℝ} (hz : z ∈ factorDemand f w q) (hz' : z' ∈ factorDemand f w' q)
    (hzm : zm ∈ factorDemand f (a • w + b • w') q) :
    a * costFunction f w q + b * costFunction f w' q ≤ costFunction f (a • w + b • w') q :=
  expenditure_concave ha hb hz hz' hzm

/-- **Shephard's lemma for cost** (MWG Prop. 5.C.2 (vi)). If `z ∈ z(w, q)`
with `w ≫ 0` and `c(·, q)` is differentiable at `w` with derivative `C'`,
then `∂c/∂wⱼ = zⱼ`: the input-price gradient of cost is factor demand. -/
theorem shephard_cost [DecidableEq ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i) {q : ℝ} {z : ι → ℝ}
    (hz : z ∈ factorDemand f w q) {C' : (ι → ℝ) →L[ℝ] ℝ}
    (hC : HasFDerivAt (fun w' => costFunction f w' q) C' w) (j : ι) :
    C' (Pi.single j 1) = z j :=
  shephard_partial hw hz hC j

/-- **Cost is nondecreasing in output** (MWG Prop. 5.C.2 (ii), weak
form): for `w ≥ 0`, if `q'` is achievable and `q ≤ q'`, then
`c(w, q) ≤ c(w, q')`. -/
theorem costFunction_mono {w : ι → ℝ} (hw : 0 ≤ w) {q q' : ℝ} (hqq : q ≤ q')
    (hne : ∃ z, 0 ≤ z ∧ q' ≤ f z) : costFunction f w q ≤ costFunction f w q' := by
  obtain ⟨z, hz0, hz⟩ := hne
  unfold costFunction expenditure
  refine csInf_le_csInf ⟨0, ?_⟩ ⟨cost w z, z, ⟨hz0, hz⟩, rfl⟩ ?_
  · rintro _ ⟨y, hy, rfl⟩; exact cost_nonneg hw hy.1
  · exact image_mono fun y hy => ⟨hy.1, hqq.trans hy.2⟩

/-- **Constant returns ⟹ linear cost in output** (MWG Prop. 5.C.2 (vii),
CRS case). If `f` is homogeneous of degree one, `c(w, q) = q · c(w, 1)`
for `q > 0`. Holds with no boundedness assumption. -/
theorem costFunction_crs (hf : ∀ t : ℝ, 0 < t → ∀ z, 0 ≤ z → f (t • z) = t * f z)
    (w : ι → ℝ) {q : ℝ} (hq : 0 < q) : costFunction f w q = q * costFunction f w 1 := by
  unfold costFunction expenditure
  -- The `q`-isoquant's upper set is `q •` the unit one.
  have hset : upperSet f q = q • upperSet f 1 := by
    ext z
    constructor
    · rintro ⟨hz0, hz⟩
      refine ⟨q⁻¹ • z, ⟨?_, ?_⟩, ?_⟩
      · exact smul_nonneg (inv_nonneg.2 hq.le) hz0
      · rw [hf _ (inv_pos.2 hq) z hz0]
        rw [le_inv_mul_iff₀ hq, mul_one]; exact hz
      · simp [smul_smul, hq.ne']
    · rintro ⟨z', ⟨hz0, hz⟩, rfl⟩
      refine ⟨smul_nonneg hq.le hz0, ?_⟩
      rw [hf _ hq _ hz0]
      nlinarith
  have himg : cost w '' (q • upperSet f 1) = q • (cost w '' upperSet f 1) := by
    rw [← image_smul, ← image_smul, image_image, image_image]
    simp only [cost_smul_right, smul_eq_mul]
  rw [hset, himg, Real.sInf_smul_of_nonneg hq.le, smul_eq_mul]

/-! ### Profit maximization implies cost minimization -/

/-- **Profit maximization ⟹ cost minimization.** If, at output price
`p ≥ 0` and input prices `w`, the input bundle `z*` maximizes profit
`p f(z) - w · z` over `z ≥ 0`, then `z*` minimizes the cost of producing
its own output `f(z*)`. This is why a profit-maximizing firm can be studied
in two steps: cost minimization, then the choice of output (MWG §5.C). -/
theorem factorDemand_of_profitMax {p : ℝ} (hp : 0 ≤ p) {w z : ι → ℝ} (hz0 : 0 ≤ z)
    (hmax : ∀ z', 0 ≤ z' → p * f z' - cost w z' ≤ p * f z - cost w z) :
    z ∈ factorDemand f w (f z) := by
  refine ⟨⟨hz0, le_rfl⟩, fun z' ⟨hz'0, hz'⟩ => ?_⟩
  have := hmax z' hz'0
  nlinarith [mul_le_mul_of_nonneg_left hz' hp]

/-! ### Non-vacuity -/

/-- **Witness for Shephard's hypotheses (cost).** With the linear
technology `f z = z₀` (only input `0` matters) and `w ≫ 0`, the bundle
`q · e₀` is cost-minimizing, and `c(w', q) = w'₀ q` near `w` is
differentiable, so Shephard's lemma applies and recovers `z(w, q) = q e₀`. -/
example (w : Fin 2 → ℝ) (hw : ∀ i, 0 < w i) (q : ℝ) (hq : 0 ≤ q) :
    (q • Pi.single 0 1 : Fin 2 → ℝ) ∈ factorDemand (fun z : Fin 2 → ℝ => z 0) w q ∧
      HasFDerivAt (fun w' => costFunction (fun z : Fin 2 → ℝ => z 0) w' q)
        (costCLM (q • Pi.single 0 1)) w := by
  -- At any `w' ≫ 0`, `q e₀` is the cheapest way to get `z₀ ≥ q`.
  have hmin : ∀ w' : Fin 2 → ℝ, (∀ i, 0 < w' i) →
      (q • Pi.single 0 1 : Fin 2 → ℝ) ∈ factorDemand (fun z : Fin 2 → ℝ => z 0) w' q := by
    intro w' hw'
    refine ⟨⟨?_, by simp⟩, fun z' ⟨hz'0, hz'⟩ => ?_⟩
    · intro i; fin_cases i <;> simp [hq]
    · show cost w' _ ≤ cost w' z'
      have hz'' : q ≤ z' 0 := hz'
      simp [cost, Fin.sum_univ_two, Pi.single_apply]
      nlinarith [mul_le_mul_of_nonneg_left hz'' (hw' 0).le, mul_nonneg (hw' 1).le (hz'0 1)]
  refine ⟨hmin w hw, ?_⟩
  refine (costCLM _).hasFDerivAt.congr_of_eventuallyEq ?_
  filter_upwards [eventually_pos hw] with w' hw'
  rw [costFunction_eq (hmin w' hw'), costCLM_apply]

end Econ
