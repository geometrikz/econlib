/-
# Lucas–Stokey with general utility: taxes depend only on the current shock

Lucas and Stokey (1983), JME, §3; Chari–Kehoe (1999), Prop. 2;
Ljungqvist–Sargent, *Recursive Macroeconomic Theory*, ch. 16.

**Setting.** As in `Econ.LucasStokey`, a finite set `ι` of date–event
histories with weights `w n = βᵗ π(sᵗ) > 0` and linear technology
`c = l − g`, but with general additively separable utility `u(c) − v(l)`
(`Prefs`: `u`, `v` twice strictly differentiable on `(0, ∞)`, so log and CRRA
are admissible). The primal-approach implementability constraint fixes
`Σ w (u'(c) c − v'(l) l)` (`implement`) at its value at the candidate
allocation (canonically `u'(c₀) b₀`; see Deviations), and the labour tax implementing an allocation is
`τ = 1 − v'(l)/u'(c)` (`tax`).

**Results.** At any local maximum of welfare `Σ w (u(c) − v(l))` on the
implementability set:
* `ramsey_foc`: at an interior optimum (`l > 0`, `c > 0`) there are
  multipliers `(a, b) ≠ 0` (Fritz John form: `a` on implementability, `b` on
  welfare), the **same at every history**, with `Φ_{a,b}(g n, l n) = 0` for
  every `n` (`Phi`). The
  allocation at a history is pinned down by the current spending shock and
  time-invariant multipliers alone.
* `history_independence`: hence if two histories have the same spending
  shock (at any dates, after any histories) and the node equation with these
  multipliers has a unique root with `l > 0`, `c > 0`, they have the same labour, consumption and tax — the
  Lucas–Stokey result that optimal taxes inherit the serial correlation of
  `g` but not history.
* `quasilinear_welfare`, `quasilinear_implement`, `nonvacuous`: the
  quasilinear isoelastic specification of `Econ.LucasStokey` is an instance,
  and its first-best Ramsey optimum satisfies the hypotheses.
* `distortionary_witness`: a genuinely distortionary Ramsey optimum
  (`γ = 1`, constant labour `c ∈ (1/2, 1)`, binding constraint, tax
  `1 − c > 0`), proved to be a (global) maximum on the implementability set.

**Deviations.** Every history enters symmetrically: the date-0 term
`u'(c₀) b₀` of the canonical problem (which makes date-0 policy special) is
omitted, as when initial debt is zero or the result is read for `t ≥ 1`.
Finite set of histories; interior optimum; uniqueness of the root of the node
equation is assumed rather than derived; the normal-form multipliers (`b = 1`
under a constraint qualification) are not stated separately.
-/
module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import EconLean.Macro.PublicFinance.LucasStokey

@[expose] public section

noncomputable section

namespace Econ
namespace LucasStokeyGeneral

open Finset

/-- Separable preferences `u(c) − v(l)` with first and second derivatives. -/
structure Prefs where
  u : ℝ → ℝ
  du : ℝ → ℝ
  d2u : ℝ → ℝ
  v : ℝ → ℝ
  dv : ℝ → ℝ
  d2v : ℝ → ℝ
  hu : ∀ x, 0 < x → HasStrictDerivAt u (du x) x
  hdu : ∀ x, 0 < x → HasStrictDerivAt du (d2u x) x
  hv : ∀ x, 0 < x → HasStrictDerivAt v (dv x) x
  hdv : ∀ x, 0 < x → HasStrictDerivAt dv (d2v x) x

namespace Prefs

variable (P : Prefs) {ι : Type*} [Fintype ι]

/-- Ramsey welfare. -/
def welfare (w g l : ι → ℝ) : ℝ := ∑ n, w n * (P.u (l n - g n) - P.v (l n))

/-- Left side of the implementability constraint. -/
def implement (w g l : ι → ℝ) : ℝ :=
  ∑ n, w n * (P.du (l n - g n) * (l n - g n) - P.dv (l n) * l n)

/-- The labour tax `τ = 1 − v'(l)/u'(c)`. -/
def tax (g l : ι → ℝ) (n : ι) : ℝ := 1 - P.dv (l n) / P.du (l n - g n)

/-- The node equation with multipliers `a` (implementability) and `b`
(welfare): the derivative of the Lagrangian in `l` at a history with shock
`g`. -/
def Phi (a b g l : ℝ) : ℝ :=
  a * (P.d2u (l - g) * (l - g) + P.du (l - g) - P.d2v l * l - P.dv l) +
    b * (P.du (l - g) - P.dv l)

theorem hasStrictFDerivAt_wsum (w : ι → ℝ) (φ : ι → ℝ → ℝ) (φ' : ι → ℝ) (l₀ : ι → ℝ)
    (h : ∀ n, HasStrictDerivAt (φ n) (φ' n) (l₀ n)) :
    HasStrictFDerivAt (fun l : ι → ℝ => ∑ n, w n * φ n (l n))
      (∑ n, (w n * φ' n) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) n) l₀ := by
  apply HasStrictFDerivAt.fun_sum (u := univ)
  intro n _
  have := (HasStrictDerivAt.const_mul (w n) (h n)).comp_hasStrictFDerivAt l₀
    (hasStrictFDerivAt_apply (𝕜 := ℝ) n l₀)
  simpa [Function.comp_def] using this

theorem hasStrictDerivAt_welfareTerm {g x : ℝ} (hx : 0 < x) (hc : 0 < x - g) :
    HasStrictDerivAt (fun y => P.u (y - g) - P.v y) (P.du (x - g) - P.dv x) x := by
  have h1 := (P.hu (x - g) hc).comp x ((hasStrictDerivAt_id x).sub_const g)
  have := HasStrictDerivAt.sub h1 (P.hv x hx)
  convert this using 1
  · funext y; simp [Function.comp_def]
  · simp

theorem hasStrictDerivAt_implTerm {g x : ℝ} (hx : 0 < x) (hc : 0 < x - g) :
    HasStrictDerivAt (fun y => P.du (y - g) * (y - g) - P.dv y * y)
      (P.d2u (x - g) * (x - g) + P.du (x - g) - P.d2v x * x - P.dv x) x := by
  have hs : HasStrictDerivAt (fun y : ℝ => y - g) 1 x := (hasStrictDerivAt_id x).sub_const g
  have h1 := (P.hdu (x - g) hc).comp x hs
  have h2 := HasStrictDerivAt.mul h1 hs
  have h3 := HasStrictDerivAt.mul (P.hdv x hx) (hasStrictDerivAt_id x)
  have := HasStrictDerivAt.sub h2 h3
  convert this using 1
  · funext y; simp [Function.comp_def]
  · simp; ring

variable [DecidableEq ι]

/-- **Ramsey first-order conditions with history-invariant multipliers.** -/
theorem ramsey_foc {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n) (hl : ∀ n, 0 < l₀ n)
    (hc : ∀ n, 0 < l₀ n - g n)
    (hmax : IsLocalMaxOn (P.welfare w g) {l | P.implement w g l = P.implement w g l₀} l₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧ ∀ n, P.Phi a b (g n) (l₀ n) = 0 := by
  have hW := hasStrictFDerivAt_wsum w (fun n y => P.u (y - g n) - P.v y) _ l₀
    (fun n => P.hasStrictDerivAt_welfareTerm (hl n) (hc n))
  have hI := hasStrictFDerivAt_wsum w (fun n y => P.du (y - g n) * (y - g n) - P.dv y * y) _ l₀
    (fun n => P.hasStrictDerivAt_implTerm (hl n) (hc n))
  obtain ⟨a, b, hab, heq⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inr hmax) hI hW
  refine ⟨a, b, hab, fun n => ?_⟩
  have h := congrArg (fun L => L (Pi.single n 1)) heq
  simp [sum_apply, Pi.single_apply] at h
  have h' : w n * P.Phi a b (g n) (l₀ n) = 0 := by
    simp only [Phi]; linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (hw n).ne'

/-- **History independence.** The Ramsey multipliers solve the node equation
at every history, and two histories with the same spending shock have the
same labour, consumption and tax, provided the node equation (with those
multipliers) has a unique root in the economic domain `l > 0`, `c > 0`. -/
theorem history_independence {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n) (hl : ∀ n, 0 < l₀ n)
    (hc : ∀ n, 0 < l₀ n - g n)
    (hmax : IsLocalMaxOn (P.welfare w g) {l | P.implement w g l = P.implement w g l₀} l₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧ (∀ n, P.Phi a b (g n) (l₀ n) = 0) ∧ ∀ n m, g n = g m →
      (∀ x y, 0 < x → 0 < x - g n → 0 < y → 0 < y - g n →
        P.Phi a b (g n) x = 0 → P.Phi a b (g n) y = 0 → x = y) →
      l₀ n = l₀ m ∧ l₀ n - g n = l₀ m - g m ∧ P.tax g l₀ n = P.tax g l₀ m := by
  obtain ⟨a, b, hab, hk⟩ := P.ramsey_foc hw hl hc hmax
  refine ⟨a, b, hab, hk, fun n m hg huniq => ?_⟩
  have hl' : l₀ n = l₀ m := huniq _ _ (hl n) (hc n) (hl m) (by rw [hg]; exact hc m) (hk n)
    (by rw [hg]; exact hk m)
  exact ⟨hl', by rw [hl', hg], by simp only [tax, hl', hg]⟩

omit [DecidableEq ι] in
theorem hasStrictDerivAt_isoV (γ : ℕ) (x : ℝ) :
    HasStrictDerivAt (fun l : ℝ => l ^ (γ + 1) / (γ + 1)) (x ^ γ) x := by
  have := (hasStrictDerivAt_pow (γ + 1) x).div_const ((γ : ℝ) + 1)
  convert this using 1
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp

/-- The quasilinear isoelastic preferences of `Econ.LucasStokey`. -/
def quasilinear (γ : ℕ) : Prefs where
  u := id
  du := fun _ => 1
  d2u := fun _ => 0
  v := fun l => l ^ (γ + 1) / (γ + 1)
  dv := fun l => l ^ γ
  d2v := fun l => γ * l ^ (γ - 1)
  hu := fun x _ => hasStrictDerivAt_id x
  hdu := fun x _ => hasStrictDerivAt_const x 1
  hv := fun x _ => hasStrictDerivAt_isoV γ x
  hdv := fun x _ => hasStrictDerivAt_pow γ x

omit [DecidableEq ι] in
theorem quasilinear_welfare (γ : ℕ) (w g l : ι → ℝ) :
    (quasilinear γ).welfare w g l = LucasStokey.welfare γ w g l := by
  simp only [welfare, LucasStokey.welfare, quasilinear, id]

omit [DecidableEq ι] in
theorem quasilinear_implement (γ : ℕ) (w g l : ι → ℝ) :
    (quasilinear γ).implement w g l = LucasStokey.implement γ w g l := by
  simp only [implement, LucasStokey.implement, quasilinear]
  exact Finset.sum_congr rfl fun n _ => by ring

omit [DecidableEq ι] in
/-- **Non-vacuity**: in the quasilinear specification `l ≡ 1` is a Ramsey
optimum (the first best of `LucasStokey.first_best`). -/
theorem nonvacuous (γ : ℕ) {w g : ι → ℝ} (hw : ∀ n, 0 ≤ w n) :
    IsLocalMaxOn ((quasilinear γ).welfare w g)
      {l | (quasilinear γ).implement w g l = (quasilinear γ).implement w g 1} 1 := by
  have h := (LucasStokey.first_best γ (g := g) hw).1
  have e1 : (quasilinear γ).welfare w g = LucasStokey.welfare γ w g :=
    funext (quasilinear_welfare γ w g)
  have e2 : {l | (quasilinear γ).implement w g l = (quasilinear γ).implement w g 1} =
      {l | LucasStokey.implement γ w g l = LucasStokey.implement γ w g 1} := by
    ext l; simp only [Set.mem_ofPred_eq, quasilinear_implement]
  rw [e1, e2]; exact h

omit [DecidableEq ι] in
/-- **A distortionary Ramsey optimum.** With `γ = 1` (so `v(l) = l²/2`) and
any constant labour `c ∈ (1/2, 1)`, the allocation `l ≡ c` maximizes welfare
on its implementability set (globally, hence locally); the constraint binds
(`c ≠ 1`, the first best) and the tax `1 − c` is strictly positive. -/
theorem distortionary_witness {w g : ι → ℝ} (hw : ∀ n, 0 ≤ w n) {c : ℝ} (hc1 : 1 / 2 < c)
    (hc2 : c < 1) :
    IsLocalMaxOn ((quasilinear 1).welfare w g)
      {l | (quasilinear 1).implement w g l = (quasilinear 1).implement w g (fun _ => c)}
      (fun _ => c) ∧ ∀ n, 0 < (quasilinear 1).tax g (fun _ => c) n := by
  refine ⟨IsMaxOn.isLocalMaxOn ?_, fun n => ?_⟩
  · intro l hl
    simp only [Set.mem_ofPred_eq, implement, quasilinear] at hl
    simp only [Set.mem_ofPred_eq, welfare, quasilinear, id]
    set A := ∑ n, w n * (l n - c)
    set Q := ∑ n, w n * (l n - c) ^ 2
    have hQ : 0 ≤ Q := Finset.sum_nonneg fun n _ => mul_nonneg (hw n) (sq_nonneg _)
    have hcon : (1 - 2 * c) * A - Q = 0 := by
      have : ∑ n, w n * (1 * (l n - g n) - l n ^ 1 * l n) -
          ∑ n, w n * (1 * (c - g n) - c ^ 1 * c) = (1 - 2 * c) * A - Q := by
        simp only [A, Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [← this, hl, sub_self]
    have hdiff : ∑ n, w n * (l n - g n - l n ^ (1 + 1) / (1 + 1)) -
        ∑ n, w n * (c - g n - c ^ (1 + 1) / (1 + 1)) = (1 - c) * A - 1 / 2 * Q := by
      simp only [A, Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    have : (1 - c) * A - 1 / 2 * Q ≤ 0 := by nlinarith
    push_cast at hdiff ⊢
    linarith
  · simp only [tax, quasilinear]
    norm_num
    linarith

end Prefs
end LucasStokeyGeneral
end Econ

end
