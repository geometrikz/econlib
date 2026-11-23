/-
# Beyond Hulten in a two-layer CES network (Baqaee–Farhi)

Baqaee and Farhi (2019), "The Macroeconomic Impact of Microeconomic Shocks:
Beyond Hulten's Theorem", Econometrica, Theorem 2 / eq. (7) specialized to a
nested-CES (tree) production structure.

**The economy.** Final output is a CES aggregate with elasticity `θ₀` of
group composites `g ∈ G`; each group composite is a CES aggregate with
elasticity `θ_g` of sector goods `i ∈ n`, each produced from labour with log
productivity `x_{g i}`. Applying the one-layer reduced form of
`Macro/BaqaeeFarhi.lean` at both layers, log real GDP is
`log Y(x) = log Y₀(g ↦ log Y_g(x_g))` (`logY`). The Domar weight of sector
`(g, i)` is `Λ_g λ_{g i}`: the group's sales share times the sector's share
within the group.

**Results.** Along a direction of productivity shocks `d`:
* `hasDerivAt_logY`: first order, `d log Y = Σ_g Λ_g Σ_i λ_{gi} d_{gi}` —
  Hulten's theorem with network Domar weights.
* `second_order`: second order,
  `d² log Y = (θ₀ − 1) Var_Λ(m) + Σ_g Λ_g (θ_g − 1) Var_{λ_g}(d_g)`,
  where `m_g = Σ_i λ_{gi} d_{gi}` is the group-level shock: each CES node
  contributes its elasticity minus one times the variance, under its own
  expenditure shares, of the shocks hitting its inputs (Baqaee–Farhi's
  formula; zero exactly in the Cobb–Douglas limit or for uniform shocks).

The one-layer derivatives are first generalized from lines to arbitrary
differentiable paths (`hasDerivAt_logY_path`, `hasDerivAt_domar_path`).

**Interpretation.** `log Y_g` and `log Y` are minus log CES price indices of
linear-in-labour technologies (one mobile factor), so `θ` is the elasticity of
substitution and `x` are log productivities. If `x` were log input quantities
the curvature coefficient would be `(θ − 1)/θ` instead.

**Deviations.** A tree (no roundabout production) with two layers; the
general input–output network of Baqaee–Farhi is not formalized. All
elasticities differ from one (the one-layer formula is a junk value at 1).
-/
module

public import EconLean.Macro.BaqaeeFarhi

@[expose] public section

noncomputable section

namespace Econ
namespace BaqaeeFarhi

open Finset Real

namespace Economy

variable {n : Type*} [Fintype n] (E : Economy n)

/-- `S` along a differentiable path. -/
theorem hasDerivAt_S_path {y : ℝ → n → ℝ} {y' : n → ℝ} {t₀ : ℝ}
    (hy : ∀ i, HasDerivAt (fun t => y t i) (y' i) t₀) :
    HasDerivAt (fun t => E.S (y t))
      (∑ i, E.b i * (exp ((E.θ - 1) * y t₀ i) * ((E.θ - 1) * y' i))) t₀ := by
  unfold S
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul _ ?_
  exact (Real.hasDerivAt_exp _).comp t₀ ((hy i).const_mul (E.θ - 1))

/-- **Hulten along a path.** -/
theorem hasDerivAt_logY_path (hθ : E.θ ≠ 1) {y : ℝ → n → ℝ} {y' : n → ℝ} {t₀ : ℝ}
    (hy : ∀ i, HasDerivAt (fun t => y t i) (y' i) t₀) :
    HasDerivAt (fun t => E.logY (y t)) (∑ i, E.domar (y t₀) i * y' i) t₀ := by
  have hθ' : E.θ - 1 ≠ 0 := sub_ne_zero.2 hθ
  have hlog := ((E.hasDerivAt_S_path hy).log (E.S_pos _).ne').const_mul (E.θ - 1)⁻¹
  convert hlog using 1
  · rfl
  simp only [domar, Finset.sum_div, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  field_simp

/-- **Domar weights along a path**: `λᵢ' = (θ − 1) λᵢ (yᵢ' − Σⱼ λⱼ yⱼ')`. -/
theorem hasDerivAt_domar_path {y : ℝ → n → ℝ} {y' : n → ℝ} {t₀ : ℝ}
    (hy : ∀ i, HasDerivAt (fun t => y t i) (y' i) t₀) (i : n) :
    HasDerivAt (fun t => E.domar (y t) i)
      ((E.θ - 1) * E.domar (y t₀) i * (y' i - ∑ j, E.domar (y t₀) j * y' j)) t₀ := by
  have hN : HasDerivAt (fun t => E.b i * exp ((E.θ - 1) * y t i))
      (E.b i * (exp ((E.θ - 1) * y t₀ i) * ((E.θ - 1) * y' i))) t₀ :=
    ((Real.hasDerivAt_exp _).comp t₀ ((hy i).const_mul (E.θ - 1))).const_mul _
  have hq := hN.div (E.hasDerivAt_S_path hy) (E.S_pos _).ne'
  convert hq using 1
  · rfl
  have hSx := (E.S_pos (y t₀)).ne'
  simp only [domar]
  have e1 : ∑ j, E.b j * exp ((E.θ - 1) * y t₀ j) / E.S (y t₀) * y' j =
      (∑ j, E.b j * exp ((E.θ - 1) * y t₀ j) * y' j) / E.S (y t₀) := by
    rw [Finset.sum_div]; exact sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, E.b j * (exp ((E.θ - 1) * y t₀ j) * ((E.θ - 1) * y' j)) =
      (E.θ - 1) * ∑ j, E.b j * exp ((E.θ - 1) * y t₀ j) * y' j := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  field_simp

end Economy

/-- A two-layer nested-CES economy. -/
structure Nested (G n : Type*) [Fintype G] [Fintype n] where
  /-- Top node: final output over group composites. -/
  top : Economy G
  /-- Group nodes: each composite over sector goods. -/
  grp : G → Economy n

namespace Nested

variable {G n : Type*} [Fintype G] [Fintype n] (N : Nested G n)

/-- Log real GDP. -/
def logY (x : G → n → ℝ) : ℝ := N.top.logY fun g => (N.grp g).logY (x g)

/-- Group sales shares `Λ_g`. -/
def Λ (x : G → n → ℝ) (g : G) : ℝ := N.top.domar (fun g => (N.grp g).logY (x g)) g

/-- Group-level shock `m_g = Σᵢ λ_{gi} d_{gi}`. -/
def m (x d : G → n → ℝ) (g : G) : ℝ := ∑ i, (N.grp g).domar (x g) i * d g i

/-- The line `x + t d`. -/
def line (x d : G → n → ℝ) (t : ℝ) : G → n → ℝ := fun g i => x g i + t * d g i

omit [Fintype G] [Fintype n] in
theorem hasDerivAt_line (x d : G → n → ℝ) (g : G) (i : n) (t₀ : ℝ) :
    HasDerivAt (fun t => line x d t g i) (d g i) t₀ := by
  simpa [line] using ((hasDerivAt_id t₀).mul_const (d g i)).const_add (x g i)

theorem hasDerivAt_inner (hθ : ∀ g, (N.grp g).θ ≠ 1) (x d : G → n → ℝ) (g : G) (t₀ : ℝ) :
    HasDerivAt (fun t => (N.grp g).logY (line x d t g)) (N.m (line x d t₀) d g) t₀ :=
  (N.grp g).hasDerivAt_logY_path (hθ g) fun i => hasDerivAt_line x d g i t₀

/-- **Hulten's theorem in the network**: the first derivative of log GDP
along `d` at any point of the line is `Σ_g Λ_g m_g`, i.e. sector `(g, i)`'s
elasticity is its network Domar weight `Λ_g λ_{gi}`. -/
theorem hasDerivAt_logY (h₀ : N.top.θ ≠ 1) (hθ : ∀ g, (N.grp g).θ ≠ 1) (x d : G → n → ℝ)
    (t₀ : ℝ) :
    HasDerivAt (fun t => N.logY (line x d t))
      (∑ g, N.Λ (line x d t₀) g * N.m (line x d t₀) d g) t₀ :=
  N.top.hasDerivAt_logY_path h₀ fun g => N.hasDerivAt_inner hθ x d g t₀

/-- **Baqaee–Farhi second-order formula in a two-layer CES network.** -/
theorem second_order (h₀ : N.top.θ ≠ 1) (hθ : ∀ g, (N.grp g).θ ≠ 1) (x d : G → n → ℝ) :
    deriv (deriv fun t => N.logY (line x d t)) 0 =
      (N.top.θ - 1) * (∑ g, N.Λ x g * N.m x d g ^ 2 - (∑ g, N.Λ x g * N.m x d g) ^ 2) +
      ∑ g, N.Λ x g * (((N.grp g).θ - 1) *
        (∑ i, (N.grp g).domar (x g) i * d g i ^ 2 - N.m x d g ^ 2)) := by
  have h1 : deriv (fun t => N.logY (line x d t)) =
      fun t => ∑ g, N.Λ (line x d t) g * N.m (line x d t) d g :=
    funext fun t => (N.hasDerivAt_logY h₀ hθ x d t).deriv
  rw [h1]
  have hx : line x d 0 = x := by funext g i; simp [line]
  -- derivative of `Λ_g` along the line
  have hΛ : ∀ g, HasDerivAt (fun t => N.Λ (line x d t) g)
      ((N.top.θ - 1) * N.Λ x g * (N.m x d g - ∑ h, N.Λ x h * N.m x d h)) 0 := by
    intro g
    have := N.top.hasDerivAt_domar_path (fun g => N.hasDerivAt_inner hθ x d g 0) g
    simpa [Λ, hx] using this
  -- derivative of `m_g` along the line
  have hm : ∀ g, HasDerivAt (fun t => N.m (line x d t) d g)
      (((N.grp g).θ - 1) * (∑ i, (N.grp g).domar (x g) i * d g i ^ 2 - N.m x d g ^ 2)) 0 := by
    intro g
    have hi : ∀ i, HasDerivAt (fun t => (N.grp g).domar (line x d t g) i * d g i)
        (((N.grp g).θ - 1) * (N.grp g).domar (x g) i * (d g i - N.m x d g) * d g i) 0 := by
      intro i
      have := ((N.grp g).hasDerivAt_domar_path (fun i => hasDerivAt_line x d g i 0) i).mul_const
        (d g i)
      simpa [hx, m] using this
    have hs := HasDerivAt.fun_sum (u := univ) fun i _ => hi i
    convert hs using 1
    · rfl
    set μ := N.m x d g
    have hμ : ∑ i, (N.grp g).domar (x g) i * d g i = μ := rfl
    calc ((N.grp g).θ - 1) * (∑ i, (N.grp g).domar (x g) i * d g i ^ 2 - μ ^ 2)
        = ((N.grp g).θ - 1) * (∑ i, (N.grp g).domar (x g) i * d g i ^ 2 - μ * μ) := by ring
      _ = ∑ i, (((N.grp g).θ - 1) * ((N.grp g).domar (x g) i * d g i ^ 2) -
            ((N.grp g).θ - 1) * μ * ((N.grp g).domar (x g) i * d g i)) := by
          rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hμ]; ring
      _ = _ := sum_congr rfl fun i _ => by ring
  have hsum : HasDerivAt (fun t => ∑ g, N.Λ (line x d t) g * N.m (line x d t) d g) _ 0 :=
    HasDerivAt.fun_sum (u := univ) fun g _ => (hΛ g).mul (hm g)
  rw [hsum.deriv]
  simp only [hx]
  set M := ∑ h, N.Λ x h * N.m x d h
  have e : ∑ g, ((N.top.θ - 1) * N.Λ x g * (N.m x d g - M)) * N.m x d g =
      (N.top.θ - 1) * (∑ g, N.Λ x g * N.m x d g ^ 2 - M ^ 2) := by
    calc ∑ g, ((N.top.θ - 1) * N.Λ x g * (N.m x d g - M)) * N.m x d g
        = ∑ g, ((N.top.θ - 1) * (N.Λ x g * N.m x d g ^ 2) - (N.top.θ - 1) * M *
            (N.Λ x g * N.m x d g)) := sum_congr rfl fun g _ => by ring
      _ = (N.top.θ - 1) * ∑ g, N.Λ x g * N.m x d g ^ 2 - (N.top.θ - 1) * M * M := by
          rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
      _ = _ := by ring
  rw [sum_add_distrib, e]

end Nested
end BaqaeeFarhi
end Econ

end
