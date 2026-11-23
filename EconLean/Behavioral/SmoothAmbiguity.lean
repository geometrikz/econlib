/-
# Smooth ambiguity (Klibanoff–Marinacci–Mukerji 2005)

Reference. P. Klibanoff, M. Marinacci and S. Mukerji (2005), "A Smooth Model
of Decision Making under Ambiguity", *Econometrica* 73(6), Theorem 1 and
Propositions 1 and 3.

States `S` and a finite set of probabilistic models `p i` (`i : ι`), with
second-order prior `π`. An act is identified with its utility profile
`f : S → ℝ`. The smooth ambiguity value is

    V(f) = Σᵢ π(i) φ(E_{p i}[f]).

**Results** (`π` a probability vector).
* `V_le_reduced` (KMM Proposition 1, ⇐): if `φ` is concave, the decision
  maker weakly prefers the reduced lottery, i.e. `V(f) ≤ φ(Σᵢ π(i) E_{p i}[f])`:
  **ambiguity aversion**.
* `concaveOn_of_averse` (⇒): if this holds for every two-model ambiguity,
  `φ` is concave. So ambiguity aversion ⟺ concave `φ`.
* `V_mix_ge` (KMM Proposition 3, uncertainty aversion): with concave `φ`,
  `V(αf + (1 − α)g) ≥ αV(f) + (1 − α)V(g)`; in particular hedging between
  indifferent acts is weakly preferred (`hedging`).
* `V_linear`: with linear `φ` the model reduces to subjective expected
  utility under the reduced prior.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ

namespace SmoothAmbiguity

open Finset

variable {S ι : Type*} [Fintype S] [Fintype ι]

/-- Expected utility of `f` under model `p i`. -/
def E (p : ι → S → ℝ) (i : ι) (f : S → ℝ) : ℝ := ∑ s, p i s * f s

/-- The smooth ambiguity value. -/
def V (φ : ℝ → ℝ) (π : ι → ℝ) (p : ι → S → ℝ) (f : S → ℝ) : ℝ := ∑ i, π i * φ (E p i f)

/-- The reduced (Bayesian) expected utility. -/
def reduced (π : ι → ℝ) (p : ι → S → ℝ) (f : S → ℝ) : ℝ := ∑ i, π i * E p i f

/-- **Ambiguity aversion.** Concave `φ` ⇒ `V(f) ≤ φ(reduced EU)`. -/
theorem V_le_reduced {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {π : ι → ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1) (p : ι → S → ℝ) (f : S → ℝ) :
    V φ π p f ≤ φ (reduced π p f) := by
  have := hφ.le_map_sum (t := univ) (w := π) (p := fun i => E p i f) (fun i _ => hπ0 i) hπ1
    (fun i _ => Set.mem_univ _)
  simpa [V, reduced, smul_eq_mul] using this

/-- **Converse.** If the decision maker is ambiguity averse in every
two-state, two-model situation, `φ` is concave. This quantifies over all
second-order priors and models, a belief-free version of KMM's
characterization (which fixes the decision maker's own `μ` under a richness
condition). -/
theorem concaveOn_of_averse {φ : ℝ → ℝ}
    (h : ∀ (π : Fin 2 → ℝ), (∀ i, 0 ≤ π i) → ∑ i, π i = 1 → ∀ (p : Fin 2 → Fin 2 → ℝ)
      (f : Fin 2 → ℝ), (∀ i s, 0 ≤ p i s) → (∀ i, ∑ s, p i s = 1) →
      V φ π p f ≤ φ (reduced π p f)) :
    ConcaveOn ℝ Set.univ φ := by
  refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
  -- model `i` puts all mass on state `i`; the act pays `a` in state 0, `b` in state 1
  have := h ![α, β] (fun i => by fin_cases i <;> simp [hα, hβ]) (by simp [Fin.sum_univ_two, hαβ])
    (fun i s => if i = s then 1 else 0) ![a, b] (fun i s => by split_ifs <;> norm_num)
    (fun i => by fin_cases i <;> simp)
  simpa [V, reduced, E, Fin.sum_univ_two, smul_eq_mul] using this

/-- **Uncertainty aversion.** With concave `φ`, `V` is concave in the act.
Acts are utility profiles, so pointwise mixing in utility is the
Anscombe–Aumann mixture (the utility index is suppressed). -/
theorem V_mix_ge {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (p : ι → S → ℝ) (f g : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α * V φ π p f + (1 - α) * V φ π p g ≤ V φ π p (fun s => α * f s + (1 - α) * g s) := by
  unfold V
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have hE : E p i (fun s => α * f s + (1 - α) * g s) = α * E p i f + (1 - α) * E p i g := by
    simp only [E, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => by ring
  rw [hE]
  have := hφ.2 (Set.mem_univ (E p i f)) (Set.mem_univ (E p i g)) hα0 (by linarith : 0 ≤ 1 - α)
    (by ring)
  simp only [smul_eq_mul] at this
  nlinarith [hπ0 i]

/-- **Hedging.** Mixing two indifferent acts is weakly preferred to either. -/
theorem hedging {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (p : ι → S → ℝ) {f g : S → ℝ} (hfg : V φ π p f = V φ π p g) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : V φ π p f ≤ V φ π p (fun s => α * f s + (1 - α) * g s) := by
  have := V_mix_ge hφ hπ0 p f g hα0 hα1
  rw [← hfg] at this
  linarith

/-- With linear `φ`, smooth ambiguity is expected utility under the reduced
prior. -/
theorem V_linear {π : ι → ℝ} (hπ1 : ∑ i, π i = 1) (p : ι → S → ℝ) (f : S → ℝ) (a b : ℝ) :
    V (fun x => a + b * x) π p f = a + b * reduced π p f := by
  simp only [V, reduced, mul_add, sum_add_distrib, ← sum_mul, hπ1, one_mul, mul_sum]
  congr 1; refine sum_congr rfl fun i _ => by ring

/-- **Ellsberg-style strictness (non-vacuity).** With `φ = min · 0`
(concave), two models that put certainty on different states, equal weights,
and the bet `f = (1, −1)`: `V(f) = −1/2 < 0 = φ(reduced)`. -/
example : V (fun x => min x 0) ![1 / 2, 1 / 2] (fun i s : Fin 2 => if i = s then 1 else 0)
    ![1, -1] < min (reduced ![1 / 2, 1 / 2] (fun i s : Fin 2 => if i = s then 1 else 0)
      ![1, -1]) 0 := by
  norm_num [V, reduced, E, Fin.sum_univ_two]

end SmoothAmbiguity

end Econ
