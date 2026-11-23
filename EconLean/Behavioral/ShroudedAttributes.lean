/-
# Shrouded attributes and the curse of debiasing (Gabaix–Laibson)

Reference. X. Gabaix and D. Laibson (2006), "Shrouded Attributes, Consumer
Myopia, and Information Suppression in Competitive Markets", *QJE* 121(2).

**The model.** Competitive firms sell a base good (unit cost `c`) and an
add-on (unit cost `ĉ`). A share `α ∈ [0, 1]` of consumers is *myopic*: they
see only the base price and later pay the add-on price `pa` (`p̂` in GL; up to the
maximum `v̂`). The other consumers are *sophisticated*: they anticipate the
add-on price and avoid it at substitution cost `e` when `pa > e`. A firm can
*unshroud* (advertise the add-on price), which educates myopes into
sophisticates.

In the shrouded equilibrium every firm charges `pa = v̂ > e` and, by zero
profit, base price `p* = c − α(v̂ − ĉ)`: the base good is a loss leader
financed by the myopes' add-on purchases.

**Modelling choices (review 2026-11-23).** Unshrouding educates *all*
myopes (GL's `λ = 1`; their general case `λ ∈ (0, 1]` is not covered). A
deviator that weakly undercuts captures a whole segment instead of sharing
it `1/n`, which is conservative for the no-deviation results. The
equilibrium interpretation of `pStar` and `zero_profit` presumes
`ĉ < e < v̂` (sophisticates avoid the add-on) and `α ∈ [0, 1]`; theorems
state the hypotheses they use.

**What is formalized** (per-consumer profits; ties are resolved in the
deviator's favor, which only strengthens the no-deviation results):

* `pStar_lt` (loss leader) and `zero_profit` (zero profit at `(p*, v̂)`);
* `shrouded_no_deviation`: if `e − ĉ ≤ α(v̂ − ĉ)`, no shrouded offer with
  add-on price at most `v̂` earns positive profit against `p*`;
* `curse_of_debiasing` (GL Proposition 2): if `ĉ ≤ e` and
  `e − ĉ < α(v̂ − ĉ)`, an unshrouding firm loses money on every educated
  consumer it attracts, so no firm wants to unshroud;
* `unshroud_profitable`: conversely, if `α(v̂ − ĉ) < e − ĉ`, unshrouding at
  `(p*, e)` attracts educated consumers at a strict profit.
-/
module

public import Mathlib.Order.MinMax
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ.Shrouding

/-- Market primitives. -/
structure Market where
  /-- unit cost of the base good -/
  c : ℝ
  /-- unit cost of the add-on, `ĉ` -/
  cA : ℝ
  /-- sophisticated consumers' cost of substituting away from the add-on -/
  e : ℝ
  /-- maximal add-on price, `v̂` -/
  vA : ℝ
  /-- share of myopic consumers -/
  α : ℝ

namespace Market

variable (M : Market)

/-- Shrouded-equilibrium base price (zero profit with `pa = v̂`). -/
def pStar : ℝ := M.c - M.α * (M.vA - M.cA)

/-- **Loss leader**: the base good sells below cost iff myopes exist and the
add-on is marked up. -/
theorem pStar_lt (h : 0 < M.α * (M.vA - M.cA)) : M.pStar < M.c := by
  unfold pStar; linarith

/-- **Zero profit** at the shrouded prices `(p*, v̂)` with `v̂ > e`: myopes pay
the add-on, sophisticates substitute. -/
theorem zero_profit :
    M.α * (M.pStar - M.c + (M.vA - M.cA)) + (1 - M.α) * (M.pStar - M.c) = 0 := by
  unfold pStar; ring

/-- Per-consumer profit of a firm that keeps the add-on shrouded and offers
`(p, pa)` against rivals at `(p*, v̂)`. Myopes compare base prices only and
come iff `p ≤ p*`; sophisticates compare total costs `p + min pa e` and come
iff it is at most `p* + e`; they buy the add-on iff `pa ≤ e`. -/
noncomputable def profitShrouded (p pa : ℝ) : ℝ :=
  (if p ≤ M.pStar then M.α * (p - M.c + (pa - M.cA)) else 0) +
    (if p + min pa M.e ≤ M.pStar + M.e then
      (1 - M.α) * (p - M.c + if pa ≤ M.e then pa - M.cA else 0) else 0)

/-- Per-consumer profit of a firm that unshrouds and offers `(p, pa)`: every
consumer is now educated and behaves like a sophisticate. -/
noncomputable def profitUnshrouded (p pa : ℝ) : ℝ :=
  if p + min pa M.e ≤ M.pStar + M.e then p - M.c + (if pa ≤ M.e then pa - M.cA else 0) else 0

/-- **No profitable shrouded deviation.** If `e − ĉ ≤ α(v̂ − ĉ)` and
`α ∈ [0, 1]`, any shrouded offer with add-on price at most `v̂` earns at most
zero against rivals at `(p*, v̂)`. -/
theorem shrouded_no_deviation (hα0 : 0 ≤ M.α) (hα1 : M.α ≤ 1)
    (hcurse : M.e - M.cA ≤ M.α * (M.vA - M.cA)) {p pa : ℝ} (hpa : pa ≤ M.vA) :
    M.profitShrouded p pa ≤ 0 := by
  unfold profitShrouded
  have hps : M.pStar = M.c - M.α * (M.vA - M.cA) := rfl
  by_cases he : pa ≤ M.e
  · rw [min_eq_left he]
    simp only [he, ite_true]
    split_ifs with h1 h2 h2
    · nlinarith
    · linarith
    · nlinarith
    · linarith
  · have he' : M.e < pa := lt_of_not_ge he
    rw [min_eq_right he'.le]
    simp only [he, ite_false, add_zero]
    split_ifs with h1 h2 h2
    · nlinarith
    · exact absurd (by linarith) h2
    · exact absurd (by linarith) h1
    · linarith

/-- **The curse of debiasing** (GL Proposition 2). If the add-on is
efficiently supplied by the firm (`ĉ ≤ e`) and `e − ĉ < α(v̂ − ĉ)`, an
unshrouding firm makes a strict loss on every consumer it attracts. -/
theorem curse_of_debiasing (hce : M.cA ≤ M.e) (hcurse : M.e - M.cA < M.α * (M.vA - M.cA))
    {p pa : ℝ} (hattract : p + min pa M.e ≤ M.pStar + M.e) :
    M.profitUnshrouded p pa < 0 := by
  unfold profitUnshrouded
  rw [ite_eq_left hattract]
  have hps : M.pStar = M.c - M.α * (M.vA - M.cA) := rfl
  by_cases he : pa ≤ M.e
  · rw [min_eq_left he] at hattract
    simp only [he, ite_true]
    linarith
  · rw [min_eq_right (le_of_not_ge he)] at hattract
    simp only [he, ite_false]
    linarith

/-- Unshrouding never helps under the curse-of-debiasing condition: profit
is at most zero, whether or not consumers are attracted. -/
theorem profitUnshrouded_nonpos (hce : M.cA ≤ M.e) (hcurse : M.e - M.cA < M.α * (M.vA - M.cA))
    (p pa : ℝ) : M.profitUnshrouded p pa ≤ 0 := by
  by_cases h : p + min pa M.e ≤ M.pStar + M.e
  · exact (M.curse_of_debiasing hce hcurse h).le
  · unfold profitUnshrouded; rw [ite_eq_right h]

/-- **When education pays.** If `α(v̂ − ĉ) < e − ĉ`, unshrouding with base
price `p*` and add-on price `e` attracts educated consumers and earns a
strictly positive profit on each. -/
theorem unshroud_profitable (h : M.α * (M.vA - M.cA) < M.e - M.cA) :
    M.pStar + min M.e M.e ≤ M.pStar + M.e ∧ 0 < M.profitUnshrouded M.pStar M.e := by
  refine ⟨by simp, ?_⟩
  unfold profitUnshrouded
  simp only [min_self, le_refl, ite_true]
  unfold pStar
  linarith

end Market

end Econ.Shrouding
