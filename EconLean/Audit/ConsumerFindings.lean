/-
# Audit findings, checked in Lean

Machine-checked evidence for the adversarial statement review in
`Audit/REVIEW-consumer.md` (2026-11-23). Each `example` compiles with no `sorry`; the
comment says what it shows. These are *diagnostics*, not results: some show a
statement is weaker than the textbook, some show a definition returns a junk
value, some show a hypothesis can actually be satisfied (the theorem is not
vacuous).
-/
module

public import EconLean.Consumer.Envelope
public import EconLean.Consumer.RevealedPreference
public import EconLean.Consumer.Continuity

@[expose] public section

open Econ

noncomputable section

/-! ### F1. Junk value: an unreachable utility level has expenditure 0.
`expenditure` is an `sInf`, and Mathlib sets `sInf ∅ = 0` on ℝ. MWG would say
e(p, ū) = +∞ (or is undefined). Every current theorem about `expenditure`
assumes a bundle reaching ū exists, so none is affected; a future theorem such
as "e is strictly increasing in ū" must keep that assumption. -/
example : expenditure (ι := Fin 2) (fun _ => (0 : ℝ)) 1 1 = 0 := by
  have h : upperSet (ι := Fin 2) (fun _ => (0 : ℝ)) 1 = ∅ := by
    ext x
    simp [upperSet]
  simp [expenditure, h]

/-! ### F2. Junk value: negative wealth gives indirect utility 0, even when u ≡ 5.
The budget set is empty and `sSup ∅ = 0`. -/
example : indirectUtility (ι := Fin 2) (fun _ => (5 : ℝ)) 1 (-1) = 0 := by
  have h : budgetSet (ι := Fin 2) (1 : Fin 2 → ℝ) (-1) = ∅ := by
    ext x
    simp only [budgetSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    have := cost_nonneg (p := (1 : Fin 2 → ℝ)) (x := x) (by intro i; simp) hx
    linarith
  simp [indirectUtility, h]

/-! ### F3. `ConvexPref` is stronger than MWG Def. 3.B.4.
`u x = max x₀ 0 + max x₁ 0` is perfect substitutes on the orthant, so it is a
convex preference in MWG's sense, yet `ConvexPref (prefOf u)` fails: it asks
for convex upper contour sets on all of ℝ², and the midpoint of (2, −10) and
(−10, 2) is (−4, −4), which is worse than (2, 0). So `convex_demand` covers
fewer preferences than MWG Prop. 3.D.2(iii). Suggested fix: quantify over
bundles `x ≥ 0` and intersect the contour set with the orthant. -/
-- RESOLVED (2026-11-23): `ConvexPref` now matches MWG Def. 3.B.4 (contour sets
-- intersected with the orthant, for `x ≥ 0`), so this counterexample no longer applies.

/-! ### F4. `slutsky` holds for functions unrelated to any consumer.
With X = H = E = 0 every hypothesis holds and the conclusion is 0 = 0. The
lemma is the chain-rule step of MWG Prop. 3.G.3; the economics (h = x(p, e(p,ū))
and Shephard's lemma) enters only as hypotheses, and nothing ties X, H, E to
`demand`, `hicksian`, `expenditure`.
RESOLVED (2026-11-23): `slutsky_demand` (Consumer/Envelope.lean) ties X, H, E to the
actual demand, Hicksian demand and expenditure of `u`, and proves the duality
identity and Shephard's lemma instead of assuming them. `slutsky` is kept as
the abstract chain-rule step, so this example still compiles. -/
example : ∀ δ : Fin 2 → ℝ,
    (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) δ =
      (0 : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)) (δ, 0) +
        cost δ ((fun _ => (0 : Fin 2 → ℝ)) (0 : Fin 2 → ℝ)) •
          (0 : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)) (0, 1) :=
  slutsky (X := fun _ => 0) (H := fun _ => 0) (E := fun _ => 0) (p := 0)
    (Filter.Eventually.of_forall fun _ => rfl)
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) (hasFDerivAt_const _ _)
    (fun δ => by simp [cost])

/-! ### F5. The compensated law of demand is algebra on its WARP hypothesis.
Under Walras' law and a compensated price change, (p' − p)·(x' − x) = w − p·x',
so `compensated_law_of_demand`'s conclusion is the WARP hypothesis rewritten.
That matches MWG's own proof of the WARP ⇒ CLD direction of Prop. 2.F.1; the
converse direction is not in the library. -/
example {ι : Type*} [Fintype ι] {p p' x x' : ι → ℝ} {w w' : ℝ}
    (hwal : cost p x = w) (hwal' : cost p' x' = w') (hcomp : w' = cost p' x) :
    cost (p' - p) (x' - x) = w - cost p x' := by
  rw [cost_sub_left, cost_sub_right, cost_sub_right]
  linarith

/-! ### F6. Non-vacuity: local nonsatiation can be satisfied.
Linear utility on two goods is strongly monotone, hence locally nonsatiated, so
`walras_law`, `roy`, `demand_subset_hicksian` apply to a real consumer. -/
example : StronglyMonotone (prefOf (fun x : Fin 2 → ℝ => x 0 + x 1)) := by
  intro x y _ hxy hne
  have h0 := hxy 0; have h1 := hxy 1
  have : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra hc
    simp only [not_or, not_lt] at hc
    exact hne (funext fun i => by fin_cases i <;> simp <;> linarith [hc.1, hc.2])
  constructor <;> simp [prefOf] <;> rcases this with h | h <;> linarith

example : LocallyNonsatiated (prefOf (fun x : Fin 2 → ℝ => x 0 + x 1)) := by
  apply StronglyMonotone.locallyNonsatiated
  intro x y _ hxy hne
  have h0 := hxy 0; have h1 := hxy 1
  have : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra hc
    simp only [not_or, not_lt] at hc
    exact hne (funext fun i => by fin_cases i <;> simp <;> linarith [hc.1, hc.2])
  constructor <;> simp [prefOf] <;> rcases this with h | h <;> linarith


/-! ### F7. `StrictlyQuasiconcave` is stronger than MWG's strict quasiconcavity.
(Review of `Consumer/Continuity.lean`, `Audit/REVIEW-continuity.md`.)
It quantifies over all of ℝⁿ, not the consumption set ℝⁿ₊. `u x = Σ √xᵢ` is
strictly quasiconcave on ℝ²₊, but Mathlib's `Real.sqrt` is 0 on negative
numbers, so u is flat on the negative orthant and fails the Lean definition.
So `demand_subsingleton` and `exists_continuous_demand_function` do not apply
to it. Suggested fix: require `0 ≤ x → 0 ≤ y →`, or use Mathlib's
`StrictQuasiconcaveOn ℝ (Set.Ici 0) u`. -/
-- RESOLVED (2026-11-23): `StrictlyQuasiconcave` now quantifies over `0 ≤ x`, `0 ≤ y`
-- only, so Σ √xᵢ is covered and the counterexample above no longer applies.

/-! ### F8. Cobb–Douglas is not strictly quasiconcave on the closed orthant.
(Re-review after the F3/F7 fixes, 2026-11-23.) `StrictlyQuasiconcave` now
matches MWG on ℝⁿ₊, but `√(x₀ x₁)` is 0 along both axes, so it fails there and
`exists_continuous_demand_function` does not cover the canonical consumer.
MWG has the same gap and handles it by noting Cobb–Douglas demand is interior.
OPEN: a version assuming strict quasiconcavity on `{x ≥ 0 | u x > u 0}` (or on
the interior, plus interior demand for `w > 0`). -/
example : ¬ StrictlyQuasiconcave
    (fun x : Fin 2 → ℝ => Real.sqrt (max (x 0) 0 * max (x 1) 0)) := by
  intro h
  have := h ![1, 0] ![2, 0] (by intro i; fin_cases i <;> simp) (by intro i; fin_cases i <;> simp)
    (by intro e; have := congrFun e 0; simp at this) (1/2) (by norm_num) (by norm_num)
  simp at this

end
