# Review: Foundations/Measure/LyapunovIntegral.lean (batch 4a)

Context-isolated adversarial review (statements vs. Lyapunov 1940 / Aumann 1965 / Hildenbrand 1974). No blockers.
The reviewer compiled a scratch proof that the gluing lemma yields convexity of the integral of an arbitrary
correspondence and checked that the `∀ [DecidablePred]` binder accepts any instance.

Applied:
1. (should-fix) Doc overclaimed that gluing proves convexity of correspondence integrals: added the corollary
   `selectionIntegral` / `convex_selectionIntegral` itself.
2. (should-fix) Weighted gluing with measurable weights (Hildenbrand's ∫F = ∫conv F) not covered: recorded as a
   known gap in the module doc (not needed for Aumann 1964).
3. (nit) Compactness half of Lyapunov absent: stated in the module doc's Scope paragraph.
5. (nit) Module doc now says "every measurable A".
6. (nit) `partMeasure`/`partDiff` documented as internal helpers.
7. (nit) Gluing generalised to a measurable set A (`exists_subset_piecewise_setIntegral_eq`, B ⊆ A); the old
   whole-space lemma is kept as the case A = Ω.

Not applied: 4 (σ-finite λ; finite suffices for Aumann/Hildenbrand), 9 (cross-reference to Mathlib `NoAtoms`;
Sierpinski.lean is already frozen and its docstring explains the definition).

Checks: warning-free; `#print axioms` = [propext, Classical.choice, Quot.sound] for all 7 headline theorems;
leanchecker exit 0; nanoda: 36330 declarations, no typechecker errors. Frozen statements added to
Audit/Statements/Lyapunov.lean (section LyapunovIntegral).
