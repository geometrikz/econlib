# Review: Foundations/Measure/Sierpinski.lean and Foundations/Measure/Lyapunov.lean

Context-isolated adversarial reviews (2026-11-25), three passes.

## Sierpinski.lean
No substantive problems. Fixes applied:
1. `Nonatomic` docstring: agrees with the standard (Fremlin 211I–J) notion for
   finite/semifinite measures; stronger on sets of infinite measure; implies
   Mathlib's `NoAtoms` for finite measures but not conversely.
2. Partition lemma: induction form renamed `exists_partition_measureReal_le_aux`;
   clean `exists_partition_measureReal_le` (no `n`) added and frozen.
3. Added `Nonatomic.of_absolutelyContinuous` (needed to apply Lyapunov to
   measures with densities, as in Aumann's proof).

## Lyapunov.lean
No mathematical errors; statements faithful (Halmos-style subset form; convexity
of the range). Fixes applied:
1. Measure index generalized from `Fin n` to any `[Fintype η]`.
2. `exists_vertex` renamed `exists_few_fractional` (it yields a point with at
   most |η| fractional coordinates, not necessarily a vertex); induction form
   kept as `exists_few_fractional_aux`; clean wrapper frozen.
3. `range` made `protected`; docstring added to `measureReal_le_sum`.
4. Module doc lists what is not included: compactness, signed/density version,
   monotone-chain form. The density version (∫_B f dλ) is planned with the
   continuum-economy batch.

Mechanical checks: axioms standard only; leanchecker OK on both modules; nanoda
OK (21786 declarations); frozen statements in Audit/Statements/Lyapunov.lean build.
