# Review: existence of Walrasian equilibrium with production

Module: `EconLean/GE/ExistenceProduction.lean`. Context-isolated adversarial review, 2026-11-25.

**Verdict: accept with should-fix items; nothing blocking.** The conclusion is the full MWG 16.B.3/17.B.1
equilibrium at p ≫ 0. `demand_unbounded`, `exists_continuous_supply` (Berge) and the unique-maximizer corollary are
correct; hypotheses are consistent (discharged by the witness).

Findings and resolution:
1. Witness technology was a free lunch (disc contained nonnegative nonzero outputs). Fixed: disc re-centred at
   (−1, −2), radius √5, inside `y₀ + 2y₁ ≤ 0`; `discSet_noFreeLunch` proves Y ∩ ℝ²₊ = {0}.
2. Witness docstring overclaimed the firm is active in equilibrium. Fixed: claim dropped (open).
3. Cost of compactness not disclosed. Fixed: header now says compactness replaces Arrow–Debreu's closed, convex,
   free-disposal sets, excludes free disposal/CRS, and truncation to attainable sets is not formalized.
4. Continuous selection hypothesis acceptable; set-valued (Kakutani) case noted as not covered.
5. Nonzero individual endowments: documented as a proof convenience.
6–8. Notes; no change.

Proof checks: `#print axioms` standard; leanchecker 0; nanoda clean. Frozen: `Audit/Statements/GE.lean`, section
ExistenceProduction. Full build warning-free.

## Addendum (2026-11-25): individual endowments relaxed

The hypothesis `hωa : ∀ a, E.endow a ≠ 0` was removed from
`exists_walrasianEquilibrium_production` and `_of_unique`. Zero-wealth consumers
demand 0 (`demand_zero_wealth`), with continuity by the squeeze `0 ≤ xᵢ ≤ w/pᵢ`.
New witness `discEconomy3` (pure shareholder, `discEconomy3_endow_two`).

Isolated adversarial review: no substantive issues. Arrow's exceptional case is
avoided because demand is only needed at p ≫ 0, and near boundary prices the
aggregate endowment ≫ 0 keeps some consumer's wealth bounded away from 0.
Nits applied: header names `discEconomy3`; "nothing at all" wording notes it is
covered by the theorem but not by a witness; witness docstring says wealth is not
computed; citation changed to MWG §17.B–17.C.

Checks: axioms {propext, Classical.choice, Quot.sound}; leanchecker clean;
nanoda 30608 declarations, no typechecker errors; frozen statements in
`Audit/Statements/GE.lean` updated and building.
