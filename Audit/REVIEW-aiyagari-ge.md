# Review: Aiyagari GE (CDFirm.lean, AiyagariGE.lean)

Frozen statements: `Audit/Statements/AiyagariGE.lean` (9 theorems).

## Reverifiers
- `#print axioms`: all 9 use only propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on EconLean.Macro.HA.CDFirm, EconLean.Macro.HA.AiyagariGE, EconLean.Audit.Statements.AiyagariGE.
- nanoda: 37,980 declarations, no errors.
- Full `lake build` warning-free.

## Adversarial statement review (context-isolated)
OK: all of CDFirm (rpow guards correct), marg_isInvariant, integral_policy_eq, integral_zfun,
goods-market identity, sqrt helper inequalities and arithmetic.

Findings and responses:
1. HIGH. `sqrtEconomy`/`sqrt_equilibrium` equilibrium exists only because of the cap: supply ≤ k̄ = 1
   forces r ≥ 0.4, so β(1+r) > 1 and the cap binds; no income risk (e ≡ 1).
   Response: relabeled as a non-vacuity witness of the capped economy, with the caveat in Lean
   docstrings, module docs and blueprint. Not claimed as a textbook Aiyagari equilibrium.
2. HIGH. `exists_stationary_equilibrium` is for the economy with exogenous cap k̄; conclusion does not
   say the cap is slack. Response: renamed in docs ("with an exogenous asset cap"); the endogenous cap
   from β(1+r) < 1 is listed as open and is the next work item.
3. MEDIUM. `le_policy`/`hhi_of_le_policy` route is genuine but only usable where only the cap bounds
   supply (needs g ≥ m > 0 everywhere, fails when the borrowing limit binds). Documented.
4. LOW. `foc_labor` is definitional. Docstring now says so.
5. Coverage gaps: r* < 1/β − 1, Huggett, Açıkgöz uniqueness, general borrowing limits. Logged.
