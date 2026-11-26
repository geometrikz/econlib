# Review: macro batch 19 (Rotemberg pricing, He–Krishnamurthy)

Context-isolated adversarial referee, 2026-11-26. Verified by hand: the FOC from the loss, the
NKPC and its timing (matches `Calvo.nkpc`), the symmetric-equilibrium reading (aggregate p fixed,
own price varied: a legitimate unilateral-deviation condition), x = Kμ/(γσ²), μ = γσ²/K and the
two regimes. No false, vacuous or contradictory hypotheses.

| # | Sev. | Item | Resolution |
|---|------|------|------------|
| 1 | MAJOR | `calvo_equiv` only a slope identity; "observationally equivalent" overclaimed | Added `calvo_bridge` (Rotemberg equilibrium ⇒ exact `Calvo.nkpc` equation); wording softened to "same Phillips curve to first order". |
| 2 | MINOR | Degenerate non-vacuity witness | Added `hasDerivAt_loss`, `isLocalMin_of_foc` (FOC sufficient by convexity) and `steady_inflation` (p_n = nπ̄, mc = c(1−β)π̄). |
| 3 | MINOR | Terminal date claimed, not proved | Docstring: terminal condition not formalized. |
| 4 | MINOR | Docstring wording, meaning of c | Clarified (per-date application; c = φ/(ε−1)). |
| 5 | MAJOR | HK "wealth matters when constrained" unproved | Added `constrained_redistribution_matters`. |
| 6 | MINOR | Household riskless holdings / λ | Docstring fixed (excess W − mw riskless; λ = 0). |
| 7 | MINOR | `IsEq` partial; μ in payoff units | Documented. |
| 8 | MINOR | Sharpe "rising with volatility" not stated | Phrase dropped. |
| 9 | MINOR | `premium_strictAnti` scope | Documented. |

Frozen statements: `Audit/Statements/MacroBatch19.lean`.
