# Review: macro batch 17 (AMSS / Barro tax smoothing, Lucas–Stokey with general utility)

Context-isolated adversarial referee, 2026-11-25, on docstrings, definitions and statements.
Verified by hand: risk-free Euler equation, quadratic minimizer b* = R(g₀+b₀−Eg)/(1+R),
complete-markets Euler equation, Arrow prices π_s/R (no arbitrage), implementability derivative,
tax formula.

| # | Sev. | Item | Resolution |
|---|------|------|------------|
| 1 | MAJOR | `history_independence` multipliers not tied to l₀ (trivial with (a,b)=(0,1)) | Conclusion now includes `∀ n, Phi a b (g n) (l₀ n) = 0`. |
| 2 | MAJOR | Uniqueness over all ℝ is vacuous for even γ | Uniqueness only on l > 0, c > 0; l₀ interior assumed. |
| 3 | MAJOR | `Prefs` required differentiability on all ℝ (excludes log/CRRA) | Derivatives now only required on (0, ∞); `ramsey_foc` assumes interior l₀. |
| 4 | MAJOR | Non-vacuity only at slack first best | Added `distortionary_witness` (γ=1, l≡c∈(1/2,1), binding constraint, tax 1−c>0), proved as a global max on the constraint set. |
| 5 | MINOR | Fritz John multipliers | Documented; normal form not stated. |
| 6 | MINOR | LSG docstring overstated | Setting rewritten; consumption equality added to the conclusion. |
| 7 | MINOR | `rf_spread` is a terminal-date artifact | Docstring says so. |
| 8 | MINOR | Attribution; revenue vs rate | Docstring: revenue level; AMSS refinements not formalized. |
| 9 | MINOR | No CM witness | Documented as a deviation; `cm_le_rf` added instead. |
| 10 | MINOR | No link between market structures | Added `costCM_const`, `cm_le_rf`. |
| 11 | MINOR | No sign on β | Harmless (β = 1/R wherever used); left. |

Frozen statements: `Audit/Statements/MacroBatch17.lean`.
