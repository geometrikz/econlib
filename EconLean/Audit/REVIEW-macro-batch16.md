# Review: macro batch 16 (Lagos–Wright bargaining, dynamic Kiyotaki–Moore, Lucas–Stokey)

Context-isolated adversarial referee, 2026-11-25, on statements and definitions only.
The referee verified by hand: the generalized Nash payment and its slope at q*, the hold-up sign,
the Kalai payment and FOC, the forward solution of the KM pricing equation (witness
ψ=1, R=2, λ=1/2, K̄=1, d=2), and the Lucas–Stokey implementability constraint, tax formula and FOC.

| # | Sev. | Item | Resolution |
|---|------|------|------------|
| 1 | MAJOR | DKM persistence assumed (λ^t built into `PriceEq`) | Holdings are now a sequence with explicit `HoldingsEq` law of motion; `holdings_eq` proves k_t = λ^t k_0; docstring states λ is exogenous and that `persistence` shows prices inherit it. |
| 2 | MINOR | DKM attribution and η notation | Docstring now "stylized linearization", not KM's equations; η renamed ψ. |
| 3 | MAJOR | `holdup` only "not a local max" | Added `nashObj_deriv_star` (explicit negative derivative) and `holdup_lt` (any best choice on (0, q*] is < q*). |
| 4 | MINOR | Nash formula valid only for q ≤ q* | Documented; global statement restricted to (0, q*]. |
| 5 | MINOR | `kalai_mono_theta` lacks θ₂ ≤ 1 | Added. |
| 6 | MINOR | Kalai Friedman rule possibly vacuous | Added `kalai_friedman_attained`. Existence for i > 0 not proved (documented). |
| 7 | MINOR | `hsurplus` rationale | Documented (what u(0)=0 would give). |
| 8 | MINOR | LS: constancy is a quasilinearity artefact | Documented vs. general history-independence result. |
| 9 | MINOR | LS: no debt, no witness, finite truncation | Documented; added `first_best` non-vacuity witness (l ≡ 1, zero tax). |
| 10 | MINOR | Fritz John multipliers | Documented which multiplier is which. |

All findings resolved. Frozen statements: `Audit/Statements/MacroBatch16.lean`.
