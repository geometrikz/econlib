# Adversarial review: macro batch 9 (information, wage posting, external finance)

Files: `Macro/Information/LucasIslands.lean`, `Macro/Information/MorrisShin.lean`,
`Macro/Labor/BurdettMortensen.lean`, `Macro/Credit/ExternalFinancePremium.lean`.

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-23.
Formulas checked by hand: Lucas weight `V_z/(V_p+V_z)`; MS weight `α/(α+β(1−r))`, loss
(MS eq. 16) and both derivatives; BM offer distribution, top wage, firm size and limits;
uniform BGG schedule.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| BGG-1 | blocking | "Premium" `D/L` was a default spread, present even with `μ = 0`; not BGG's agency-cost premium. | Renamed to `contractRate_strictMono`. Added monitoring cost `m` to `Schedule` and `efp = (g + m)/L = 1 + m/L`; `efp_eq_one_iff` (premium is 1 iff no monitoring cost, MM), `one_lt_efp`, `uniform_efp_zero`; `uniform_efp_strictMono` / `uniform_efp_anti_netWorth` require `μ > 0`. |
| BGG-2 | should-fix | Monotonicity/concavity of `g` assumed. | Documented as reduced-form (verified for the uniform case); hazard-rate derivation listed as not formalized. |
| BGG-3 | nit | Normalizations. | Safe rate 1 and return support `[0,1]` documented. |
| LI-1 | should-fix | `anticipated_neutral` true by definition (no demand, `p̄` exogenous). | Removed. Added aggregate demand `y = m − p` (`IsEqPrice`), `isEqPrice_iff`, `output_eq`, `rational_expectations` (`E p = p̄` iff `p̄ = E m`), `output_zero_iff` (only money surprises move output). |
| LI-2 | nit | Linear predictor = conditional expectation only under Gaussian shocks. | Documented. |
| LI-3 | nit | `V_p` exogenous. | Documented (`V_p = V_m/(1+bθ)²` in equilibrium, not formalized). |
| MS-1 | should-fix | Sign results were about a written-out fraction, not the derivative. | Restated with `deriv`: `public_info_harmful_iff`, `public_info_helps_of_le_half`, `private_info_helps`. |
| MS-2 | nit | `hr0 : 0 ≤ r` too strong. | Weakened to `-1 < r`. |
| MS-3 | nit | Harmful region not shown non-empty. | Added `harmful_region_nonempty` (`r = 3/4, α = 1, β = 16`). |
| MS-4 | nit | Uniqueness only among linear equilibria. | Docstring says "linear". |
| BM-1 | should-fix | `l` used the raw `F` off the support; `profit_eq` claimed equal profit for all `w < p`; deviation below `b` missing. | `Fc` clamps `F` to `[0,1]`; `l = 0` below `b`; `profit_eq` restricted to `[b, w̄]`; new `isEquilibrium`: `∀ w`, profit ≤ common level, with equality on the support. |
| BM-2 | nit | Uniqueness not formalized; equal on/off-the-job offer rates. | Documented. |

Checks after fixes: all four files compile warning-free; `#print axioms` standard
only; leanchecker and nanoda pass.
