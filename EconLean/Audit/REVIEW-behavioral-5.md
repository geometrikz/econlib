# Review record: behavioral round 5 (2026-11-23)

Modules: `Behavioral/BeliefRule`, `Behavioral/CognitiveDiscounting`,
`Behavioral/DiagnosticExpectations`, `Behavioral/Overconfidence`,
`Behavioral/MotivatedBeliefs`, `Behavioral/NarrowBracketing`,
`Behavioral/MarketInequity`. Frozen statements:
`Audit/Statements/BehavioralV.lean` (53 theorems).

## Step 1: adversarial statement review

A context-isolated reviewer read the stripped statements (all proofs replaced
by `sorry`) against Gabaix (2020), Bordalo–Gennaioli–Shleifer (2018),
Bordalo–Gennaioli–Ma–Shleifer (2020), Coibion–Gorodnichenko (2015),
Brunnermeier–Parker (2005), Tversky–Kahneman (1981), Thaler (1985) and
Fehr–Schmidt (1999). It recomputed by hand the NK forward matrix, determinant,
trace and determinacy index (matching Gabaix's condition after σ ↦ 1/σ), the
FE/FR covariances and the BGMS CG coefficient, and the diagnostic price IRF.

No major issues. Minor issues and resolutions:

1. Forward-guidance results are partial equilibrium (IS block, exogenous real
   rate, terminal condition imposed), not Gabaix's GE statement. **Fixed:**
   documented as such in the module header and blueprint.
2. `fg_knife_edge` overclaimed in its name. **Fixed:** renamed
   `fg_eventually_below_half`, docstring states it against `fg_puzzle_rational`.
3. `cognitive m` is horizon-independent shrinkage, not Gabaix's `m^h`; CG's
   positive coefficient comes from information frictions. **Fixed:** docs say
   "uniform underreaction", with the caveat.
4. `fe_orthogonal_iff` had an unneeded `0 < v`. **Fixed:** dropped (proof uses
   the `ε_{t−1}` direction instead of `x_{t−2}`).
5. Narrow-bracketing witness was only weakly monotone with saturation and no
   loss aversion. **Fixed:** new witness `max (min x (270 + x/10)) (−630 + x/10)`,
   strictly increasing and loss-averse; `narrow_choices_exist` now requires
   `StrictMono`, loss aversion, and includes the dominance conclusion for the
   same `v`.
6. Rabin–Weizsäcker general theorem not formalized. **Fixed:** attribution
   reworded (only the TK example is formalized).
7. `competitive_offer` gives only necessity. **Fixed:** added
   `competitive_no_outbid` (at `s = 1` outbidding strictly hurts); downward
   deviations and acceptance convention documented.
8. `overprecision` is nearly immediate. Documentation only; kept.
9. `rational_not_optimal` had a free derivative `r` forced to 0; reduced form.
   **Fixed:** hypothesis is now `DifferentiableAt ℝ R q`; reduced form
   documented.

## Step 2: mechanical checks

- Full `lake build EconLean` (with the shared tree as of 2026-11-23 11:50 UTC,
  including the BerkNash `open Real` fix): success, no warnings.
- `#print axioms` on all 121 theorems (68 library + 53 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 7 modules and `Audit.Statements.BehavioralV` pass.
- `leanexport` + `nanoda`: 19,873 declarations checked, no typechecker errors
  (the usual single "Unable to print axioms" pretty-printer message).
