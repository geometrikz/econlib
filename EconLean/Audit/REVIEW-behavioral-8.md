# Review record: behavioral round 8 (2026-11-23)

Modules: `BoundedRationality/RegretMatching`,
`BoundedRationality/SelfConfirming`, `BoundedRationality/Replicator` (plus a
docstring fix in `BoundedRationality/NoRegret`). Frozen statements:
`Audit/Statements/BehavioralVIII.lean` (22 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements against Blackwell (1956),
Hart–Mas-Colell (2000, 2001), Fudenberg–Levine (1993), Battigalli (1987),
Taylor–Jonker (1978), Hofbauer–Schuster–Sigmund (1979) and Weibull (1995). It
checked the orthant-potential bound and the per-step increment `|A| M²`, that
`rm` is the canonical rule, that regrets use `uᵢ(a, σ₋ᵢ) − uᵢ(σ)` with all
players updating simultaneously, that `avgDist` and `regrets` sum over the
same periods (including `T = 0`), the `2B √|Sᵢ| / √T` rate, the `Confirmed`
condition, the replicator equation, the KL argument order and the sign of the
Lyapunov derivative, and satisfiability of `IsReplicatorPath`.

No major issues. Minor issues and resolutions:

1. Regret matching here is the unconditional, expected-payoff variant, which
   gives CCE, not Hart–Mas-Colell's conditional/CE theorem. **Documented** in
   the headers of `RegretMatching` and `NoRegret` and in the blueprint.
2. `isNash_of_isSCE` required `y i` injective on whole profiles, which
   excludes the canonical perfect feedback `y i s = s₋ᵢ`. **Fixed:** the
   hypothesis is now "given the own action, the observation identifies the
   profile".
3. `sce_not_nash` relies on players not observing their own payoffs.
   **Fixed:** added `sce_not_nash_ownPayoff` (Safe/Risky game) with
   `ownPayoff_observed`.
4. Fudenberg–Levine is extensive-form; the normal form with feedback is
   Battigalli's conjectural equilibrium. **Documented.**
5. `lyapunov_strictAnti` needs `∀ t, x t ≠ x*` (equivalent by ODE uniqueness
   to `x 0 ≠ x*`), and convergence `x(t) → x*` is not stated. **Fixed / documented:**
   added `lyapunov_antitone` without that hypothesis; the header states that
   convergence (LaSalle) is not formalized.
6. Only rest points witness `IsReplicatorPath`. **Documented** (replicator
   flows are complete and preserve the open simplex; no non-constant solution
   is constructed).
7. `∑ x t i = 1` in `IsReplicatorPath` is redundant. Kept (harmless).

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-23
  ~21:30 UTC (7,360 jobs): success, no warnings.
- `#print axioms` on 89 declarations (67 library + 22 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 4 modules and `Audit.Statements.BehavioralVIII` pass.
- `leanexport` + `nanoda` on the 22 frozen theorems: 28,200 declarations, no
  typechecker errors (usual single "Unable to print axioms" pretty-printer
  message).
- `leanblueprint pdf` and `web` build; every `\lean{}` name in
  `behavioral.tex` (513) resolves.
