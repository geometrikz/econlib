# Review record: behavioral round 9 (2026-11-23)

Modules: `BoundedRationality/ConditionalRegret`, `BoundedRationality/Cursed`,
`BoundedRationality/Analogy`, and a convergence section added to
`BoundedRationality/Replicator`. Frozen statements:
`Audit/Statements/BehavioralIX.lean` (20 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements and the module headers
against Foster–Vohra (1997), Hart–Mas-Colell (2000), Blum–Mansour (2007),
Hofbauer–Schuster–Sigmund (1979), Weibull (1995), Eyster–Rabin (2005), Jehiel
(2005) and Jehiel–Koessler (2008). It checked that `condMatrix` is
row-stochastic, that `crm_balance` is the stationarity condition, the
`2B|Sᵢ|/√T` rate, that `tendsto_ess` carries no extra hypotheses, that the
cursed belief (type-averaged actions, payoff state drawn given own type) is
Eyster–Rabin's, that the ABEE belief averages actions over the class with
prior weights, that `0/0` on null types/classes is harmless, and the lemons
computation (`(2χ − 1)·3/2`).

No major issues. Minor issues and resolutions:

1. "Time-averaged product distribution" ambiguous. **Fixed** wording.
2. `IsReplicatorPath` is on all of `ℝ`; convergence needs only `t ≥ 0`.
   **Documented** (header).
3. `χ` is unrestricted in the cursed definitions and in `lemons_cursed_iff`.
   **Documented** (only `χ ∈ [0, 1]` is meaningful; the iff holds for all `χ`).
4. `exists_mixed_cursed` is plan-level existence for the modified game, not
   Eyster–Rabin behavioral-strategy existence. **Documented.**
5. Eyster–Rabin proposition number unverified. **Fixed:** numbering removed.
6. ABEE "coarsest partition" is coarsest among own-type-fixing partitions
   (Jehiel–Koessler's private-information partition); only pure strategies are
   treated. **Documented** in header and blueprint.

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-23
  ~22:30 UTC (7,388 jobs): success, no warnings.
- `#print axioms` on 84 declarations (64 library + 20 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 4 modules and `Audit.Statements.BehavioralIX` pass.
- `leanexport` + `nanoda` on the 20 frozen theorems: 28,401 declarations, no
  typechecker errors (usual single "Unable to print axioms" message).
- `leanblueprint pdf` and `web` build; every `\lean{}` name in
  `behavioral.tex` (566) resolves.
