# Review: endogenous asset bound (Macro/HA/AssetBound.lean)

Frozen statements: `EconLean/Audit/Statements/AssetBound.lean` (9 theorems).

## Reverifiers
- `#print axioms`: all 9 use only propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on EconLean.Macro.HA.AssetBound and EconLean.Audit.Statements.AssetBound.
- nanoda: no typechecker errors (≈37.7k declarations).
- Full `lake build` warning-free; blueprint PDF 0 undefined references; all 31 `\lean` names exist.

## Adversarial statement review (context-isolated)
No MISMATCH, no VACUOUS-RISK. OK: EulerGap is a faithful difference form of βR u'(c−y) < u'(c);
A depends only on u, β, R, ȳ (kbar appears only in `A < kbar`); hypotheses satisfiable; example
arithmetic checked (A = 15 vs needed ≥ 14.34; A = 40 vs needed ≥ 35.84; w(1/10) = 5/4); income risk genuine.

Findings and responses:
1. WEAK: examples stated support only for some invariant μ. Fixed: now ∀ invariant ν.
2. WEAK: Inada hypothesis excludes log / CRRA σ ≥ 1 (Aiyagari's preferences). Documented; the
   bounded-DP framework already requires u finite at 0.
3. Scope: R > 1 only (R = 1 open), i.i.d. income only, borrowing limit 0. Documented.
4. "Slack" = cap never binds and bound independent of kbar; equality with the uncapped [0,∞) problem
   is not proved. Documented.
5. No GE packaging: A depends on r; no uniform bound over [rlo, rhi]; equilibrium r not located; a GE
   witness with both boundary conditions derived and slack cap is open (needs supply divergence as
   β(1+r) ↑ 1). Documented.
6. Minor (redundant hgc/hgm, unnecessary-looking `ybar/R ≤ a`, impatient βR = 0.55 examples): noted, unchanged.
