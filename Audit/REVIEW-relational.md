# Review record: relational contracts (batch 12)

Module: `Contracts/Relational` (new directory `EconLean/Contracts`). Frozen statements: `Audit/Statements/Relational.lean`, which holds 4 theorems.

## What is proved
The setting is the observable-effort benchmark of Levin (2003), in the MacLeod–Malcomson (1989) setting.
- `IsSelfEnforcing` requires:
  - the Bellman recursions, with bounded continuation values;
  - participation;
  - the agent's effort constraint against every deviation;
  - both bonus-payment constraints.
- `stationary_selfEnforcing`: if (1−δ)c(e) ≤ δ s(e), every nonnegative split of the surplus is supported by a stationary contract.
- `selfEnforcing_dynamic`: c(e_t) ≤ δ(U_{t+1} + P_{t+1}). Only joint surplus matters.
- `levin_stationary_optimal`: stationary contracts are optimal at every date. This needs finitely many efforts.
- `constant_effort_iff`: a constant effort is sustainable iff (1−δ)c ≤ δ s.
- Witnesses:
  - high effort is sustainable at δ = 1/2 and not at δ = 1/10;
  - the bound applies at δ = 1/2;
  - the optimum is high effort.

## Check 1: isolated adversarial review (2 rounds, proofs stripped)
**Round 1.** No Major findings. Minor findings, all fixed:
- The docstring now explains why boundedness is harmless.
- The "any split" wording is corrected.
- Added a witness that exercises the optimality theorem.
- Dropped an uncertain section citation.
- The header now says this is the observable-effort benchmark, not Levin's main hidden-effort model.
- The randomization remark is labelled informal.

**Round 2.** All six items are confirmed resolved, and there are no Major findings. Minor findings, all fixed:
- Added a sharper witness: the optimum is high effort.
- The header now notes that only the optimality theorem uses finitely many efforts.
- Clarified the `stationaryRel` docstring.

## Check 2: kernel and axioms
- Full shared build is green (7792 jobs) and warning-free.
- Axioms: only propext, Classical.choice and Quot.sound, on 4 theorems plus 4 frozen copies.
- leanchecker exits 0 on `Contracts.Relational` and on `Audit.Statements.Relational`.
- nanoda found no typechecker errors across 11,678 declarations.
- Comparator stand-in: the frozen-statements file.
