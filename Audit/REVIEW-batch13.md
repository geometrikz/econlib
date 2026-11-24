# Review record: batch 13 (HM optimality, assignment-game prices, Levin hidden effort)

## Modules
- `Matching/ContractsLattice` (new). The header of `Matching/Contracts` is also updated.
- `Cooperative/AssignmentLattice` (new). The header of `Cooperative/Assignment` is also updated.
- `Contracts/RelationalMH` (new).

Frozen statements: `Audit/Statements/Batch13.lean`, 15 theorems.

## What is proved

**Matching with contracts.** Both sides satisfy substitutes and IRC.
- `stable_isFixedPoint`: every stable allocation comes from a fixed point of the Hatfield–Milgrom map. This is the converse half of the fixed-point theorem.
- `doctor_optimal` / `hospital_optimal`: there is a stable Y* such that C_D(Y* ∪ Y) = Y* for every stable Y. The hospital version is symmetric.

**Assignment game.**
- `isCorePayoff_iff`: core payoffs, written as (u, p), are exactly the core.
- `core_sup_inf`: the core is a lattice.
- `buyer_optimal_core` / `seller_optimal_core`: buyer-optimal and seller-optimal points exist. Each is worst for the other side.
- `core_slack`: complementary slackness.
- `compEq_core`: competitive equilibria are efficient and in the core.
- `core_compEq`: core prices together with any optimal matching are competitive.
- `compEq_prices_iff`: competitive prices are exactly core prices.
- `exists_min_compEq_prices`: minimal competitive prices exist, and they are the prices at the buyer-optimal core point.
- Witness: a 1×1 market.

**Levin, hidden effort, stationary contracts.**
- `statContract_iff_range`: a stationary contract enforces effort iff the bonus range is at most δ/(1−δ)·surplus.
- `one_step_bound`: one-step bonuses are optimal against a single deviation.
- `two_effort_iff`: the two-effort sustainability criterion.
- Witnesses: sustainable at δ = 2/3, not sustainable at δ = 1/3.

## Check 1: isolated adversarial review (2 rounds, proofs stripped)

**Round 1.** Three independent reviewers, one per module. No Major findings. All Minor findings were fixed:
- HM:
  - unverified theorem numbers dropped;
  - docstrings now match the ∃ statements;
  - stale "not formalized" text and the deferred-acceptance direction corrected in Contracts.lean;
  - added a note that the witness has a unique stable allocation.
- Assignment:
  - added `compEq_prices_iff`;
  - tied the minimal prices to the buyer-optimal point in the statement;
  - stated the normalization;
  - reworded "opposed interests";
  - updated the stale text in Assignment.lean;
  - added the 1×1 witness.
- Levin MH:
  - noted that nonnegativity of f is unused;
  - moved surplus ≥ 0 into the right-hand side of the iff;
  - softened the one-step claim;
  - re-attributed to "stationary-contract version" and "two-effort specialization";
  - made the witness interior.

**Round 2.** One reviewer confirmed all items resolved and found no Major issues. Four Minor docstring items were fixed:
- the header wording for the HM ∃ statements and `stable_exists`;
- dropped the LAD attribution;
- the witness wording now says "in the core" rather than "optimal";
- dropped an unverified survey attribution.

Not done: a witness with two distinct stable allocations for HM. It is optional, and it is noted in the header.

## Check 2: kernel and axioms
- Full shared build is green and warning-free (7804 jobs).
- Axioms: only propext, Classical.choice and Quot.sound, on all 15 theorems and their 15 frozen copies.
- leanchecker exits 0 on the 3 new modules, the 2 updated modules and the frozen file.
- nanoda found no typechecker errors (18,026 declarations).
- The Comparator stand-in is the frozen-statements file.
- `leanblueprint pdf` builds. New blueprint entries:
  - matching.tex: `thm:hm-optimal`
  - cooperative.tex: `thm:assignment-lattice`
  - asyminfo.tex: `def:stat-contract`, `thm:levin-mh`
