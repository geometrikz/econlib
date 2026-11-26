# Review: behavioral round 30 (DeGroot naive learning, catalog A11.2)

File: `EconLean/Behavioral/DeGroot.lean` (namespace `Econ.DeGroot`).
Frozen statements: `EconLean/Audit/Statements/BehavioralXXX.lean` (15 theorems).
Blueprint: `thm:beh-degroot` (new section "Naive social learning" in behavioral.tex).

## Step 1: adversarial statement review (context-isolated agent)
No MAJOR findings (conventions checked: row-stochastic T, T *ᵥ p update, left
eigenvector π ᵥ* T = π, (T^t) i j → π j; empty-agent edge cases handled by
`[Nonempty ι]`). MINOR findings, all addressed:
1. `influence_degree` needs no nonnegativity: docstring and header now say so.
2. Missing non-vacuity witness for `consensus_degree`: added `normalize_ones`
   (normalized complete graph = `half`, which is stochastic and primitive).
3. `swap` shows *aperiodicity* is needed (it is strongly connected, period 2);
   header reworded, and it states only agent 0's belief fails to converge.
4. Header citations made section-level; "Not covered" now lists the general
   converse (periodic ⇒ non-convergence for some p).
5. Uniqueness is among probability vectors: stated in header and docstring.

## Step 2: mechanical checks
- Full `lake build EconLean` on the shared tree: success (8010 jobs), no warnings.
- `#print axioms` on 15 library + 15 frozen theorems: only propext, Classical.choice, Quot.sound.
- leanchecker: DeGroot and BehavioralXXX pass.
- leanexport + nanoda: 14892 declarations, no typechecker errors.
