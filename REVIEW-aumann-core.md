# Review: GE/AumannCore.lean (batch 4b, Aumann 1964 core ⊆ Walrasian)

Context-isolated adversarial review against Aumann (1964), Hildenbrand (1974). No blockers. Reviewer confirmed:
hcont/hmeas reasonable and correctly implied by the canonical hypotheses; conclusion (p ≫ 0, demand at wealth p·e(a), a.e.)
is the right one; [Nonempty ι] + ∫e ≫ 0 rule out μ = 0; standard axioms only.

Applied:
1. (should-fix) Stale "future work" header in ContinuumEconomy.lean: now points to AumannCore.lean.
2. (should-fix) Joint (graph) measurability attributed to Hildenbrand 1974; Aumann's pairwise axiom noted, with hmeas its
   special case.
3. (should-fix) Witness reworded ("canonical hypotheses hold"), and added a non-convex, trader-dependent witness
   `bumpContinuum` (utility max(z₀,z₁) + (1+a²)(z₀+z₁)) with `bumpContinuum_not_convexPref` and
   `bumpContinuum_inCore_iff`.
4. (nit) "Hypotheses vs. the literature" paragraph: completeness used only for demand, closed upper sets unused,
   strong monotonicity used for p ≫ 0, quasi-equilibrium version not formalised.
5. (nit) "weakest form" replaced by "allocation-specific weakening (depending on x)".
6. (nit) hR for every trader: noted in the doc (not weakened).
7. (nit) Docstring of inCore_iff explains that p ≫ 0 loses nothing under strong monotonicity.
8. (nit) ContinuumEconomy doc notes equality vs free-disposal feasibility equivalence under strong monotonicity.

Checks: warning-free; #print axioms = [propext, Classical.choice, Quot.sound] for all 9 headline theorems; leanchecker exit 0;
nanoda 37049 declarations, no typechecker errors. Frozen statements: Audit/Statements/Lyapunov.lean section AumannCore.
