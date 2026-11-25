# Review: GE/ExistenceAggregateDisposal.lean (exact clearing under aggregate free disposal)

Context-isolated adversarial review (2026-11-25): no correctness problems; no
vacuous or contradictory hypotheses; `disposalEconomy` genuinely separates
aggregate from single-firm free disposal (aggregate = nonpositive orthant;
equilibrium necessarily disposes of the bad).

Fixes applied:
1. (Medium) Attribution: the hypothesis is the MWG 5.B.2(vi) form `Y − ℝᴸ₊ ⊆ Y`
   applied to the aggregate; Debreu 1959 §3.3(e)/§5.7(b.4) assumes only `−Ω ⊆ Y`
   (equivalent under additivity). Docstrings and blueprint now say so; the
   literal Debreu form is noted as not covered.
2. (Low) `hnfl` was redundant; dropped, and derived via new
   `noFreeLunch_of_freeDisposal` (free disposal + irreversibility + inaction).
3. Header lists the remaining differences from Debreu §5.7 (closed convex Yⱼ
   rather than Y, ℝᴸ₊ consumption, ω ≫ 0, continuous utilities).
4. Citation "MWG §17.B" replaced by "MWG ch. 17 and its appendix on production".

Mechanical checks: axioms standard only, leanchecker OK, nanoda OK, frozen
statements in Audit/Statements/GE.lean build.
