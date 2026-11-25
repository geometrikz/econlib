# Review: GE/ContinuumEconomy.lean (Aumann continuum economy; Walrasian ⊆ core)

Context-isolated adversarial review (2026-11-25): no soundness problem.
Definitions match Aumann (1964) (∫x = ∫e; blocking with ∫_S y = ∫_S e and a.e.
member strictly better); `IsWalrasianEquilibrium.inCore` holds with no
nonatomicity, monotonicity, rationality or sign restriction on p.

Fixes applied:
1. Header no longer claims the converse is formalized; it is future work, with
   the hypotheses it will need listed.
2. Header notes the structure allows any μ (μ = 0 is degenerate); finite and
   nonatomic is the intended application.
4. Added `linContinuum_blocks_zero` / `linContinuum_zero_not_inCore`, showing
   `Blocks` is satisfiable; witness renamed `linContinuum` (name clash).
Advice recorded for the converse (item 3): keep equality blocking but prove an
upgrade lemma from ≤-blocking under monotonicity; add measurability of
preferences, μ finite and nonatomic, ∫e ≫ 0 as hypotheses there.

Mechanical checks: axioms standard only, leanchecker OK, nanoda OK, frozen
statements in Audit/Statements/Lyapunov.lean build.
