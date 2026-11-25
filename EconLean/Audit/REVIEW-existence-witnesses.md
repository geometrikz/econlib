# Review: GE/ExistenceWitnesses.lean (production existence: disposal and several firms)

Context-isolated adversarial review (2026-11-25): `badEconomy` is a sound,
non-vacuous witness (all hypotheses of the free-disposal existence theorem hold;
exact clearing fails at every p ≥ 0, including p = 0).

Fixes applied:
1. (Medium) ∃ vs ∀: added `badEconomy_excess_supply` (every free-disposal
   equilibrium at p ≥ 0 has strict excess supply); docstrings reworded.
2. (Medium-low) Qualified "at nonnegative prices" and added
   `badEconomy_negativePrice_equilibrium` (autarky clears exactly at p = (1, −1)).
3. (Medium) The two-firm witness had identical CRS firms (relabelled one-firm
   economy). Firm 1 is now the capacity-constrained `capSet`, which earns positive
   profit (`capSet_positive_profit`), so shares matter; aggregate technology is
   strictly larger than either firm's (`twoFirmEconomy_aggProd_ne`); NFL and
   irreversibility proved for the sum.
4. Dropped the unused "free-disposal firms" emphasis.
5. Noted that `badEconomy` shows the `hfd` hypothesis of
   `exists_walrasianEquilibrium_arrowDebreu_lns` cannot be dropped.

Mechanical checks: axioms standard only, leanchecker OK, nanoda OK, frozen
statements in Audit/Statements/GE.lean build.
