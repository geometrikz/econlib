# Adversarial review: macro batch 8 (money and credit)

Files: `Macro/MoneySearch/KiyotakiWright.lean`, `Macro/MoneySearch/LagosWright.lean`,
`Macro/Credit/KiyotakiMoore.lean`, `Macro/Credit/CostlyStateVerification.lean`.

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-23.
No contradictory or unsatisfiable hypothesis sets were found; the algebra of
`delta_eq` and `monetary_iff` was checked by hand.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| CSV-1 | blocking | `debt_optimal` proved only dominance (debt with face `R(ω₀)` repays *more*), which hurts the entrepreneur; not optimality. | Renamed to `debt_dominates_expected`. New `debt_optimal`: for every IC+LL contract some debt contract has the *same* expected repayment and weakly lower verification cost (face value lowered by the intermediate value theorem). New `debt_optimal_pc`: with the lender's participation constraint net of verification costs (`LenderPC`), debt also satisfies it and gives the entrepreneur the same expected payoff. |
| CSV-2 | should-fix | Contracts that verify every state were never compared. | `debt_optimal` has no unverified-state hypothesis; the all-verified case uses face value `max S`. |
| CSV-3 | nit | `IsIC` silently assumes detected lies are punishable. | Stated in the docstring. |
| CSV-4 | nit | Returns may be negative. | Stated in the docstring (not needed for the results). |
| KW-1 | should-fix | Only pure strategies. | Added `IsMixedEq` and `mixed_iff`: a mixed equilibrium exists iff the monetary condition holds strictly. |
| KW-2 | nit | Timing differs from KW93; symmetric `Π`. | Docstring names the produce-on-demand textbook variant and symmetry. |
| LW-1 | should-fix | θ = 1 and `q = z` hard-coded. | Docstring states θ = 1, linear cost, and that `q = z` (not `min(z, q*)`) only matters for `i ≤ 0`; the θ < 1 hold-up is listed as not formalized. |
| LW-2 | should-fix | No existence: conditional theorems could be vacuous. | Added `exists_optimal`: an optimum exists for `0 ≤ i < σ(u'(a) − 1)` (Darboux's theorem). |
| LW-3 | nit | `i < 0` non-existence not shown; redundant `hq`. | Non-existence for `i < 0` documented as not formalized (needs the `min(z, q*)` objective). `hq` kept (harmless). |
| KM-1 | should-fix | No feasibility (`k ≥ 0`); `K̄` naming. | Added `kEq_nonneg_iff` (`k ≥ 0` iff net worth at `q₀` is ≥ 0); docstring says `K̄` is entrepreneurs' inherited land and `d` stands for the user cost. |
| KM-2 | nit | Amplification is static only. | Renamed "Amplification (static)" in docstrings; dynamic persistence listed as not formalized. |

Checks after fixes: all four files compile warning-free; `#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`; leanchecker and nanoda pass.
