# Review record: Doeblin, parametric invariant distributions, Aiyagari (2026-11-23)

Modules: `Macro/DP/Doeblin.lean`, `Macro/DP/ParamInvariant.lean`, `Macro/HA/Aiyagari.lean`,
`doeblin_pow` / `IsStochastic.pow` / `IsInvariant.pow` in `Macro/DP/MarkovChain.lean`, and a
docstring fix to `RCKModel.optimal_capital_converges` (`Macro/Growth/Ramsey.lean`).
Frozen statements: `EconLean/Audit/Statements/Aiyagari.lean` (12 theorems).

## Step 1: context-isolated adversarial review
The reviewer saw only the statements, with proofs and comments stripped (`verify/strip_proofs.py`).

**Round 1** found no false or vacuous statements. Findings:
- **HIGH: `exists_equilibrium` assumed uniqueness and had a degenerate-only witness.**
  - Fixed: uniqueness was dropped (Açıkgöz-style existence via the closed graph of the invariant-measure
    correspondence, `isClosed_invariant_graph`, plus convex mixing).
  - Renamed to `exists_asset_market_clearing`, documented as partial equilibrium (demand curve not derived
    from a firm), and applied to `aiyagariFamily`, where saving earns `r`.
- **MEDIUM: the asset cap `k̄` can create spurious equilibria.** Documented as a gap.
- **MEDIUM: `UniqueStationary` is never derived for a model with a return.** Now used only for continuity
  (`continuous_aggregate`). Documented.
- **LOW: the general-kernel Doeblin uses uniform minorization (SL Thm 11.12 case, not Condition D /
  Thm 11.10).** Docstrings and citations corrected; the periodic-chain non-coverage is noted.

**Round 2** found no HIGH issues and nothing that got worse. Remaining items:
- **MEDIUM: the `aiyagariFamily` market-clearing example checks no economics** (its boundary conditions are
  cheap). Now labelled "existence check only".
- **MEDIUM: there is no guard `r_hi < 1/β - 1` against the cap binding.** Documented, not enforced.
- **LOW: `hhi` was required for every stationary distribution.** Weakened to "some stationary distribution"
  (a strictly stronger theorem).
- **LOW: the name overstated the result.** Renamed (see HIGH above).

**Still open:**
- General equilibrium with Cobb–Douglas firm, wage and labor clearing.
- Deriving the upper boundary condition (supply diverges as β(1+r)→1).
- Endogenous asset bound.
- Uniqueness from primitives (Hopenhayn–Prescott monotone mixing).
- A non-degenerate stationary distribution.
- SL Condition D for general kernels.

## Step 2: reverifiers
- Full `lake build`: 6520 jobs, warning-free.
- `#print axioms` on all 12 frozen theorems: `[propext, Classical.choice, Quot.sound]` only.
- `leanchecker` exits 0 on Doeblin, ParamInvariant, Aiyagari, MarkovChain, Ramsey and Audit.Statements.Aiyagari.
- `nanoda` on the export of the 12 frozen theorems: 37,922 declarations checked with no typechecker errors.
  The only message is the benign "Unable to print axioms" printer note.
