# Review: SMD step 2 (`Bridges/Aggregation/SMDConsumer.lean`), 2026-11-24

## Step 1: context-isolated adversarial statement review
Verdict: **faithful, with caveats**. No blocking findings.

Confirmed by the reviewer:
- Quantifiers are sound: utilities and endowments are chosen before `∀ p ∈ K`.
- `demand (prefOf U) p (cost p ω) = {x}` is single-valued Walrasian demand on ℝ^L₊ at income p·ω, and
  `∑ (x l − ω l) = z p` is aggregate excess demand.
- A compact `K ⊆` open simplex generalizes Debreu's `S_ε`.
- The `zBad` example is non-vacuous: compact domain, continuity, Walras' law, and a proved WARP failure.
- A trivial utility cannot satisfy the statement.

Findings and resolution:
1. *should-fix:* the constructed utility is **provably** discontinuous, non-monotone and satiated (`u = −2` off the bounded
   set `C_1`). The docstring read as if this was merely unproven.
   **Fixed:** the module docstring now says it plainly and names the open item: standard consumers need a different
   utility (Geanakoplos 1984 or Mantel 1974).
2. *should-fix:* strict convexity was not named as missing. **Fixed:** it is now in the scope/caveat paragraph.
3. *should-fix:* the unqualified theorem name overclaimed. **Fixed:** renamed to
   `sonnenschein_mantel_debreu_quasiconcave`, with a caveat in the docstrings of it and of `exists_consumer_weightedPiece`.
4. *should-fix:* the `zBad_rational_consumers` docstring needed the caveat. **Fixed.**
5. *note:* endowments were only `≥ 0`. **Fixed:** `ω = max b 1 · 𝟙`, and the statements now say `∀ i, 0 < ω i`.
6. *note:* individual budget exhaustion comes from `p · y(p) = 0`, not from nonsatiation. **Documented** in the module
   docstring.
7. *note:* homogeneity. **Documented:** normalization plus `demand_smul`.
8. *note:* `pieceUtility_lt` and `quasiconcaveOn_pieceUtility` are accurate. No change.

## Step 2: machine checks
- Build: `lake build` is warning-free.
- `#print axioms` for the frozen headline statements: `propext`, `Classical.choice`, `Quot.sound` only.
- `lake env leanchecker EconLean.Bridges.Aggregation.SMDConsumer`: exit 0.
- nanoda on the frozen statements: 16297 declarations, no typechecker errors. Its single pretty-printer message
  ("Unable to print axioms") also appears on earlier batches.
- Frozen statements: `Audit/Statements/Aggregation.lean`, `section SMDConsumer`.
