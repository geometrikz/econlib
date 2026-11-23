# Review record: producer theory (MWG Ch. 5) and uncertainty (MWG Ch. 6) — 2026-11-23

Files: `EconLean/Producer/{Production,Cost,Aggregation}.lean`,
`EconLean/Uncertainty/{VNM,MoneyLottery,RiskAversion,Pratt,StochasticDominance}.lean`.
Frozen statements: `EconLean/Audit/Statements/ProducerUncertainty.lean` (26 headline theorems).

Prior work checked: J. Li, arXiv 2506.07066 (vN–M in Lean 4). Its representation
theorem is a sketch with placeholder code and an axiom, so nothing was reused; `VNM.lean`
is an independent complete proof.

## Step 1: context-isolated adversarial review (two rounds)
Reviewers saw only statements (proofs and comments stripped) plus the definitions they
depend on; reference MWG Ch. 5–6.

**Round 1: no statement wrong.** Findings and resolution:

| # | Finding | Resolution |
|---|---|---|
| 1 | Pratt (6.C.2) lacked the Arrow–Pratt clause (i) | Added `arrowPratt_le_iff_moreRiskAverse` (`Pratt.lean`): r_A(u₂) ≥ r_A(u₁) ∀x ⟺ `MoreRiskAverse u₂ u₁`, via Cauchy MVT and limits of slopes |
| 2 | 6.D.2 only one direction (MPS ⟹ SOSD ⟹ integrated CDF) | Open: converses (Rothschild–Stiglitz) listed below |
| 3 | Hotelling / Shephard only the envelope direction (differentiability assumed, as MWG's proof does) | Open: "unique supply ⟹ differentiable" listed below |
| 4 | `costFunction_concave` needed minimizers | Added `concaveOn_costFunction`: `ConcaveOn` on `w ≥ 0` given only feasibility |
| 5 | `profit_aggregate` needed attained maxima | Now needs only nonempty `Yⱼ` with bounded profits; old version kept as `profit_aggregate_of_supply` |
| 6 | Junk values (0 for MWG's ±∞) undocumented | Documented in `Production.lean` and `Cost.lean` headers |
| 7 | `HasEURepresentation.unique` had an unneeded nontriviality hypothesis | Removed (total-indifference case proved) |
| 8 | Finite-support lotteries; `RiskAverseOn` meant for convex `I`; CRS hypothesis on z < 0 | Documented; `costFunction_crs` now assumes homogeneity only for z ≥ 0 |
| 9 | Missing non-vacuity witnesses | Added: MPS (coin flip vs δ₀), 5.F.2 (half-space technology), aggregation (two free-disposal firms), CARA ranking for Pratt |
| 10 | Namespace `Econ.Finset.exists_top_of_total` | Renamed `exists_top_of_total_finset` |

**Round 2 (changed and new statements): no statement wrong.** All faithful; minor notes:
`costFunction_crs` is true unconditionally but only `0 = q·0` off the feasible set
(documented); the MPS and 5.F.2 witnesses are valid but simple (sanity instances).

## Step 2: proof checks
- `#print axioms` on all 26 headline theorems: `propext, Classical.choice, Quot.sound` only. No `sorry`.
- `leanchecker` (toolchain `bin/`): exit 0 on each of the 8 modules (one module per call).
- `nanoda_bin` 0.4.17 on a `leanexport` of all 26 headline theorems and their closure:
  38,152 declarations, no typechecker errors.
- Comparator: unreachable from the cloud container; stand-in is the frozen-statements file.
- Full `lake build` warning-free.

## Open (not yet formalized)
- 5.C.1: recover Y from π; strictly convex Y ⟹ single-valued supply; D²π symmetric PSD;
  Hotelling/Shephard "unique optimizer ⟹ differentiable" direction.
- 5.C.2: convexity of z(w,q); D²c NSD; concave f ⟹ c convex in q.
- 6.C: risk/probability premium, DARA (6.C.3), relative risk aversion, portfolio and insurance (6.C.4).
- 6.D: FOSD ⟹ higher mean (easy); SOSD converses (integrated-CDF ⟹ SOSD; SOSD ⟹ MPS).
- General (non-finitely-supported) distributions.
- Bridge lemma to `Econ.RankDependent.Lottery n` (Behavioral thread) — requested by that thread.
