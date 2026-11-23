# Independent statement review of the whole library (2026-11-23)

Step 1 of the verification protocol, run a second time by reviewers independent
of the threads that wrote the files. Six fresh, context-isolated agents each
saw only the statement files (proofs and comments stripped by
`verify/strip_proofs.py`) and the canonical references. Full reports, one per
area, are in `Audit/independent/review-{A..F}.md`:
A GE + foundations, B uncertainty + producer, C aggregation + rational
inattention + ambiguity, D dynamic programming + growth, E econometrics +
finance, F behavioral, bounded rationality, labor, OLG, Solow, Hulten,
misallocation, Diamond–Dybvig.

**Result: no false theorem was found anywhere.** The problems are hypotheses
that standard objects cannot meet, conclusions weaker than the textbook's,
hard steps taken as hypotheses, and missing headline results.

## Confirmed in Lean (`EconLean/Audit/IndependentFindings.lean`, sorry-free)
- **I1 (vacuous-risk, GE/Existence):** `exists_freeDisposalEquilibrium(_two_goods)`
  assume a demand selection on the closed simplex; strongly monotone consumers
  have no demand at corner prices, so the library's own `linEconomy` cannot use
  it. Needs the MWG 17.C.1 boundary-condition version (prices in the interior).
- **I2 (vacuous-risk, Bridges/Aggregation/LawOfDemand):** the library's own
  `zCD` violates `LawOfDemand` on positive prices; the law of demand only makes
  sense on normalised prices (simplex), as in MWG 17.F.
- **I3 (weak, Ramsey):** every RCK policy fixes k = 0, so
  `optimal_capital_converges` ("converges to some fixed point") does not say
  capital converges to the modified-golden-rule k* > 0.
- **I4 (weak, MarkovChain):** `doeblin` needs every one-step probability ≥ ε;
  an ergodic chain with a zero entry is excluded (SLP 11.4 uses N steps).
- **I5 (definition, HosiosDiscounted):** `Feasible` allows vacancy-filling
  probability 5/2 (and reviewer F shows an `IsSearchEqm` with job-finding
  probability ≈ 9.9); probabilities need to be capped at 1.
- Earlier: `ConvexPref` and `StrictlyQuasiconcave` stronger than MWG
  (`ConsumerFindings.lean` F3, F7); reviewer A notes this also limits the
  second welfare theorems, which use `ConvexPref`.

## Reviewer findings not yet machine-checked (by owner)
- **GE:** `gale_nikaido_debreu` takes Brouwer as a hypothesis (proved only for
  n = 2), and is for functions, not correspondences; the Leontief existence
  example is degenerate; exact-equality feasibility vs free disposal is mixed.
- **Producer/uncertainty:** Rothschild–Stiglitz only half stated; Hotelling and
  Shephard (cost) assume differentiability; risk-aversion / Pratt theorems on
  all of ℝ with u′ > 0 everywhere exclude log, √, CRRA.
- **Aggregation/RI:** Gorman indirect-utility form (MWG 4.B.1) not stated;
  softmax corollary assumes uniform marginals (Matějka–McKay derive it);
  existence of an optimal RI rule missing; Gilboa–Schmeidler representation not
  stated; GS tâtonnement stability (17.H.9) missing.
- **DP/growth:** `IsOptimalValue` requires attainment (fails with sup not
  attained); stochastic DP covers only SLP 9.6; Romer equilibrium growth is
  defined, not derived; Lucas is a stylized no-capital model.
- **Econometrics:** sharp RD has no probability (data identify E[Y|X] only
  a.e.); Goodman-Bacon decomposition missing; IPW/adjustment only for discrete
  covariates; Gauss–Markov missing; LATE's relevance hypothesis is redundant
  because x/0 = 0; `att_eq_ate` lacks integrability.
- **Behavioral/bounded rationality:** general QRE and Berk–Nash existence not
  stated; `exists_ppe` assumes a personal equilibrium exists; Hulten and
  Hsieh–Klenow only in special/qualitative forms; Gul–Pesendorfer one direction.

Note: these reviews ran on the tree as of 06:57 UTC.

## Follow-up review, 2026-11-23 10:45 UTC (new and changed files)
Reports: `Audit/independent/review-G.md` (fixed points, general existence),
`review-H.md` (updated DP, Ramsey, stationary distributions, savings).
- **Brouwer, KKM, Sperner, Kakutani: faithful.** `brouwer_fixedPoint` needs no
  Brouwer hypothesis and covers any nonempty compact convex set in a
  finite-dimensional real normed space. Sperner is for iterated barycentric
  subdivisions only (documented deviation).
- **Ramsey fixed:** `RCKModel.global_convergence` proves convergence to the
  unique k* > 0 with β f′(k*) = 1 from every k₀ > 0 (supersedes I3).
- **Still open, I1:** `exists_freeDisposalEquilibrium'` (GE/ExistenceGeneral)
  removes the Brouwer hypothesis but keeps the demand selection on the closed
  simplex, so strongly monotone, Cobb–Douglas, CES and linear economies still
  cannot use it. MWG 17.C.1 (interior prices + boundary condition) is needed.
- **Still open, I4:** `doeblin` unchanged.
- **New:** `exists_stationary` (StationaryDist, StochSavings) asserts only that
  some invariant measure exists; with f(0) = 0, the point mass at zero capital
  is invariant, so the Brock–Mirman example satisfies it trivially. Uniqueness
  and convergence (SLP 12.12) are missing. StochSavings caps assets at an
  arbitrary k̄ and has no interest rate, wage or equilibrium (not yet
  Aiyagari / LS ch. 18). `policy_of_optimal` covers date 0 only (SLP 9.5 is
  every date). `value_concave` gives weak, not strict, concavity (SLP 9.8).

## Follow-up, 2026-11-23 11:20 UTC: interior existence (MWG 17.C.1)
Report: `Audit/independent/review-interior.md`.
`exists_equilibrium_of_boundaryCondition` (GE/ExistenceInterior) is a faithful
statement of the first sentence of MWG 17.C.1, slightly more general because
homogeneity is not needed; the boundary condition and lower bound match
17.B.2(iv)–(v); a Cobb–Douglas exchange economy meets every hypothesis. This
closes the abstract part of I1. Still open: MWG 17.B.2 (an economy with
continuous, strictly convex, strongly monotone preferences and Σω ≫ 0 has an
excess demand satisfying (i)–(v)) and the economy-level corollary.
Machine checks on the 10:55 UTC tree: 1,064 theorems, all six kernels accept.

## Check-in 2 (15:55 UTC): 75 new or changed files

Six isolated reviewers (J–O) got stripped statements only. Reports are in
`Audit/independent/review-{J..O}.md`, with uncompiled sanity tests in
`sanity-{J..O}.lean.txt`. No reviewer found a false theorem. Every finding
below is a mismatch, a hypothesis that fails for textbook examples, or a
missing canonical result.

Mismatches (statement says something different from the textbook):
- Macro/Climate SocialCostCarbon `scc_eq` (N1): no capital channel, so the SCC
  is γ(1−s)Y₀·kernel, not GHKT's γY₀·kernel (30% low at s = 0.3).
- Econometrics SVARRestrictions (M4): there is no order or rank condition
  (n(n−1)/2 count, RWZ 2010 Thm 1), although the plan lists it.

Hypotheses that exclude textbook examples (the same pattern as Σ√xᵢ):
- Finance SequentialMarkets `IsAD`/`IsRadner` (M1): no x ≥ 0 consumption set,
  so log or CRRA economies have no equilibrium at all (log|x| junk value). The
  equivalence theorem is then vacuous for them. Fix: add x ≥ 0 on both sides.
- Information MoralHazard `fullInsurance_optimal`, `implementsHigh_cost_gt`
  (K2): φ = u⁻¹ is convex/monotone on all of ℝ, which excludes CARA and √w.
- Matching Assortative `HasIncreasingDifferences` (J4): supermodular on ℝ²,
  which excludes log x·log y and rpow surpluses.
- PublicGoods `voluntary_underprovision` (L3): derivative conditions on all of
  ℝ, which excludes log(1+G) and √G.
- Games Repeated `IsRepeatedSPE` (K5): every σ is an SPE at δ = 1. The theorems
  assume δ < 1, but the definition should carry it.

Weaker than canonical (WEAK):
- `median_not_defeated` (L2) counts ties for m; MWG 21.D.2 is strict vs strict.
- `gs_blocking_lemma` (J5) drops w ∈ μ′(M′).
- `myerson_satterthwaite` (J2) shares one support [a,b], and IC/IR/efficiency
  are imposed off support. It is faithful only for full common support.
- `postedPrice_optimal` (J1) assumes a threshold sign pattern instead of
  regularity, and it covers one buyer with discrete types only.
- GE `exists_walrasianEquilibrium_of_preferences` (L1): Cobb–Douglas is not
  covered (strong monotonicity, as in MWG). It also has an extra ω_a ≠ 0.
- ChamleyJudd (N2) assumes the planner's FOC. Aiyagari (N3) lacks r < 1/β−1.
- Doeblin (N4/N5) is weaker than SLP 11.4.
- Extremum `mle_*` and `z_estimator_asymptotic` (M2/M3) assume the key step.
- BLP (M5) has no contraction.
- RationalInattention `optimal_is_softmax_of_uniform` (O1) assumes uniform
  marginals. ReferenceDependence `exists_ppe` (O2) assumes PE exists; the
  reviewer gives a counterexample to dropping that hypothesis outright.
- Lemons (K6) has no gains from trade, so unraveling carries no welfare loss.

Coverage gaps: the intuitive criterion (Signaling), the OSDP and the
Fudenberg–Maskin folk theorem, the informativeness principle, Green–Laffont,
the general first-price bid, the multi-bidder Myerson auction, Blanchard–Kahn,
Rabin–Weizsäcker, the BGS salience Allais results, and the second-order
Baqaee–Farhi term.

Checked faithful, among others: revelation principle, Groves/Clarke, Myerson
IC iff, Gale–Shapley stability, optimality and strategyproofness, Falmagne,
Luce, Fehr–Schmidt, Kőszegi–Rabin, Matějka–McKay generalized logit, and
diamond_paradox (symmetric).
Machine checks on the 15:20 UTC tree (before the owners' fixes): 1,953 theorems, axioms limited to propext/Quot.sound/Classical.choice, all six kernels accept (verify/check.sh exit 0).
