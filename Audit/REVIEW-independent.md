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
