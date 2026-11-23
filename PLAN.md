# EconLean master plan: canonical, modern and behavioral economics in Lean 4, and a unified micro–macro theory

Status as of 2026-11-23. Companion to `ROADMAP.md` (which tracks the
consumer-theory stage in detail). This file is the long-range plan: scope,
library layout, the Mathlib foundations we must build, dependency order,
milestones, and how we check that what we prove is actually the economics.

Scope (revised 2026-11-23): the graduate canon (§3–4), modern and behavioral
micro (§5), modern macro including heterogeneous agents and information
frictions (§6), and a final phase that unifies micro and macro on shared
formal primitives (§7). The unifying layer is designed now (§7.1) so the
whole library is built on it rather than retrofitted.

Legend: ✅ done · 🟡 partly done · ○ not started.
Difficulty: **E** easy (days) · **M** medium (1–3 weeks) · **H** hard (a month+)
· **R** research-level (no one has formalized it; may need new math infrastructure).
Estimates assume one learner working with Claude, part time.


> **Coding conventions** (Lean module system file header, no `sorry`,
> warning-free build) are in [`CONVENTIONS.md`](CONVENTIONS.md). Every new file
> must follow them.

---

## 0. Guiding principles

1. **Correct statements matter more than proofs.** Lean's kernel guarantees a
   proof proves *its statement*. It cannot tell us the statement is the theorem
   in MWG. Every milestone therefore ends with the adversarial audit in §8
   before it counts as done.
2. **Foundations first, economics second.** Most of the hard work in grad
   theory is generic math (fixed points, correspondences, convex duality,
   dynamic programming, Markov processes). We build those once, in
   `EconLean/Foundations/`, written to Mathlib style so they could be
   upstreamed.
3. **Two tracks in parallel.** Micro needs static optimization and fixed
   points; macro needs dynamic programming and stochastic processes. After a
   shared foundation (M1), the tracks are independent and can be worked in
   separate threads.
4. **Reuse, don't redo.** Game theory, social choice and mechanism design are
   partly done in EconCSLib; Brouwer/Nash in Lyu–Li. We depend on or port from
   them (license permitting) instead of re-proving.
6. **One set of primitives for everything.** Agents, choice rules, beliefs,
   aggregation and equilibrium are defined once in `EconLean/Core/` (§7.1).
   Rational and behavioral agents differ only in their `ChoiceRule` and
   `BeliefRule`; micro and macro differ only in the population and the time
   structure. New models should be stated as instances of `Core` wherever
   possible, so the bridges in §7.2 can be proved later without rewrites.
5. **Statements are frozen and reviewed.** Each headline theorem has a
   reviewed reference statement, cited to the textbook, that CI checks the
   proof against (§8.3). Proofs can change freely; statements only with review.

---

## 1. Library layout

```
EconLean/
  Core/                 unifying primitives: Population, DecisionProblem, ChoiceRule,
                        BeliefRule, Aggregator, Equilibrium, Welfare (§7.1)
  Bridges/              aggregation and limit theorems linking micro and macro (§7.2)
  Foundations/          generic math, Mathlib-style, upstreamable
    Correspondence.lean     set-valued maps, upper/lower hemicontinuity, closed graph
    Maximum.lean            Berge's maximum theorem
    FixedPoint/             Brouwer (port), Kakutani, Tarski/Topkis, Schauder (stretch)
    Optimization/           KKT, envelope theorems, concave programming, Lagrangian duality
    ConvexDuality.lean      support functions, conjugates, Minkowski, Farkas variants
    Lattice.lean            supermodularity, increasing differences, Topkis, Milgrom–Shannon
    DynamicProgramming/     Bellman operators, Blackwell, principle of optimality
    Markov/                 finite chains, Feller kernels, invariant distributions
    StochasticOrders.lean   FOSD, SOSD, mean-preserving spreads
    DifferenceEq.lean       linear systems, stability, saddle paths, Blanchard–Kahn
  Preferences/          ✅ (Ch. 1)
  Consumer/             🟡 (Ch. 2–4), owned by the consumer-theory thread
  Producer/             Ch. 5
  Uncertainty/          Ch. 6, plus stochastic dominance and Anscombe–Aumann
  PartialEq/            Ch. 10–12: competitive markets, externalities, oligopoly
  GE/                   Ch. 15–20: exchange, production, welfare, core, existence
  Games/                Ch. 7–9 plus repeated, supermodular, Bayesian games
  Information/          Ch. 13–14: adverse selection, signaling, screening, moral hazard
  Mechanism/            Ch. 21–23: social choice, bargaining, mechanism design, auctions, matching
  Behavioral/           prospect theory, reference dependence, present bias, ambiguity,
                        stochastic choice, rational inattention, bounded-rationality games
  Networks/  MarketDesign/  IO/   modern micro (§5)
  Macro/
    Growth/             Solow, Ramsey–Cass–Koopmans, endogenous growth
    OLG/
    AssetPricing/
    Consumption/        PIH, precautionary saving, incomplete markets
    Search/
    RBC/
    Policy/             fiscal, monetary, time consistency, recursive contracts
    Heterogeneous/      Bewley–Aiyagari, HANK cores, sequence space, mean-field games
    InfoFrictions/  Behavioral/  Production/  Finance/  Trade/   modern macro (§6)
  Examples/             concrete economies (Cobb–Douglas, CES, Brock–Mirman ...)
  Audit/                non-vacuity witnesses, counterexamples, frozen statements
```

Modelling conventions to fix up front (decide once, record in `CONVENTIONS.md`):
- Commodity space: `ι → ℝ` with `[Fintype ι]` for static micro (current choice).
  Infinite-horizon macro uses sequences `ℕ → ℝ` and, for welfare theorems, the
  Banach space `lp (fun _ => ℝ) ∞` (Mathlib has `lp`).
- Preferences: keep the current `R : X → X → Prop` + `Rational R` structure;
  add a bridge to Mathlib's `Preorder`/`TotalPreorder`-style classes and to
  EconCSLib's encoding so we can import their results.
- Uncertainty: `PMF` for finite lotteries; `MeasureTheory.ProbabilityMeasure`
  and `ProbabilityTheory.Kernel` for general ones and for Markov processes.
- Optimizers are **sets** (argmax correspondences), never `Classical.choose`
  picks, so statements don't silently depend on an arbitrary selection.
- Values defined by `sSup`/`sInf` must always be paired with an attainment or
  boundedness lemma (see the junk-value warning in §8.2).

---

## 2. Mathlib: what we can use, and the gaps we must fill

### Available in Mathlib (as of v4.36; re-verify when bumping)
| Need | Mathlib |
|---|---|
| Order theory, preorders, complete lattices, Knaster–Tarski | `OrderHom.lfp`, `CompleteLattice` |
| Real analysis, extreme value theorem, compactness | `IsCompact.exists_isMaxOn` |
| Convexity, `ConvexOn`/`ConcaveOn`, Jensen | `ConvexOn.map_sum_le`, `ConvexOn.map_integral_le` |
| Separating hyperplanes (Hahn–Banach) | `geometric_hahn_banach_*` |
| Farkas-type lemma, cones, dual cones | `ProperCone`, `PointedCone` |
| Fréchet derivatives, mean value thm, implicit function thm | `HasFDerivAt`, `HasStrictFDerivAt.implicitFunction` |
| Lagrange multipliers (equality constraints only) | `IsLocalExtrOn.exists_linear_combination_of_hasStrictFDerivAt` |
| Banach fixed point (contraction mapping) | `ContractingWith.efixedPoint` |
| Bounded continuous functions as a complete metric space | `BoundedContinuousFunction` |
| Measure theory, integration, conditional expectation | `MeasureTheory.*`, `condExp` |
| Markov kernels, composition, Ionescu-Tulcea | `ProbabilityTheory.Kernel`, `Kernel.traj` |
| Discrete-time martingales, stopping times, optional stopping | `MeasureTheory.Martingale`, `Submartingale` |
| Weak convergence of probability measures | `ProbabilityMeasure` topology |
| Matrices, eigenvalues of Hermitian matrices, `PosSemidef` | `Matrix.PosSemidef`, `Matrix.IsHermitian.eigenvalues` |
| ODE existence (Picard–Lindelöf), Grönwall | `IsPicardLindelof`, `norm_le_gronwallBound_of_norm_deriv_right_le` |
| Hall's marriage theorem | `Finset.all_card_le_biUnion_card_iff_exists_injective` |
| `lp` spaces, ℓ^∞ | `lp`, `MeasureTheory.Lp` |

### Gaps we must build (the "Foundations" backlog), in priority order
| # | Gap | Used by | Diff. | Notes |
|---|---|---|---|---|
| F1 | Correspondences: UHC/LHC, closed graph, compact-valued | Berge, Kakutani, GE, DP | M | Mathlib has nothing on hemicontinuity. |
| F2 | Berge's maximum theorem | demand continuity, DP, GE | M | Unlocks continuity of v, x(p,w), value functions. |
| F3 | Brouwer fixed point | GE existence, Nash | H | Check Mathlib first; else port Lyu–Li (simplex version) and extend to compact convex sets in ℝⁿ via retraction. |
| F4 | Kakutani fixed point | Nash, GE with correspondences | M | From Brouwer by approximate selection (Cellina) or via simplicial approx. |
| F5 | KKT conditions (inequality constraints, Slater/LICQ) | producer, GE, contracts, Ramsey taxation | M | Extends Mathlib's equality-constraint Lagrange. |
| F6 | Envelope theorems (Milgrom–Segal general version) | Hotelling, Roy, Benveniste–Scheinkman, mechanism design | M | Current Shephard/Roy are ad hoc; generalize once. |
| F7 | Monotone comparative statics: Topkis, Milgrom–Shannon, single crossing | supermodular games, screening, search, DP | M | Pure order theory; good learning exercise. |
| F8 | Dynamic programming: Bellman operator on bounded functions, Blackwell's sufficient conditions, principle of optimality, policy functions | all of macro | M | Contraction mapping already in Mathlib; this is the highest-leverage macro foundation. |
| F9 | Value-function properties: monotone, concave, differentiable (Benveniste–Scheinkman); Euler eq + transversality sufficiency | growth, consumption | M | |
| F10 | Stochastic DP with Markov kernels; Feller property | stochastic growth, search, Aiyagari | H | Measurability of policies is the hard part. |
| F11 | Finite Markov chains: stationary distributions, ergodic theorem for irreducible aperiodic chains | search, Huggett, Markov perfect eq | M | Perron–Frobenius may be needed; check Mathlib. |
| F12 | General invariant distributions (Stokey–Lucas ch. 11–12: monotone mixing, Hopenhayn–Prescott) | Aiyagari, Hopenhayn, firm dynamics | H | |
| F13 | Stochastic orders: FOSD, SOSD, Rothschild–Stiglitz equivalences | uncertainty, insurance, info design | M | |
| F14 | Linear difference systems: stability via spectral radius, saddle-path (Blanchard–Kahn) | Ramsey, NK model | M | |
| F15 | Minimax theorem (von Neumann/Sion) | zero-sum games, LP duality | M | Possibly via Hahn–Banach. |
| F16 | Concavification / convex hull of graphs | Bayesian persuasion | E–M | |
| F17 | Sard's theorem / regular values | regular economies, generic finiteness | R | Skip unless upstream Mathlib gets it. |
| F18 | Continuous-time optimal control (Pontryagin, HJB, viscosity solutions); Itô calculus | continuous-time growth, Merton, HACT, Brunnermeier–Sannikov | R | Out of scope; discrete-time versions only. |
| F19 | Capacities and the Choquet integral | rank-dependent utility, CPT, maxmin EU | M | Not in Mathlib (guess; verify). |
| F20 | Shannon entropy and mutual information for finite and general distributions | rational inattention, logit | M | Mathlib has `negMulLog` and KL divergence pieces; mutual information as needed here is likely missing (guess). |
| F21 | Optimal transport, Kantorovich duality | matching markets, assortative matching | H | Finite case reduces to LP duality (M). |
| F22 | Lyapunov convexity theorem; Aumann integral of correspondences | continuum economies, core equivalence, nonatomic games, B2 | H | Key for every continuum-of-agents result. |
| F23 | Implicit function theorem on sequence spaces (ℓ^∞) applied to equilibrium maps | sequence-space HANK, B4 | M | Mathlib's IFT is on Banach spaces, so this is mostly application (guess). |
| F24 | Propagation of chaos / finite-to-mean-field limits | MFG, B2 | R | Active research even on paper. |

---

## 3. Microeconomics (MWG order, plus standard grad extensions)

### Part I: Individual decision making
**Ch. 1–4 Consumer** (consumer thread owns this; listed for dependency planning)
- ✅ Preferences, utility, budget, demand, Walras' law, duality, WARP, Shephard, Roy, Slutsky.
- ○ Berge ⇒ continuity of v and x(p,w) **[needs F2]** (M)
- ○ Slutsky matrix symmetric, NSD, rank n−1 (M)
- ○ Debreu representation theorem; lexicographic counterexample (H / M)
- ○ GARP, Afriat's theorem (M; finite combinatorics + LP)
- ○ Integrability: recovering preferences from demand (H)
- ○ Ch. 4 aggregation: Gorman polar form, representative consumer, wealth effects (M)

**Ch. 5 Producer** (M overall)
- Production sets and properties (free disposal, CRS, convexity, additivity).
- Profit max, supply correspondence; homogeneity; Hotelling's lemma **[F6]**.
- Cost minimization, conditional factor demand, Shephard's lemma for cost.
- Law of supply; Le Chatelier principle; aggregation (profit of sum = sum of profits; easy and elegant).
- Efficient production ⟺ profit maximizing (small welfare theorem; needs separation).

**Ch. 6 Choice under uncertainty**
- Lotteries, compound lotteries, independence axiom (E).
- vN–M expected utility theorem, finite outcomes (M). Audit the existing Lean attempt by J. Li first.
- Risk aversion ⟺ concave u; Arrow–Pratt; certainty equivalents; Pratt's theorem (M).
- FOSD/SOSD characterizations **[F13]** (M).
- Anscombe–Aumann subjective EU (H). Savage (R, stretch).
- Portfolio problem, demand for insurance, Mossin's theorem (E–M).

### Part II: Game theory
Start by importing EconCSLib's strategic games / Nash and Lyu–Li's mixed Nash.
- Ch. 7–8: dominance, iterated deletion, rationalizability = ISD in 2-player games (M), mixed Nash existence **[F3/F4]**, correlated equilibrium (LP), zero-sum minimax **[F15]**, Bayesian games and Bayes–Nash existence (finite).
- Ch. 9: extensive-form games as trees, Kuhn's theorem (behavioural vs mixed, perfect recall) (H), Zermelo/backward induction (M), SPE, one-shot deviation principle (M), sequential equilibrium and PBE (M–H).
- Repeated games: one-shot deviation for discounted games, Nash folk theorem, Fudenberg–Maskin folk theorem (H), APS self-generation (shares F8 machinery).
- Supermodular games: extremal equilibria exist and are monotone **[F7 + Tarski]** (M).
- Knowledge: Aumann agreement theorem, common knowledge as meet of partitions (E–M).

### Part III: Market equilibrium and failure
- Ch. 10 partial equilibrium: competitive eq, surplus, deadweight loss, welfare theorems in quasilinear economies (E).
- Ch. 11 externalities and public goods: Samuelson condition, Lindahl, Coase theorem in quasilinear setting, free-riding (E–M).
- Ch. 12 market power: monopoly, Cournot existence/uniqueness, Bertrand paradox, Stackelberg, Cournot → competitive limit (M).
- Ch. 13 adverse selection: Akerlof unravelling, Rothschild–Stiglitz nonexistence of pooling eq, Spence signaling, intuitive criterion (M).
- Ch. 14 moral hazard: principal–agent with finite outcomes, first-order approach validity conditions, Holmström informativeness principle (M–H).

### Part IV: General equilibrium
- Exchange economies, Edgeworth box, Walrasian eq, Pareto optimality (E).
- First Welfare Theorem (E). Second Welfare Theorem via Hahn–Banach (M).
- Core; equilibria are in the core (E); Debreu–Scarf core convergence (H).
- Existence: excess demand properties (homogeneity, Walras, boundary) ⇒ equilibrium via Brouwer/Kakutani **[F3/F4]** (H). This is the flagship micro milestone.
- Uniqueness and stability under gross substitutes; tâtonnement (M–H).
- Production economies; Arrow–Debreu with time and uncertainty; Radner sequential equilibrium; incomplete markets (M–H).
- Sonnenschein–Mantel–Debreu (R, stretch). Regular economies / generic finiteness **[F17]** (R, skip).

### Part V: Welfare, incentives, mechanisms
- Ch. 21 social choice: import Arrow and Gibbard–Satterthwaite from EconCSLib; add May's theorem, Sen's liberal paradox, median voter theorem (E–M).
- Ch. 22 bargaining and cooperative games: Nash bargaining characterization (M), Kalai–Smorodinsky, Shapley value uniqueness (M), Bondareva–Shapley (LP duality) (M).
- Ch. 23 mechanism design: revelation principle (E), VCG/Groves strategy-proofness (import), Green–Laffont uniqueness of Groves (H), Myerson lemma and optimal auction (import/extend), revenue equivalence (M **[F6]**), Myerson–Satterthwaite (M–H), Maskin monotonicity (M).
- Beyond MWG: auctions (Krishna ch. 2–4: first/second price symmetric IPV equilibria), matching (Gale–Shapley stability, lattice of stable matchings, strategy-proofness for proposers), Bayesian persuasion (concavification **[F16]**), Blackwell's comparison of experiments (H), screening with single crossing **[F7]**.

---

## 4. Macroeconomics (Stokey–Lucas, Ljungqvist–Sargent, Acemoglu)

Everything is discrete time. Continuous-time results are out of scope until
Mathlib has the control theory (F18).

### Foundations (Stokey–Lucas ch. 3–4, 9, 11–12)
- Contraction mapping ✓ in Mathlib; Blackwell's sufficient conditions **[F8]** (E–M).
- Deterministic DP: sequence problem ⟺ Bellman equation (SL Thms 4.2–4.5), existence/uniqueness of V in bounded continuous functions, policy correspondence UHC via Berge **[F2]** (M).
- Monotonicity, concavity, differentiability of V (Benveniste–Scheinkman), uniqueness of policy (M **[F9]**).
- Euler equation + transversality sufficient for optimum (SL 4.15) (M).
- Unbounded returns (Alvarez–Stokey / weighted norms) (H).
- Stochastic DP with Markov kernels; measurable selection of policies (H **[F10]**).
- Markov chains: finite case invariant distributions and convergence (M **[F11]**); general state spaces, Feller, weak convergence, monotone mixing (H **[F12]**).
- Linear difference equations: stability and saddle paths (M **[F14]**).

### Growth (Acemoglu ch. 2–8, 11–13)
- Solow model: existence, uniqueness, global stability of steady state (E). Good first macro milestone.
- Ramsey–Cass–Koopmans: optimal growth via DP; monotone convergence of capital; steady state ⟺ modified golden rule (M).
- Planner = competitive equilibrium in the neoclassical growth model (M–H; needs infinite-horizon welfare theorem, see below).
- Brock–Mirman closed form (log utility, full depreciation): explicit V and policy as a concrete witness for the DP machinery (E–M).
- Stochastic growth: existence and uniqueness of invariant distribution of capital (H **[F12]**).
- AK, Romer (expanding varieties), Lucas human capital: balanced growth paths and growth-rate formulas (M).

### Overlapping generations (LS ch. 9, Acemoglu ch. 9)
- Diamond OLG: existence of steady state, dynamic inefficiency when r < g (M).
- Samuelson pure-exchange OLG: failure of First Welfare Theorem; money as Pareto improvement (M). A nice formal counterpoint to GE Part IV.
- Cass criterion / Balasko–Shell (R, stretch).

### Infinite-horizon equilibrium and asset pricing (LS ch. 8, 13)
- Arrow–Debreu vs sequential markets equivalence with natural debt limits (M).
- Infinite-dimensional First Welfare Theorem in ℓ^∞ (M); Second (Debreu 1954 / Bewley) (H).
- Fundamental theorem of asset pricing, finite states: no arbitrage ⟺ positive SDF (M; Farkas).
- Lucas tree pricing as a fixed point (M **[F8]**); Hansen–Jagannathan bound (E; Cauchy–Schwarz).
- Modigliani–Miller (E).

### Consumption and savings (LS ch. 16–18)
- Permanent income hypothesis with quadratic utility; martingale consumption (Hall) (M).
- Precautionary saving under prudence (u''' > 0) (M).
- Income fluctuation problem: bounded assets, existence of stationary distribution (H **[F10/F12]**).
- Huggett / Aiyagari existence of stationary recursive equilibrium (R; flagship stretch).

### Search and labor (LS ch. 6, 28)
- McCall: reservation wage property, comparative statics in mean-preserving spreads (M **[F7/F13]**). Good early macro milestone; small and complete.
- Steady-state unemployment, DMP with Nash bargaining, Hosios condition (M).
- Burdett–Mortensen wage dispersion (H).

### Business cycles and policy (LS ch. 11, 19–24; Galí)
- RBC as stochastic growth with labor; planner = CE (M–H).
- Linear rational expectations: Blanchard–Kahn determinacy (M **[F14]**).
- New Keynesian 3-equation model: Taylor principle ⟺ determinacy (M).
- Ricardian equivalence (E); Barro tax smoothing (M); Friedman rule optimality in cash-in-advance (M).
- Ramsey optimal taxation; Chamley–Judd zero capital tax. Formalize **with precise hypotheses**: Straub–Werning (2020) showed the classic statement is wrong in standard cases, which makes this a showcase for what formalization catches (H).
- Time inconsistency (Kydland–Prescott) (E–M); recursive contracts and APS/Abreu–Pearce–Stacchetti credible policy sets (H).
- Dynamic contracts: Thomas–Worrall, Spear–Srivastava promised-utility recursion (H).

---

## 5. Modern and behavioral microeconomics (beyond the textbook canon)

These build on Parts I–V. Each item names the paper whose statement is the
reference for the adversarial check, because behavioral models come in many
variants and "prospect theory" alone is not a precise statement.

### 5.1 Behavioral decision theory
- **Rank-dependent utility and cumulative prospect theory** (Quiggin 1982; Tversky–Kahneman 1992): Choquet-integral representation, probability weighting, loss aversion; CPT respects FOSD while original prospect theory does not (M; needs the Choquet integral **[F19]**).
- **Reference dependence**: Kőszegi–Rabin (2006) personal and preferred personal equilibrium, existence for finite choice sets (M); endowment effect and WTA/WTP gap as theorems (E).
- **Present bias**: quasi-hyperbolic β–δ (Laibson 1997; O'Donoghue–Rabin 1999). Strotz consistent planning as subgame-perfect equilibrium of the intrapersonal game; sophisticated vs naive procrastination results (M). Existence can fail with continuous choice (Harris–Laibson); state that carefully.
- **Temptation and self-control**: Gul–Pesendorfer (2001) representation of preferences over menus (H).
- **Ambiguity**: maxmin EU (Gilboa–Schmeidler 1989) representation theorem (H); variational preferences (Maccheroni–Marinacci–Rustichini 2006) (H); smooth ambiguity (KMM 2005) (M); multiplier preferences / robustness (Hansen–Sargent), which links straight to macro (M).
- **Recursive utility**: Epstein–Zin / Kreps–Porteus, existence and uniqueness of the utility fixed point (Marinacci–Montrucchio 2010) (M–H; uses F8).
- **Stochastic choice**: Luce's choice axiom ⟺ logit (E–M); random utility characterizations (Block–Marschak finite case, McFadden–Richter) (H); logit as entropy-regularized choice (E).
- **Rational inattention**: Sims; Matějka–McKay (2015) RI ⟺ generalized multinomial logit (M; needs mutual information **[F20]**); Caplin–Dean posterior-separable costs (M).
- **Limited attention and salience**: consideration sets (Masatlioglu–Nakajima–Ozbay 2012) revealed-attention characterization (M); salience theory (Bordalo–Gennaioli–Shleifer 2012) (M).
- **Belief distortions**: diagnostic expectations (BGS 2018), overconfidence, motivated beliefs (E–M; mostly definitions + comparative statics).
- **Social preferences**: Fehr–Schmidt inequity aversion and ultimatum game predictions; Charness–Rabin (E).

### 5.2 Bounded rationality in games and learning
- **Level-k and cognitive hierarchy** (Nagel; Camerer–Ho–Chong 2004) (E–M).
- **Quantal response equilibrium** (McKelvey–Palfrey 1995): existence via Brouwer, logit QRE → Nash as noise → 0 (M).
- **Cursed equilibrium** (Eyster–Rabin 2005), **analogy-based expectation equilibrium** (Jehiel 2005) (M).
- **Misspecified learning**: Berk–Nash equilibrium (Esponda–Pouzo 2016) existence (H); self-confirming equilibrium (Fudenberg–Levine 1993) (M).
- **Learning dynamics**: fictitious play converges in zero-sum games (Robinson 1951) (H); no-regret play converges to coarse correlated equilibria (Hart–Mas-Colell 2000) (M); Bayesian learning and merging of opinions (Blackwell–Dubins, via martingale convergence, which Mathlib has) (M–H).
- **Evolutionary games**: replicator dynamics, ESS ⇒ asymptotically stable (Taylor–Jonker) (M; Mathlib ODEs); stochastic stability (Kandori–Mailath–Rob, Young) (H).

### 5.3 Modern information economics
- Cheap talk: Crawford–Sobel partition equilibria (M–H).
- Information design: Bayes correlated equilibrium (Bergemann–Morris 2016) (M); persuasion already in Part V.
- Global games: Carlsson–van Damme / Morris–Shin uniqueness via iterated dominance (M–H). Bridge to macro crises (§7.2).
- Social learning and herding: Bikhchandani–Hirshleifer–Welch cascades (E–M); Smith–Sørensen (H).
- Reputation: Fudenberg–Levine (1989) payoff bound (H).
- Dynamic and robust mechanism design: Pavan–Segal–Toikka envelope formula (H); Bergemann–Morris robust implementation (H).

### 5.4 Networks
- Network games with linear best replies: Nash equilibrium ∝ Bonacich centrality (Ballester–Calvó-Armengol–Zenou 2006) (E–M; linear algebra).
- DeGroot learning: consensus ⟺ strongly connected and aperiodic; influence = stationary distribution (M; shares F11).
- Network formation: pairwise stability, efficiency vs stability (Jackson–Wolinsky 1996) (M).
- Contagion and cascades (Acemoglu–Ozdaglar–Tahbaz-Salehi 2015) (H).
- Production networks: see Hulten and Baqaee–Farhi in §6; they are bridges, not just micro.

### 5.5 Market design and matching
- Matching with contracts (Hatfield–Milgrom 2005) via Tarski (M).
- Top trading cycles: core uniqueness and strategy-proofness (Shapley–Scarf; Roth–Postlewaite; Roth 1982) (M).
- School choice: deferred acceptance vs Boston mechanism (Abdulkadiroğlu–Sönmez 2003) (M).
- Assignment game: core = LP dual solutions (Shapley–Shubik 1971) (M).
- Matching as optimal transport; positive assortative matching from supermodularity (Becker; Galichon) (M–H; Kantorovich duality **[F21]**).

### 5.6 Modern IO and contracts
- Discrete-choice demand: logit/nested logit, Berry (1994) inversion as a contraction (M; Mathlib contraction mapping).
- Diamond (1971) search paradox; consumer search (M).
- Two-sided markets (Rochet–Tirole; Armstrong) (M).
- Relational contracts (Levin 2003) stationarity result (M–H); incomplete contracts (Grossman–Hart–Moore) (M).

---

## 6. Modern macroeconomics (beyond the textbook canon)

### 6.1 Heterogeneous agents
- **Bewley–Huggett–Aiyagari**: existence of stationary equilibrium (Açıkgöz 2018 gives a careful proof; uniqueness can fail) (R; flagship). Needs F10, F12.
- **Krusell–Smith approximate aggregation**: a numerical finding, not a theorem. Formalize the definitions and the exact-aggregation special cases only. (Guess at what is provable.)
- **HANK**: Kaplan–Moll–Violante is quantitative; formalize the analytical cores: two-agent THANK (Bilbiie 2008/2020), Werning (2015) "as-if" conditions under which incomplete markets give the RANK Euler equation, intertemporal MPCs and the intertemporal Keynesian cross (Auclert–Rognlie–Straub 2024) (M–H).
- **Sequence-space approach** (Auclert–Bardóczy–Rognlie–Straub 2021): equilibrium as H(U, Z) = 0 on sequences, linearized impulse responses via the implicit function theorem in sequence space (M–H; Mathlib IFT on Banach spaces, ℓ^∞). This is a central bridge (§7.2).
- **Mean-field games**: discrete-time, finite-state MFG existence (H); Lasry–Lions monotonicity ⇒ uniqueness (M in discrete time); continuum-of-agents competitive equilibrium as MFG. Continuous-time HJB–Kolmogorov systems remain out of scope (F18).

### 6.2 Information frictions
- Lucas (1972) islands: monetary non-neutrality from signal extraction (M).
- Sticky information (Mankiw–Reis 2002) and noisy information (Woodford 2003) Phillips curves (M).
- Rational inattention in macro (Maćkowiak–Wiederholt 2009) (M; F20).
- Beauty contests and the social value of public information (Morris–Shin 2002) (M).
- Higher-order beliefs dampen GE effects; forward-guidance puzzle and its resolution by incomplete information (Angeletos–Lian 2018) (H).

### 6.3 Behavioral macro
- Behavioral New Keynesian model with cognitive discounting (Gabaix 2020): determinacy without the Taylor principle, no forward-guidance puzzle (M).
- Level-k in GE (García-Schmidt–Woodford 2019; Farhi–Werning 2019) (M–H).
- Diagnostic expectations and credit cycles (Bordalo–Gennaioli–Shleifer 2018) (M).
- Present-biased consumers and hand-to-mouth behavior (Laibson et al.) (M).
- Robust control in macro (Hansen–Sargent) (M; reuses 5.1).

### 6.4 Production, firms, misallocation, trade
- Hulten's theorem: aggregate TFP response = Domar-weighted sum (E–M). Baqaee–Farhi (2019) second-order terms (H). Key micro→macro bridge.
- Granular hypothesis (Gabaix 2011): idiosyncratic shocks don't wash out under fat tails (M–H; probability).
- Misallocation and aggregate TFP (Hsieh–Klenow 2009) formula (E–M).
- Hopenhayn (1992) firm dynamics stationary equilibrium (H; F12).
- Trade: Eaton–Kortum (Fréchet algebra) (M); Melitz (2003) selection (M); Arkolakis–Costinot–Rodríguez-Clare (2012) gains-from-trade formula (M).
- Quantitative spatial: existence/uniqueness (Allen–Arkolakis 2014) (H).

### 6.5 Macro-finance, money, crises
- Diamond–Dybvig (1983): multiple equilibria, deposit insurance eliminates the run (E–M); global-games uniqueness (Goldstein–Pauzner 2005) (H).
- Holmström–Tirole liquidity (M); Kiyotaki–Moore (1997) collateral amplification (M); Bernanke–Gertler–Gilchrist financial accelerator (M).
- Intermediary asset pricing: He–Krishnamurthy (2013) discrete-time version (H); Brunnermeier–Sannikov is continuous-time (out of scope).
- Asset pricing with recursive utility: long-run risk, rare disasters (M).
- New monetarism: Kiyotaki–Wright (1989), Lagos–Wright (2005) (M).
- Climate: Golosov–Hassler–Krusell–Tsyvinski (2014) closed-form optimal carbon tax (E–M).

### 6.6 Modern growth and public finance
- Schumpeterian growth (Aghion–Howitt 1992), directed technical change (Acemoglu 2002) (M).
- New dynamic public finance: Mirrlees optimal income tax (Diamond 1998 / Saez 2001 formula), inverse Euler equation (Golosov–Kocherlakota–Tsyvinski 2003) (M–H). This is the mechanism-design ↔ macro bridge.

---

## 7. Phase U: a unifying theory of micro and macro

**Goal.** Make every model in the library, micro or macro, rational or
behavioral, an instance of one small set of abstractions, so that macro models
are *built from* micro primitives and the passage between them is a theorem,
not an informal step. Then use Lean to map exactly where the bridges hold and
where they break.

**Honest framing.** Formalization cannot by itself produce a new unified
theory; what it can do, and what nobody has done, is (a) put the existing
fields in one formal language, (b) prove the known bridge theorems in that
language, (c) state precisely the bridges that are missing, and (d) extract
automatically, from the Lean dependency graph, exactly which micro assumptions
each macro result uses. Items (c) and (d) are where genuinely new results could
appear. Whether they amount to a "unified theory" is a research question; this
plan treats it as one.

### 7.1 Core abstractions (design now, used from M1 onward)
Built in `EconLean/Core/`. *Guess at the right design; to be revised after the
first three instances are built.*

1. **`Population`**: a measure space of agents. Finite economies use the
   counting measure, continuum economies (Aumann 1964) use an atomless
   probability measure, type-distribution models use a measure on types.
   Building this in from the start means going from finite micro to continuum
   macro is a change of measure, not a rewrite.
2. **`DecisionProblem`**: for each agent, a feasible set depending on the
   agent's state and on aggregate objects (prices, others' actions, laws of
   motion).
3. **`ChoiceRule`**: a correspondence from decision problems to chosen
   actions. Utility maximization is one instance; prospect theory, β–δ
   sophisticated planning, rational inattention, level-k, quantal response and
   consideration sets are others. **This is what lets behavioral and rational
   models share all equilibrium machinery.**
4. **`BeliefRule`**: how agents form expectations about aggregates. Rational
   expectations = beliefs equal the true law (a fixed point). Alternatives:
   diagnostic, level-k, cognitive discounting, Berk–Nash, self-confirming.
5. **`Aggregator`**: maps the population's profile of choices to aggregate
   objects (excess demand, aggregate capital, a distribution). Integration
   against the population measure.
6. **`Equilibrium`**: a profile where (i) each agent's action is chosen by its
   `ChoiceRule` given perceived aggregates, (ii) perceived aggregates are
   produced by its `BeliefRule`, (iii) feasibility/market clearing holds for the
   aggregate. Static, dynamic (sequence-space) and recursive (stationary-distribution) versions.
7. **`Welfare`**: Pareto and social-welfare comparisons defined on the same
   objects, including for behavioral agents (where "welfare" needs a stated
   normative criterion; Bernheim–Rangel choice-based welfare is a candidate).

**Instance theorems** (each a definitional equivalence, proved early to test
the design): Walrasian equilibrium, Nash equilibrium, Bayes–Nash, Aumann
continuum-economy equilibrium, recursive competitive equilibrium, Bewley
stationary equilibrium, mean-field equilibrium, QRE, Berk–Nash, and the
existing consumer-theory `demand` (via a bridge lemma, without editing the
consumer files).

### 7.2 The bridges: which exist, which are missing
Status column is my reading of the literature; treat it as a guess to be
checked by the adversarial reviewer.

| # | Bridge | Known results to formalize | What is missing (research target) |
|---|---|---|---|
| B1 | **Heterogeneous agents → representative agent** | Gorman aggregation; Constantinides (1982) complete-markets representative agent; Werning (2015) as-if; Hulten | A characterization of exactly which aggregate predictions are invariant to heterogeneity, beyond these special cases. SMD says without restrictions aggregates are arbitrary; the boundary between SMD and Gorman is not mapped; see B0 (§7.2a). |
| B2 | **Finite agents → continuum** | Debreu–Scarf core convergence; Cournot → competitive; Aumann's core equivalence (needs Lyapunov **[F22]**); large-game → MFG limits (Carmona–Delarue, partial) | General convergence of equilibria (not just of the core) for dynamic economies with frictions. Macro assumes continuum; micro proves things for finite n; the limit is usually assumed. |
| B3 | **Static → dynamic → recursive** | Arrow–Debreu ⟺ sequential markets; recursive competitive equilibrium as a fixed point; Kubler–Schmedders (2002) nonexistence of recursive eq with incomplete markets | Conditions under which recursive equilibria of heterogeneous-agent models exist, which modern HANK takes for granted. |
| B4 | **Partial → general equilibrium** | GE effect = PE effect + feedback, via sequence-space Jacobians; Auclert–Rognlie–Straub intertemporal Keynesian cross | A general theorem relating micro-estimated elasticities to macro effects; "micro-to-macro elasticity" debates (e.g. labor supply) lack one formal statement. |
| B5 | **Rational ↔ behavioral expectations** | Gabaix cognitive discounting; Angeletos–Lian; Farhi–Werning level-k | A parametrized family of `BeliefRule`s with RE as a limit, plus a classification of which macro results are robust (continuous in the parameter) and which are knife-edge. Lean can do this classification mechanically. |
| B6 | **Behavioral choice → aggregate behavior** | Logit/RI aggregate to smooth demand; Becker (1962) "irrational" agents still give downward-sloping market demand | When do behavioral biases cancel in aggregate and when do they amplify (e.g. through GE feedback)? Little general theory. |
| B7 | **Mechanism design ↔ macro policy** | New dynamic public finance (Mirrlees, inverse Euler); Ramsey vs Mirrlees | Unified treatment of optimal policy where both information constraints and GE feedback bind. |
| B8 | **Information: micro design ↔ macro dispersed info** | Bergemann–Morris BCE; Morris–Shin; Angeletos–Pavan efficiency | Information design applied to aggregate (macro) outcomes with GE feedback. |
| B9 | **Networks: micro shocks → macro fluctuations** | Hulten; Acemoglu et al. (2012) network origins; Gabaix granularity | Nonlinear and dynamic versions in one framework (Baqaee–Farhi covers part). |
| B10 | **Welfare across fields** | Pareto (micro), consumption-equivalent welfare (macro), Bernheim–Rangel (behavioral) | One welfare criterion consistent across all three, with theorems on when they agree. |

### 7.2a Bridge B0: which micro restrictions escape SMD (the aggregation map)

**Why this is the first bridge.** The Sonnenschein–Mantel–Debreu theorem says
that the standard consumer axioms (rational, continuous, monotone, convex
preferences; utility maximization) impose almost nothing on *aggregate* excess
demand: beyond continuity, homogeneity of degree zero, Walras' law and a
boundary condition, any function can be the excess demand of some exchange
economy (Debreu 1974: with at least as many consumers as goods, on prices
bounded away from zero). Mas-Colell (1977) extends this: any compact set of
prices can be the equilibrium set. So uniqueness, stability and comparative
statics in GE, and the representative agent in macro, all require extra
restrictions. Macro models adopt them (homothetic or CRRA preferences, Gorman
forms, complete markets) mostly without saying so.

**Design decision: don't rebuild micro, layer restrictions on top.** The
general consumer theory stays as is: it is correct and is what SMD is a
theorem *about*. Each restriction below becomes a named predicate on
preferences, demand functions or populations in `Bridges/Aggregation/`,
with two theorems each: (i) whether it is **preserved under aggregation**
(summing over agents), and (ii) which **aggregate property** it buys. Because
Lean tracks exactly which hypotheses a proof uses, the assumption atlas (§7.3)
then shows, for every GE or macro result, which of these restrictions it
silently relies on.

| Restriction (micro) | Preserved under summation? | Aggregate property it buys | Source | Diff. |
|---|---|---|---|---|
| *None* (standard axioms only) | — | **Nothing beyond continuity, homogeneity, Walras' law, boundary behavior** | SMD: Sonnenschein 1972, Mantel 1974, Debreu 1974; Mas-Colell 1977 | H–R (flagship negative result) |
| Gorman polar form, common wealth slope `b(p)` | n/a (property of the population) | Aggregate demand depends only on aggregate wealth; a positive representative consumer exists | Gorman 1953/1961; MWG 4.B, 4.D | M |
| Identical homothetic preferences | yes | Aggregate demand = one consumer's demand at aggregate wealth: aggregate WARP, uniqueness under the usual conditions; the macro representative agent | MWG 4.B–4.D; Eisenberg 1961 | E–M |
| Gross substitutes (excess demand) | **yes** (sum of GS functions is GS) | Unique normalized equilibrium; global stability of tâtonnement | Arrow–Block–Hurwicz 1959; MWG 17.F | M–H |
| Law of demand (uncompensated, fixed wealth) | **yes** | Aggregate law of demand ⇒ uniqueness and stability; aggregate WARP | MWG 4.C | M |
| Mitjushin–Polterovich curvature bound: −x·D²u(x)x / x·Du(x) < 4 | via the law of demand | Individual (hence aggregate) law of demand | Mitjushin–Polterovich 1978; Milleron | H |
| Hildenbrand distributional condition: identical demand functions, wealth density decreasing on [0, w̄] | property of the population | Market demand satisfies the law of demand, though individuals need not | Hildenbrand 1983; Härdle–Hildenbrand–Jerison 1991 (increasing dispersion) | H |
| Behavioral heterogeneity: preferences spread "enough" across a family of commodity-space transformations | property of the population | Aggregate demand approximately gross substitutes / law of demand | Grandmont 1992; Quah 1997 | H–R |
| Complete markets + common discounting | n/a | Planner/representative-agent representation of equilibrium prices (with Negishi weights) | Constantinides 1982; Negishi 1960 | M |
| Individual endowments and incomes observed | n/a | SMD fails: GE has testable restrictions on observed data | Brown–Matzkin 1996 (finite data) | M–H (guess) |

**Deliverables.** (1) SMD in Debreu's (1974) form, the flagship theorem. Its
proof is constructive (one consumer per good, each demanding along one
direction), so H rather than R is plausible, but this is a guess. (2) Each row
as a Lean theorem stated against `Core` primitives. (3) A Lean-checked
"lattice" of restrictions: which imply which (e.g. identical homothetic ⇒
Gorman ⇒ positive representative consumer; MP condition ⇒ law of demand ⇒
aggregate WARP). (4) Open problems stated precisely, e.g. weaker conditions
than Hildenbrand's or Grandmont's that still give the aggregate law of demand;
which modern HANK results survive dropping CRRA.

**Dependencies.** Needs the consumer theory (done), GE existence (M4) for the
equilibrium-set statements, and `Core` (MU0). Can start as soon as M4 lands,
well before the rest of Phase U.

### 7.3 Deliverables of Phase U
1. `Core/` abstractions with the instance theorems above.
2. Bridge theorems B1–B10, known parts proved, missing parts stated precisely as open `Prop`s (no `sorry`; stated as definitions of conjectures, so the axiom audit stays clean).
3. **Assumption atlas**: a script that walks Lean's dependency graph and reports, for every macro result, which micro primitives and hypotheses it actually uses (e.g. "this HANK result needs no borrowing constraint but does need CRRA"). This is only possible with a formal library and is the most concrete form of "connecting the fields."
4. **Robustness classification** for B5/B6: each macro result tagged as robust or knife-edge with respect to behavioral deviations.
5. A written synthesis (blueprint chapter) of what the formal map shows. If a new unifying result emerges, it goes through the two-step check like everything else.

---

## 8. Adversarial checking: making sure the theorems are right

Short answer to "doesn't Lean have adversarial checkers?": Lean has excellent
tools that check **proofs** (that is the kernel's job, and it is very
trustworthy). It has nothing built in that checks a **statement** says what the
textbook says. Almost all real formalization bugs are of the second kind: a
definition that is subtly off, a hypothesis that can never hold, or a junk
value that makes the conclusion trivially true. So the checker has three layers.

### 8.0 The verification protocol (geoff's rule, mandatory)
When we say a theorem is "checked", it has passed these two steps, in this order:

1. **Context-isolated adversarial agent.** Spin up a fresh agent that has never
   seen the proofs, our comments, or this thread. It gets only the Lean
   statements (and the definitions they use) plus the canonical textbook
   reference (MWG, Stokey–Lucas, Ljungqvist–Sargent, Acemoglu …), and its job
   is to show that a statement does *not* match canonical economics. Procedure
   and verdicts are in §8.3. Anything rated **wrong** is fixed and goes back
   through step 1.
2. **Comparator and proof reverifiers.** Once the statements pass, freeze
   them in `Audit/Statements/` and run:
   - **Comparator** (`leanprover/comparator`, or `SafeVerify` as fallback):
     the proofs prove exactly the frozen statements, using only the allowed
     axioms (`propext`, `Classical.choice`, `Quot.sound`).
   - **Proof reverifiers**: `lean4checker` (replays every declaration through
     Lean's own kernel) and **nanoda** (an independent kernel written in Rust,
     so a bug in Lean's kernel would not hide a bad proof).

   Both must pass; a failure blocks the milestone.

The rule applies unchanged to the expanded scope, with two additions:
- **Modern and behavioral models**: the canonical reference is the original
  paper cited in §5–6 (e.g. Kőszegi–Rabin 2006, not "reference dependence" in
  general). The adversarial agent gets that paper's statement and must flag any
  variant we chose instead.
- **Bridge theorems and open bridges (§7)**: the agent also checks that `Core`
  instances really are the textbook equilibrium concept (both directions of
  each instance theorem), and that open bridges stated as `Prop`s are neither
  trivially true nor trivially false.

Layers 1 and 2 below (axiom audit, linters, witnesses, counterexamples,
unit tests) are the supporting checks that feed both steps.

### 8.1 Layer 1: proof integrity (automated, in CI, cheap)
| Check | Tool | Catches |
|---|---|---|
| No `sorry`, `admit`, custom `axiom` | `#print axioms` on every headline theorem; allowed set is exactly `propext`, `Classical.choice`, `Quot.sound` | unfinished or assumed results |
| No `native_decide` / `Lean.ofReduceBool` / `implemented_by` tricks | same axiom audit + grep | proofs trusting compiled code |
| Independent kernel replay | `lean4checker` (re-checks every declaration in the `.olean`s through the kernel) | environment tampering by metaprograms or tactics |
| Independent kernel implementation | `nanoda` (Rust re-implementation of the Lean kernel; check it supports our Lean version) on exported declarations | bugs in Lean's own kernel |
| Statement didn't drift | `leanprover/comparator` or `SafeVerify`: checks the proof file proves *exactly* the frozen reference statement in `Audit/Statements/`, with the same axioms | silently weakened theorems after refactors |
| Hygiene | Mathlib linters (`#lint`), `linter.unusedVariables`, `autoImplicit = false` (already set) | unused hypotheses (often a sign the statement is not what you think), accidental auto-bound variables |

Layer 1 makes "the proof is fine" essentially certain. It says nothing about meaning.

### 8.2 Layer 2: statement faithfulness (semi-automated, per theorem)
Every headline theorem gets an entry in `Audit/` with four artefacts:

1. **Non-vacuity witness.** A Lean `example` that builds a concrete object
   satisfying *all* hypotheses (e.g. Cobb–Douglas consumer, Brock–Mirman
   economy) and applies the theorem. If the hypotheses are contradictory, this
   cannot be written. Catches: inconsistent assumptions, e.g. requiring both
   strict monotonicity and satiation.
2. **Hypothesis necessity counterexamples.** For each hypothesis, either a
   Lean proof that the conclusion fails without it (e.g. Walras' law fails
   without local nonsatiation: a thick indifference curve), or a note saying it
   is redundant and should be removed. Catches: statements stronger or weaker
   than the textbook's.
3. **Definitional unit tests.** Lemmas pinning definitions to textbook
   formulas on concrete cases: Cobb–Douglas demand is `α w / p₁`, the expenditure
   function of Cobb–Douglas has its known closed form, the Solow steady state is
   `(s/(n+δ))^{1/(1−α)}`. If a definition is off, these fail.
4. **Junk-value audit.** Lean totalizes partial operations: `x / 0 = 0`,
   natural subtraction truncates, and `sSup` of an unbounded or empty set of
   reals is `0`. Our `indirectUtility` and `expenditure` are defined by
   `sSup`/`sInf`, so any theorem about them must either assume or prove
   attainment. The auditor checks each such theorem for a case where the
   conclusion holds only because of a junk value.

Light automation helps here: the `plausible` tactic (random testing, formerly
`slim_check`) can search for counterexamples to decidable or finite versions of
statements, and trying `exact?` / `aesop` / `simp` on a statement flags ones
that are suspiciously trivial.

### 8.3 Layer 3: adversarial review (an independent reviewer)
A separate reviewer, a fresh Claude agent given only the statements and the
textbook reference (never the proofs or our explanations, so it isn't
anchored on our reading), is asked to break each theorem:
- Write the textbook statement in English, then compare it line by line with the Lean statement and list every discrepancy (quantifier order, strict vs weak inequalities, missing interiority conditions, wrong domain such as `ℝ` vs `ℝ₊`).
- Try to derive `False` from the hypotheses, or prove the negation of the conclusion for some instance.
- Try to prove the statement with a trivial proof; if that works, explain why.
- Propose a counterexample from the economics literature (e.g. Straub–Werning for Chamley–Judd, the lexicographic order for Debreu).

Findings go into `Audit/REVIEW.md` per theorem with a verdict:
**faithful**, **faithful with documented deviation** (e.g. we assume
differentiability where MWG doesn't), or **wrong** (blocks the milestone). Only
statements with a "faithful" verdict are frozen into `Audit/Statements/`, which
Layer 1's comparator then protects. The human (geoff) signs off on each frozen
headline statement; this is also the best way to learn the material.

A **blueprint** (Patrick Massot's `leanblueprint`, used by FLT, PFR and most
large Lean projects) gives a LaTeX document with the human-readable statement
of each result linked to its Lean declaration and a dependency graph showing
what is proved. It is the natural home for the textbook-vs-Lean comparison and
for tracking this plan.

### 8.4 CI pipeline
```
lake build
→ lake exe lean4checker EconLean
→ lean4export | nanoda   (independent kernel)
→ audit script: #print axioms for every @[headline] theorem, fail on anything outside the allowed three
→ grep: fail on sorry / admit / native_decide / axiom / implemented_by
→ comparator: proof files vs Audit/Statements/
→ lake build EconLean.Audit   (witnesses, counterexamples, unit tests)
→ #lint
```
The adversarial agent (step 1 of §8.0) runs before statements are frozen,
per milestone, not in CI; the comparator and reverifier steps run on every push.

---

## 9. Milestones and dependency order

```
M0 Audit infra ──┬─► M1 Shared foundations (F1 F2 F5 F6 F7) ──┬─► M3 Producer + uncertainty ─► M4 GE + welfare (F3 F4) ─► M6 Games, info, mechanisms
                 │                                              │
                 └─► M2 Finish consumer (consumer thread) ──────┘
                                                                └─► M5 DP foundations (F8 F9 F14) ─► M7 Growth, OLG, search ─► M8 Stochastic macro (F10–F13) ─► M9 Policy & stretch

M1 ─► MU0 Core primitives (instances only) ─────────────── used by every later milestone
M3 + M6 ─► M10 Behavioral & modern micro (F19 F20 F21)
M8 ─► M11 Modern macro (F22 F23) ─► M12 Phase U: bridges, assumption atlas, synthesis
M4 + MU0 ─► MU1 Aggregation map: SMD and the restrictions that escape it (§7.2a)
```

| Milestone | Contents | Exit criterion | Size |
|---|---|---|---|
| **M0** Audit infrastructure | `Audit/` folder, adversarial-review prompt template, axiom-audit script, comparator + lean4checker + nanoda in CI, `@[headline]` attribute, witnesses and counterexamples for *all existing* consumer theorems, blueprint skeleton | CI green; every existing headline theorem has witness + review verdict | 1–2 weeks |
| **M1** Shared foundations | Correspondences, Berge, KKT, general envelope theorem, Topkis/Milgrom–Shannon | Berge used to prove continuity of demand | 4–6 weeks |
| **M2** Finish consumer theory | Remaining ROADMAP Stage 2–3 items, Ch. 4 aggregation | ROADMAP Stage 3 all ✅ | (consumer thread) |
| **M3** Producer + uncertainty | MWG Ch. 5–6 | Hotelling, vN–M, Arrow–Pratt, FOSD/SOSD audited | 4–6 weeks |
| **M4** General equilibrium | Exchange + production economies, both welfare theorems, core, **existence of Walrasian equilibrium** | Existence theorem frozen and reviewed (flagship) | 2–3 months |
| **M5** Dynamic programming | Blackwell, SL ch. 4 theorems, Benveniste–Scheinkman, Euler + TVC, linear difference systems | Brock–Mirman closed form verified via the general theory | 4–6 weeks |
| **M6** Games, info, mechanisms | Port EconCSLib/Lyu–Li; Ch. 7–9, 13–14, 21–23; auctions, matching, persuasion | Nash existence, SPE/one-shot deviation, Myerson, revenue equivalence audited | 3–4 months |
| **M7** Deterministic macro | Solow, Ramsey–Cass–Koopmans, Diamond and Samuelson OLG, McCall, DMP, AK/Romer | Planner problem solved via M5; Samuelson OLG welfare failure proved | 2–3 months |
| **M8** Stochastic macro | Stochastic DP, Markov chains and invariant distributions, Lucas tree, FTAP, PIH, RBC, Blanchard–Kahn, NK determinacy | Invariant distribution for stochastic growth | 3–4 months |
| **MU0** Core primitives | `Core/` abstractions; instance theorems for Walrasian, Nash and the existing consumer demand | Three instances proved; design revised once | 3–4 weeks (guess) |
| **M9** Policy and stretch | Ramsey taxation (with Straub–Werning), APS, dynamic contracts, Aiyagari, Debreu–Scarf, Debreu representation, Kuhn's theorem | Pick by interest | open-ended |

| **M10** Behavioral & modern micro | §5: CPT, Kőszegi–Rabin, β–δ, ambiguity, Luce/RI, level-k/QRE/Berk–Nash, learning, networks, market design, IO | Each model stated as a `Core` instance; RI ⟺ logit and QRE existence audited | 6–9 months (guess) |
| **M11** Modern macro | §6: heterogeneous agents, sequence space, MFG, info frictions, behavioral NK, Hulten, macro-finance, trade | Werning as-if and Hulten proved as `Core` theorems | 6–12 months (guess) |
| **MU1** Aggregation map (B0) | SMD (Debreu 1974 form), Gorman, identical homothetic, gross substitutes, law of demand, Mitjushin–Polterovich, Hildenbrand, Grandmont; implication lattice | SMD and at least three escape theorems proved and through the two-step check | 3–6 months (guess) |
| **M12** Phase U | §7.2–7.3: bridge theorems B0–B10, open bridges stated precisely, assumption atlas, robustness classification, synthesis | Atlas generated for all macro results; known bridges proved | open-ended (research) |

Realistic total for M0–M8: on the order of 1.5–2 years part time; the
parallel tracks shorten this if micro and macro run in separate threads. M0
should happen next, before more theorems pile up unaudited. With the expanded
scope (M10–M12) the honest estimate is several years part time, and the
unification phase is research with no guaranteed endpoint (guess). Running
micro, macro and behavioral tracks in parallel threads is what makes it
tractable.

### Suggested first tasks
1. **M0 audit infra** on the existing consumer files (no edits to their proofs; audit files only): witnesses for Walras' law, duality, Shephard/Roy/Slutsky; junk-value check on `indirectUtility`/`expenditure`; CI with axiom audit + lean4checker.
2. **Solow model** (`Macro/Growth/Solow.lean`): small, self-contained, gives the macro track an early win and exercises the "unit test" audit style.
3. **Core primitives sketch (MU0)** right after M1 starts, so producer, GE and macro models are written as instances from day one.
4. **Correspondences + Berge** (`Foundations/Correspondence.lean`, `Foundations/Maximum.lean`): the single most reused missing piece of math.

---

## 10. Existing work to reuse (see also ROADMAP.md)
- **EconCSLib** (Lean 4): strategic games, Nash, Arrow, Gibbard–Satterthwaite, VCG, Myerson, Gale–Shapley.
- **Lyu & Li**: Brouwer on simplices, Scarf, mixed Nash existence in Lean.
- **Isabelle AFP** Microeconomics / First Welfare Theorem: proof blueprint for GE.
- **J. Li vN–M in Lean 4**: reported partial; audit before use.
- Check licences and Lean/Mathlib versions before importing; prefer a pinned
  `require` over copying, and run our Layer 1 checks on anything imported.
