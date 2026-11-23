# EconLean master plan: all of graduate micro and macro in Lean 4

Status as of 2026-11-23. Companion to `ROADMAP.md` (which tracks the
consumer-theory stage in detail). This file is the long-range plan: scope,
library layout, the Mathlib foundations we must build, dependency order,
milestones, and how we check that what we prove is actually the economics.

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
   in MWG. Every milestone therefore ends with the adversarial audit in §5
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
5. **Statements are frozen and reviewed.** Each headline theorem has a
   reviewed reference statement, cited to the textbook, that CI checks the
   proof against (§5.3). Proofs can change freely; statements only with review.

---

## 1. Library layout

```
EconLean/
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
  Macro/
    Growth/             Solow, Ramsey–Cass–Koopmans, endogenous growth
    OLG/
    AssetPricing/
    Consumption/        PIH, precautionary saving, incomplete markets
    Search/
    RBC/
    Policy/             fiscal, monetary, time consistency, recursive contracts
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
  boundedness lemma (see the junk-value warning in §5.2).

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
| F18 | Continuous-time optimal control (Pontryagin, HJB, viscosity solutions); Itô calculus | continuous-time growth, Merton, HACT | R | Out of scope; discrete-time versions only. |

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

## 5. Adversarial checking: making sure the theorems are right

Short answer to "doesn't Lean have adversarial checkers?": Lean has excellent
tools that check **proofs** (that is the kernel's job, and it is very
trustworthy). It has nothing built in that checks a **statement** says what the
textbook says. Almost all real formalization bugs are of the second kind: a
definition that is subtly off, a hypothesis that can never hold, or a junk
value that makes the conclusion trivially true. So the checker has three layers.

### 5.0 The verification protocol (geoff's rule, mandatory)
When we say a theorem is "checked", it has passed these two steps, in this order:

1. **Context-isolated adversarial agent.** Spin up a fresh agent that has never
   seen the proofs, our comments, or this thread. It gets only the Lean
   statements (and the definitions they use) plus the canonical textbook
   reference (MWG, Stokey–Lucas, Ljungqvist–Sargent, Acemoglu …), and its job
   is to show that a statement does *not* match canonical economics. Procedure
   and verdicts are in §5.3. Anything rated **wrong** is fixed and goes back
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

Layers 1 and 2 below (axiom audit, linters, witnesses, counterexamples,
unit tests) are the supporting checks that feed both steps.

### 5.1 Layer 1: proof integrity (automated, in CI, cheap)
| Check | Tool | Catches |
|---|---|---|
| No `sorry`, `admit`, custom `axiom` | `#print axioms` on every headline theorem; allowed set is exactly `propext`, `Classical.choice`, `Quot.sound` | unfinished or assumed results |
| No `native_decide` / `Lean.ofReduceBool` / `implemented_by` tricks | same axiom audit + grep | proofs trusting compiled code |
| Independent kernel replay | `lean4checker` (re-checks every declaration in the `.olean`s through the kernel) | environment tampering by metaprograms or tactics |
| Independent kernel implementation | `nanoda` (Rust re-implementation of the Lean kernel; check it supports our Lean version) on exported declarations | bugs in Lean's own kernel |
| Statement didn't drift | `leanprover/comparator` or `SafeVerify`: checks the proof file proves *exactly* the frozen reference statement in `Audit/Statements/`, with the same axioms | silently weakened theorems after refactors |
| Hygiene | Mathlib linters (`#lint`), `linter.unusedVariables`, `autoImplicit = false` (already set) | unused hypotheses (often a sign the statement is not what you think), accidental auto-bound variables |

Layer 1 makes "the proof is fine" essentially certain. It says nothing about meaning.

### 5.2 Layer 2: statement faithfulness (semi-automated, per theorem)
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

### 5.3 Layer 3: adversarial review (an independent reviewer)
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

### 5.4 CI pipeline
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
The adversarial agent (step 1 of §5.0) runs before statements are frozen,
per milestone, not in CI; the comparator and reverifier steps run on every push.

---

## 6. Milestones and dependency order

```
M0 Audit infra ──┬─► M1 Shared foundations (F1 F2 F5 F6 F7) ──┬─► M3 Producer + uncertainty ─► M4 GE + welfare (F3 F4) ─► M6 Games, info, mechanisms
                 │                                              │
                 └─► M2 Finish consumer (consumer thread) ──────┘
                                                                └─► M5 DP foundations (F8 F9 F14) ─► M7 Growth, OLG, search ─► M8 Stochastic macro (F10–F13) ─► M9 Policy & stretch
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
| **M9** Policy and stretch | Ramsey taxation (with Straub–Werning), APS, dynamic contracts, Aiyagari, Debreu–Scarf, Debreu representation, Kuhn's theorem | Pick by interest | open-ended |

Realistic total for M0–M8: on the order of 1.5–2 years part time; the
parallel tracks shorten this if micro and macro run in separate threads. M0
should happen next, before more theorems pile up unaudited.

### Suggested first three tasks
1. **M0 audit infra** on the existing consumer files (no edits to their proofs; audit files only): witnesses for Walras' law, duality, Shephard/Roy/Slutsky; junk-value check on `indirectUtility`/`expenditure`; CI with axiom audit + lean4checker.
2. **Solow model** (`Macro/Growth/Solow.lean`): small, self-contained, gives the macro track an early win and exercises the "unit test" audit style.
3. **Correspondences + Berge** (`Foundations/Correspondence.lean`, `Foundations/Maximum.lean`): the single most reused missing piece of math.

---

## 7. Existing work to reuse (see also ROADMAP.md)
- **EconCSLib** (Lean 4): strategic games, Nash, Arrow, Gibbard–Satterthwaite, VCG, Myerson, Gale–Shapley.
- **Lyu & Li**: Brouwer on simplices, Scarf, mixed Nash existence in Lean.
- **Isabelle AFP** Microeconomics / First Welfare Theorem: proof blueprint for GE.
- **J. Li vN–M in Lean 4**: reported partial; audit before use.
- Check licences and Lean/Mathlib versions before importing; prefer a pinned
  `require` over copying, and run our Layer 1 checks on anything imported.
