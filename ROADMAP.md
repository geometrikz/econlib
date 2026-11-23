# Roadmap: formalizing canonical microeconomic theory in Lean 4

Ordered so that each stage reuses the previous one, roughly following
Mas-Colell, Whinston & Green (MWG) and Kreps. ✅ = done in this repo.

## Stage 1: Choice and preferences (MWG ch. 1)
- ✅ Rational preferences, strict preference, indifference; MWG Prop. 1.B.1
- ✅ Utility representation ⇒ rationality (Prop. 1.B.2); ordinal invariance
- ✅ Finite X: rational ⟺ utility representable
- ○ Choice structures, Weak Axiom of Revealed Preference (WARP); Prop. 1.D.1–1.D.2
  (rational preferences generate choice satisfying WARP, and the converse on
  finite budget families)
- ○ Countable X: utility representation (needs an enumeration argument)

## Stage 2: Representation with topology (MWG §3.C)
- ○ Continuity of preferences (closed upper and lower contour sets)
- ○ Debreu's theorem: continuous rational preferences on ℝⁿ₊ admit a continuous
  utility. *Hard; good milestone.* An easier MWG version assumes monotonicity.
- ○ Lexicographic preferences on ℝ² have no utility representation (classic
  counterexample; nice exercise in cardinality arguments)

## Stage 3: Consumer choice (MWG ch. 2–3)
- ✅ Budget sets: homogeneity, convexity, closedness, compactness for p ≫ 0
- ✅ Walrasian demand: homogeneity of degree zero, convexity under convex prefs
- ✅ Existence of demand (continuous utility, extreme value theorem)
- ✅ Local nonsatiation, strong monotonicity ⇒ LNS, Walras' law
- ✅ Indirect utility, expenditure function, Hicksian demand (with existence)
- ✅ Duality: UMP ⇔ EMP, e(p, v(p,w)) = w, v(p, e(p,ū)) = ū, no excess utility
- ✅ v homogeneous of degree 0 and nondecreasing in w; e homogeneous of degree 1
  and concave in p
- ✅ WARP from utility maximization; compensated law of demand (MWG 2.F.1)
- ○ Quasiconvexity of v; continuity of v and demand (Berge's maximum theorem)
- ✅ Shephard's lemma, Roy's identity, Slutsky equation (envelope arguments
  via Fermat's theorem; differentiability assumed as in MWG)
- ○ Slutsky matrix symmetric and negative semidefinite
- ○ GARP and Afriat's theorem; integrability (recovering preferences)

## Stage 4: Choice under uncertainty (MWG ch. 6)
- ○ Lotteries as probability measures (Mathlib `PMF` for the finite case)
- ○ von Neumann–Morgenstern expected utility theorem
- ○ Risk aversion ⟺ concave Bernoulli utility (Jensen is in Mathlib)

## Stage 5: Exchange economies and welfare (MWG ch. 15–16)
- ○ Allocations, Pareto optimality, Walrasian equilibrium
- ○ First Welfare Theorem (purely algebraic; very doable)
- ○ Second Welfare Theorem (needs a separating hyperplane theorem: Mathlib has
  Hahn–Banach / `geometric_hahn_banach_*`)
- ○ Existence of Walrasian equilibrium (needs Brouwer or Kakutani; see the
  Lyu–Li Brouwer formalization below)

## Stage 6: Games and social choice (later)
- ○ Nash equilibrium existence, Arrow's theorem, mechanism design. These are
  already partly covered by other Lean projects (below), so reuse rather
  than redo.

## Existing work to learn from or reuse
- **Mathlib**: no economics, but all the order theory, real analysis,
  topology, convexity and probability we need.
- **Isabelle AFP, "Microeconomics and the First Welfare Theorem"**
  (Parsert & Kaliszyk, 2017–18): preferences, utility, exchange economies,
  First Welfare Theorem. The best blueprint for Stages 1, 3 and 5.
- **EconCSLib** (Bei et al., 2026, Lean 4 + Mathlib): preferences as total
  preorders, strategic games, Nash, Arrow, Gibbard–Satterthwaite, VCG, Myerson,
  Gale–Shapley. Computational-economics focus; no consumer theory or welfare
  theorems.
- **Lyu & Li, "Formalizing Scarf, Brouwer, and Nash in Lean"** (ICML 2026):
  Brouwer on simplices and mixed Nash existence. Useful for equilibrium existence.
- **Jingyuan Li, vNM theorem in Lean 4** (arXiv 2506.07066): reported to leave
  parts axiomatized or as placeholders; check before relying on it.
- **EconLib4** (Lean 4): broad scope, but mostly statements with ~210 `sorry`s.
- **CC Liang, Arrow's theorem in Lean 4** (Verso literate proof).
