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
- ○ Budget sets, Walrasian demand correspondence
- ○ Existence of demand: continuous utility on compact budget set (extreme
  value theorem, which Mathlib has: `IsCompact.exists_isMaxOn`)
- ○ Walras' law under local nonsatiation; homogeneity of degree zero
- ○ Indirect utility, expenditure function, Hicksian demand; duality identities
- ○ Revealed preference for demand: WARP / SARP / GARP, Afriat's theorem
- ○ Slutsky equation (needs differentiability; Mathlib calculus is adequate)

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
