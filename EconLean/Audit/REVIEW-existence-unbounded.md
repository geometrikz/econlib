# Review: GE/ExistenceUnbounded.lean (2026-11-25)

Existence of Walrasian equilibrium with unbounded, closed, strictly convex
production sets `Yⱼ ∋ 0`, aggregate no free lunch and irreversibility
(`exists_walrasianEquilibrium_unbounded`), via bounded attainable production
(`exists_bound_attainable`), Euclidean truncation and the compact theorem.

Context-isolated adversarial review: no substantive issues; all statements true,
non-vacuous and canonical (Arrow–Debreu 1954 Assumption I; MWG Def. 17.B.1
equilibrium). Findings applied:
1. Header now says strict convexity forces full-dimensional `Yⱼ` and excludes
   CRS, linear activities, flat facets and free disposal.
2. Header states this theorem and the compact one are not nested.
3. Uncertain section/proposition numbers replaced by Arrow–Debreu Assumption I
   and "Debreu (1959) ch. 5".
4. Main docstring mentions single-valued demand (`RegularUtility`).
5. `parabolaSet` gloss restricted to `a ∈ [0, 1]`.
6. Witness has one firm; multi-firm witness noted as open (not done).
7. Truncation wording: each firm's component `yⱼ`.

Checks: axioms {propext, Classical.choice, Quot.sound}; leanchecker clean;
nanoda 30698 declarations, no typechecker errors; frozen statements in
`Audit/Statements/GE.lean` (section ExistenceUnbounded).
