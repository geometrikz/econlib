# Review: GE/ValuationEquilibrium.lean (B4.6 SWT part: Second Welfare Theorem in a topological vector space)

Context-isolated adversarial review (2026-11-25): core definitions and
`second_welfare_theorem_tvs` are faithful (Debreu 1954 Thm 2 generality: any real
TVS, no Hausdorff/local convexity; weak PO, convex strictly-better sets, LNS at x
as closure, interior of aggregate better set; nonzero continuous linear p,
quasi-equilibrium). Cheaper-point step matches MWG 16.D.2.

Fixes applied:
1. (Medium) The equilibrium form had `hcheap` quantified over every supporting p,
   which failed on the file's own ℓ^∞ witness and was close to assuming the
   conclusion. Replaced by the exogenous condition `∀ a, x a ∈ interior (C a)`
   via new `exists_cheaper_of_mem_interior`; added witness `commonEconomy_*`
   on ℓ^∞ satisfying every hypothesis of the equilibrium form.
2. ℓ^∞ two-agent example relabelled a toy economy (not Bewley's setting).
3. Caveat added: in ℓ^∞ the valuation may be purely finitely additive; Bewley's
   ℓ¹ prices (Mackey continuity) not formalized.
4. Docstring notes that the equilibrium predicates omit market clearing.
5. Header now says the interior lemma needs all better sets nonempty.
6. Deviations list MWG quasi-equilibrium form vs Debreu's cost-minimisation and
   production; unverified "§6" citation removed.

Mechanical checks: axioms standard only, leanchecker OK, nanoda (27541 decls) OK,
frozen statements in Audit/Statements/GE.lean build.
