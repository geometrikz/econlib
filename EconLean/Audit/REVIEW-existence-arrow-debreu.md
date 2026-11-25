# Review: GE/ExistenceArrowDebreu.lean (2026-11-25)

Arrow–Debreu existence with closed convex production sets (constant returns,
free disposal, set-valued supply allowed) via Kakutani on
`Δ × [0, c]^{A×L} × ∏ⱼ Tⱼ` after truncating production and consumption.

Context-isolated adversarial review: no substantive issues. Main theorem true,
non-vacuous, canonical equilibrium notion (profit max on untruncated `Yⱼ`,
demand at private-ownership wealth, exact clearing); hypotheses match Arrow–Debreu
1954 Theorem I (I.a–c, survival IV.c as `ωₐ ≫ 0` for `Xₐ = ℝᴸ₊`) with stronger
preference assumptions. The `max w m` floor and `max(0, p·yⱼ)` wealth are internal
devices that drop out at the fixed point. Witness `linearEconomy` (closed convex
cone with free disposal, not strictly convex, unbounded) applies the theorem
with all hypotheses discharged.

Wording fixes applied: scope notes strong monotonicity vs AD nonsatiation and
`p ≥ 0`; continuity stated on all of `ℝᴸ` (no loss); witness noted as unbounded
hence not compact, and only existence claimed (firm may be inactive); total
endowment notation.

Checks: axioms {propext, Classical.choice, Quot.sound}; leanchecker clean;
nanoda 31412 declarations, no typechecker errors; frozen statement in
`Audit/Statements/GE.lean` (section ExistenceArrowDebreu).

## Addendum (2026-11-25): convex preferences

New `exists_walrasianEquilibrium_arrowDebreu_convex`: utilities only
quasiconcave on `ℝᴸ₊` (MWG Def. 3.B.4 convex preferences), with set-valued
truncated demand (`truncDemand_props`) in the Kakutani map. The strictly
quasiconcave theorem is now a corollary (statement unchanged). Witness
`substEconomy` with perfect substitutes `x₀ + x₁`.

Isolated adversarial review: no substantive issues; lift-back uses only
continuity, quasiconcavity and strong monotonicity (on `ℝᴸ₊` these imply
Arrow–Debreu's convexity, so the hypotheses are not claimed weaker). Fixes
applied: representation-invariant `not_strictlyQuasiconcave_of_prefOf_eq_uLin`;
stale comment; blueprint states the convex theorem in full, the strict one as
corollary, and corrects the `δ` wording.

Checks: axioms standard; leanchecker clean; nanoda 31402 declarations, no
typechecker errors; frozen `frozen_exists_walrasianEquilibrium_arrowDebreu_convex`
and `frozen_quasiconcaveOn` added.

## Addendum 2 (2026-11-25): local nonsatiation

New `exists_freeDisposalEquilibrium_arrowDebreu` (LNS + quasiconcave utilities;
p in the simplex, z ≤ 0, p·z = 0: AD 1954's equilibrium notion) and
`exists_walrasianEquilibrium_arrowDebreu_lns` (a free-disposal firm absorbs the
excess supply; exact clearing, prices in the simplex). The strongly monotone
theorem is now derived from the free-disposal one (statement unchanged).
Witness `leonProdEconomy` (Leontief, not strongly monotone).

Isolated adversarial review: no substantive issues. Fixes applied: Debreu 1959
cited for the exact-clearing free-disposal form, AD 1954 for z ≤ 0; scope note
corrected (AD: global nonsatiation + semi-strict convexity, which imply LNS;
neither assumption set contains the other); blueprint proof moved so the
Kakutani sketch sits in the free-disposal theorem (no circular references);
`lns_leon` added to the blueprint. Not done (noted open): weakening the
free-disposal hypothesis to the aggregate set; a witness in which disposal is
actually needed (Leontief witness only shows strong monotonicity fails).

Checks: axioms standard; leanchecker clean; nanoda 31350 declarations, no
typechecker errors; frozen statements added for both new theorems and
`FreeDisposal`.
