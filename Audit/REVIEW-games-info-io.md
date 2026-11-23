# Review: potential and supermodular games, agreement, cascades, cheap talk, SPA, Maskin, linear city

Date: 2026-11-23. New modules: Games/{Potential,Supermodular}, Information/{Agreement,Cascades,CheapTalk},
Mechanism/{SecondPrice,Implementation}, Partial/Hotelling. Frozen: Audit/Statements/GamesInfoIO.lean (22 statements).
Blueprint: new sections appended to games.tex, asyminfo.tex, mechanism.tex, partial.tex.

## Isolated adversarial review (round 1, statement-only files)
| Headline | Verdict | Action |
|---|---|---|
| Potential games: Nash from maximizer, existence, FIP, Rosenthal congestion | OK | — |
| Supermodular: Topkis monotone BR, greatest/least pure NE | OK (finite chains only) | Scope note added (Milgrom–Roberts allow complete lattices). |
| `aumann_agreement` (self-evident set form of common knowledge) | OK | — |
| Cascades: absorption, first-two-signals cascade | OK; `cascadeAction_eq_bayes` WEAK vs docstring | Scope note: public state is modelled as revealed-signal count; tie rule (follow own signal) vs BHW coin flip stated. |
| Crawford–Sobel arbitrage, closed form, existence iff 2N(N−1)b<1 | OK | Scope note: midpoint rule and partition form built into the definition. |
| SPA truthful weakly dominant (strict part included), Nash, efficiency | OK | — |
| Maskin necessity; sufficiency with n≥3 and no veto power; weak Pareto example | OK | — |
| Hotelling price equilibrium | WEAK (one firm, abstract demand) | Added `hotellingDemand` (truncated) and `hotelling_nash`: joint Nash equilibrium of the price game with true demands. |
| Hotelling maximal differentiation | OK as comparative static; docstring overclaimed | Docstrings now say location game/leapfrogging not formalized. |

## Round 2 (revised files)
All three items RESOLVED (Hotelling joint equilibrium verified algebraically by the reviewer; cascades and cheap talk by disclosure). Remaining nits fixed in docstrings.

## Mechanical checks
- `#print axioms`: all 100 blueprint-listed declarations use at most propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on all 8 new modules and the frozen file.
- nanoda: 43,158 declarations, no typechecker errors.
- Full shared build: 7300 jobs, warning-free. Blueprint PDF: 137 pages, all `\lean` names resolve.

## Open follow-ups
Rubinstein alternating offers; TTC/housing market; matching with contracts; school choice (Boston); global games; BCE;
Grossman–Hart–Moore; informativeness principle; full Bayesian cascade model; location stage of the linear city.
