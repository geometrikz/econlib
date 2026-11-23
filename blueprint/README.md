# Blueprint: human-readable proofs, one per Lean result

The blueprint is a LaTeX document, built with
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) (as in FLT and PFR),
that gives a human proof for every Lean result. Each entry is linked to its Lean
declaration, and the proof is written to follow the Lean proof step by step.

Published at https://geometrikz.github.io/econlib/blueprint/ (PDF:
https://geometrikz.github.io/econlib/blueprint.pdf) by the "Blueprint and docs"
GitHub Actions workflow on every push to `main`.

## Layout
- `src/content.tex`: the introduction and the list of chapters (`\input` lines).
- `src/chapters/<area>.tex`: one file per area (preferences, consumer, foundations,
  ge, dp, growth, olg, labor, ...). Add a new file for a new area and `\input` it
  in `content.tex`.
- `src/macros/common.tex`: shared notation (`\R`, `\pref`, ...) and theorem styles.
- `src/web.tex`, `src/print.tex`: web and PDF wrappers. Do not put content here.

## Adding an entry (required with every new Lean theorem)
```latex
\begin{theorem}[Shephard's lemma]
  \label{thm:shephard}
  \lean{Econ.shephard_lemma}
  \leanok
  \uses{def:expenditure, def:hicksian}
  If ... then $\partial e/\partial p_i = h_i(p,u)$.
\end{theorem}
\begin{proof}
  \leanok
  \uses{lem:expenditure-concave}
  Step 1 (the Lean `have h1`): ...
  Step 2: ...
\end{proof}
```
Rules (also in `CONVENTIONS.md`):
- `\lean{...}` takes fully qualified names, comma separated. CI checks they exist.
- `\leanok` in the statement: the Lean statement exists. `\leanok` in the proof:
  the Lean proof is complete (no `sorry`).
- `\uses{...}` lists labels of the definitions and results used. These edges make
  the dependency graph. Statement-level `\uses` are the definitions in the
  statement; proof-level `\uses` are the results the proof applies.
- Labels: `def:`, `lem:`, `thm:`, `cor:`, `prop:` plus a short kebab name. Unique
  across the whole blueprint.
- Follow the Lean proof: same steps in the same order, same case splits, and name
  the Mathlib lemmas that do real work. Do not substitute a slicker textbook proof.
- Same hypotheses as Lean. Note any gap with the textbook statement.
- Greek letters in Lean names are fine inside `\lean{...}`; the PDF
  build uses xelatex.

## Building
CI builds everything. To check locally or in a cloud sandbox:
```
pip install leanblueprint        # needs graphviz; PDF needs xelatex (texlive-xetex)
leanblueprint web                # writes blueprint/web and blueprint/lean_decls
leanblueprint pdf                # writes blueprint/print/print.pdf
lake exe checkdecls blueprint/lean_decls   # after `lake build`
```
