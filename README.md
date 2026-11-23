# EconLean

A learning project: formalizing canonical microeconomic theory in Lean 4 with
Mathlib. Every file is heavily commented for readers who know the economics
(MWG / Kreps level) but are new to Lean.

- `EconLean/Preferences/Basic.lean`: rational preferences, ≻ and ∼, MWG 1.B.1
- `EconLean/Preferences/Utility.lean`: utility representations, ordinal
  invariance, existence on finite sets
- `ROADMAP.md`: what comes next, and related projects

## Build
```
lake exe cache get   # downloads prebuilt Mathlib
lake build
```
Pinned to Lean v4.36.0 and Mathlib v4.36.0.
