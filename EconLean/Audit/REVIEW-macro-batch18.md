# Review: macro batch 18 (Campbell–Shiller, Bansal–Yaron long-run risk)

Context-isolated adversarial referee, 2026-11-25. No blockers or majors. Verified by hand: forward
iteration and the k/(1−ρ) term; A₁ = (1−1/ψ)/(1−κ₁ρ); SDF innovation −γσε − λ_e σ e with
λ_e = (γ−1/ψ)κ₁φ_e/(1−κ₁ρ) (= Bansal–Yaron's λ_{m,e}); premium formula. Witness for
`returns_predictable`: Ω = Bool, p = ½, pd = ±1, Δd = 0, r = k − (1−ρ)pd.

| # | Sev. | Item | Resolution |
|---|------|------|------------|
| 1 | MINOR | `Bdd r` redundant | Dropped; derived in `bdd_r`. |
| 2 | MINOR | ρ range, k free | Docstring updated. |
| 3 | MINOR | p not required ≥ 0 | Added `IsProb` (nonnegative, sums to 1). |
| 4 | MINOR | Cochrane sign/moment convention | Docstring: pd vs dp units, cross-state vs time-series. |
| 5 | MINOR | `returns_predictable` is a corollary | Labelled as such. |
| 6 | MINOR | `xCoeff` hand-written | Added `logEuler` (conditional mean from the dynamics), `logEuler_affine`, `euler_forces_A₁`. |
| 7 | MINOR | σ unrestricted | `hσ : 0 < σ` in `Params`; per-theorem hσ dropped. |
| 8 | MINOR | κ₁ fixed in `lamE_strictMono_ρ` | Docstring note. |
| 9 | MINOR | `wealth_premium_gt` hypotheses only sufficient | Docstring note with the exact excess. |
| 10 | MINOR | `calibration` too loose | Replaced by `byCalibration` with BY values and `17 < λ_e < 17.2`. |
| 11 | MINOR | `premium` is a definition | Kept; documented under Deviations. |

Frozen statements: `Audit/Statements/MacroBatch18.lean`.
