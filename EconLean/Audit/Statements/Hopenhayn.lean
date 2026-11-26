/-
# Frozen statements: Hopenhayn (1992) stationary equilibrium

Headline statements of `Macro/Firms/Hopenhayn.lean`, copied verbatim after the
context-isolated adversarial review (record in `Audit/REVIEW-hopenhayn.md`).
Each statement is closed by the library theorem, so this file stops compiling
if a library statement is ever weakened.
-/
module

public import EconLean.Macro.Firms.Hopenhayn

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ Real Finset Hopenhayn Hopenhayn.Model

namespace HopenhaynFrozen

variable {X : Type*} [Fintype X] (m : Model X)

theorem frozen_hop_V_eq (p : ℝ) (x : X) :
    m.V p x = m.π p x + m.β * (1 - m.δ) * max (∑ x', m.Q x x' * m.V p x') 0 :=
  m.V_eq p x

theorem frozen_hop_V_unique (p : ℝ) (v : X → ℝ)
    (hv : ∀ x, v x = m.π p x + m.β * (1 - m.δ) * max (∑ x', m.Q x x' * v x') 0) : v = m.V p :=
  m.V_unique p v hv

theorem frozen_hop_entryValue_strictMono :
    StrictMonoOn (fun p => ∑ x, m.ν x * m.V p x) (Ioi 0) :=
  m.entryValue_strictMono

theorem frozen_hop_stays_isUpperSet [Preorder X] (hπ : ∀ p, Monotone (m.π p))
    (hQ : ∀ v : X → ℝ, Monotone v → Monotone fun x => ∑ x', m.Q x x' * v x') (p : ℝ) :
    IsUpperSet {x | 0 ≤ ∑ x', m.Q x x' * m.V p x'} :=
  m.stays_isUpperSet hπ hQ p

theorem frozen_hop_exists_unique_stationary (p M : ℝ) :
    m.IsStationary p M (M • m.μ₁ p) ∧ ∀ μ, m.IsStationary p M μ → μ = M • m.μ₁ p :=
  m.exists_unique_stationary p M

theorem frozen_hop_exists_unique_equilibrium {plo phi : ℝ} (hplo : 0 < plo) (hphi : 0 < phi)
    (hlo : ∀ x, m.π plo x ≤ 0) (hhi : m.ce ≤ ∑ x, m.ν x * m.π phi x) :
    ∃! e : ℝ × ℝ × (X → ℝ), m.IsEquilibrium e.1 e.2.1 e.2.2 :=
  m.exists_unique_equilibrium hplo hphi hlo hhi

theorem frozen_hop_equilibrium_nonneg {p M : ℝ} {μ : X → ℝ} (h : m.IsEquilibrium p M μ) : 0 ≤ μ :=
  Model.IsEquilibrium.nonneg m h

theorem frozen_hop_example₁_equilibrium :
    ∃! e : ℝ × ℝ × (Fin 2 → ℝ), example₁.IsEquilibrium e.1 e.2.1 e.2.2 :=
  example₁_equilibrium

end HopenhaynFrozen

end Econ.Audit
