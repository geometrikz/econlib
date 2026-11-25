/-
# Groves and VCG mechanisms

MWG §23.C (Prop. 23.C.4 and the Clarke mechanism); Vickrey (1961), Clarke (1971), Groves (1973). Agents have
quasilinear utilities: agent `i` of type `θᵢ` values the outcome `x` at `v i x θᵢ` and also
receives a money transfer. An **efficient** decision rule `k` maximizes total reported value.

A **Groves mechanism** pays each agent the others' reported value of the chosen outcome plus
a term `hᵢ` that does not depend on `i`'s own report:
`tᵢ(θ) = ∑_{j ≠ i} vⱼ(k θ, θⱼ) + hᵢ(θ₋ᵢ)`.
The **Clarke (pivot)** mechanism takes `hᵢ(θ₋ᵢ) = −max_x ∑_{j ≠ i} vⱼ(x, θⱼ)`, so each agent pays the
externality it imposes on the others.

Main results:
* `groves_truthful` (MWG Prop. 23.C.4): every Groves mechanism is strategy-proof.
* `clarke_transfer_nonpos`: Clarke transfers are payments (the mechanism never subsidizes).
* `clarke_individuallyRational`: with nonnegative valuations every truthful agent gets a
  nonnegative payoff.
* Witness: the second-price auction is the Clarke mechanism for one indivisible good.

The converse (Green–Laffont: every strategy-proof efficient mechanism is Groves, on an
unrestricted domain) is in `Mechanism/GreenLaffont`.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace Econ

open Finset Function

variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} {X : Type*}

/-- `k` is an **efficient** decision rule: it maximizes total reported value. -/
def IsEfficientRule (v : ∀ i, X → Θ i → ℝ) (k : (∀ i, Θ i) → X) : Prop :=
  ∀ θ x, ∑ i, v i x (θ i) ≤ ∑ i, v i (k θ) (θ i)

/-- A transfer term for agent `i` that ignores `i`'s own report. -/
def IgnoresOwn (i : I) (h : (∀ j, Θ j) → ℝ) : Prop :=
  ∀ θ (θi' : Θ i), h (update θ i θi') = h θ

/-- The **Groves transfer** to agent `i`. -/
def grovesTransfer (v : ∀ i, X → Θ i → ℝ) (k : (∀ i, Θ i) → X) (h : I → (∀ j, Θ j) → ℝ)
    (i : I) (θ : ∀ j, Θ j) : ℝ :=
  ∑ j ∈ univ.erase i, v j (k θ) (θ j) + h i θ

/-- **Groves mechanisms are strategy-proof** (MWG Prop. 23.C.4). For every true type `θᵢ`,
every report `θᵢ'` and every report profile `θ` of the others, reporting truthfully gives
at least as much value plus transfer. -/
theorem groves_truthful {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X} (hk : IsEfficientRule v k)
    {h : I → (∀ j, Θ j) → ℝ} (hh : ∀ i, IgnoresOwn i (h i)) (i : I) (θ : ∀ j, Θ j)
    (θi' : Θ i) :
    v i (k (update θ i θi')) (θ i) + grovesTransfer v k h i (update θ i θi') ≤
      v i (k θ) (θ i) + grovesTransfer v k h i θ := by
  simp only [grovesTransfer]
  rw [hh i θ θi']
  -- Both sides are total value at the true profile `θ`, under `k θ'` and `k θ`.
  have hsplit : ∀ x, v i x (θ i) + ∑ j ∈ univ.erase i, v j x (θ j) = ∑ j, v j x (θ j) :=
    fun x => Finset.add_sum_erase _ (fun j => v j x (θ j)) (mem_univ i)
  have hrest : ∑ j ∈ univ.erase i, v j (k (update θ i θi')) (update θ i θi' j) =
      ∑ j ∈ univ.erase i, v j (k (update θ i θi')) (θ j) :=
    Finset.sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  rw [hrest]
  have := hk θ (k (update θ i θi'))
  linarith [hsplit (k (update θ i θi')), hsplit (k θ)]

variable [Fintype X] [Nonempty X]

/-- The others' maximal total value, `max_x ∑_{j ≠ i} vⱼ(x, θⱼ)`. -/
def othersMax (v : ∀ i, X → Θ i → ℝ) (i : I) (θ : ∀ j, Θ j) : ℝ :=
  univ.sup' univ_nonempty fun x => ∑ j ∈ univ.erase i, v j x (θ j)

theorem othersMax_ignoresOwn (v : ∀ i, X → Θ i → ℝ) (i : I) : IgnoresOwn i (fun θ => -othersMax v i θ) := by
  intro θ θi'
  simp only [othersMax, neg_inj]
  congr 1
  funext x
  exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- The **Clarke pivot** transfer: `tᵢ = ∑_{j≠i} vⱼ(k θ) − max_x ∑_{j≠i} vⱼ(x)`. -/
def clarkeTransfer (v : ∀ i, X → Θ i → ℝ) (k : (∀ i, Θ i) → X) (i : I) (θ : ∀ j, Θ j) : ℝ :=
  grovesTransfer v k (fun i θ => -othersMax v i θ) i θ

/-- The Clarke mechanism is strategy-proof. -/
theorem clarke_truthful {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X} (hk : IsEfficientRule v k)
    (i : I) (θ : ∀ j, Θ j) (θi' : Θ i) :
    v i (k (update θ i θi')) (θ i) + clarkeTransfer v k i (update θ i θi') ≤
      v i (k θ) (θ i) + clarkeTransfer v k i θ :=
  groves_truthful hk (fun i => othersMax_ignoresOwn v i) i θ θi'

/-- **No subsidies**: every Clarke transfer is a payment, `tᵢ ≤ 0`. -/
theorem clarke_transfer_nonpos (v : ∀ i, X → Θ i → ℝ) (k : (∀ i, Θ i) → X) (i : I)
    (θ : ∀ j, Θ j) : clarkeTransfer v k i θ ≤ 0 := by
  simp only [clarkeTransfer, grovesTransfer, othersMax]
  have := Finset.le_sup' (fun x => ∑ j ∈ univ.erase i, v j x (θ j)) (mem_univ (k θ))
  linarith

/-- **Individual rationality** of the Clarke mechanism: with nonnegative valuations, every
truthful agent ends up with a nonnegative payoff. -/
theorem clarke_individuallyRational {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X}
    (hk : IsEfficientRule v k) (hv : ∀ i x θi, 0 ≤ v i x θi) (i : I) (θ : ∀ j, Θ j) :
    0 ≤ v i (k θ) (θ i) + clarkeTransfer v k i θ := by
  simp only [clarkeTransfer, grovesTransfer, othersMax]
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' univ_nonempty
    (fun x => ∑ j ∈ univ.erase i, v j x (θ j))
  rw [hx]
  have hsplit : ∀ x, v i x (θ i) + ∑ j ∈ univ.erase i, v j x (θ j) = ∑ j, v j x (θ j) :=
    fun x => Finset.add_sum_erase _ (fun j => v j x (θ j)) (mem_univ i)
  have := hk θ x
  linarith [hsplit x, hsplit (k θ), hv i x (θ i)]

/-- Two bidders for one good: outcome `x` names the winner, bidder `i` of value `θᵢ` gets
`θᵢ` if it wins. -/
def auctionValue (i : Fin 2) (x : Fin 2) (θi : ℝ) : ℝ := if x = i then θi else 0

/-- The efficient rule gives the good to the higher bid (ties to bidder `0`). -/
noncomputable def highBidder (θ : Fin 2 → ℝ) : Fin 2 := if θ 1 ≤ θ 0 then 0 else 1

/-- **Witness: the Clarke mechanism is the second-price auction.** If bidder `0` bids more
than bidder `1 ≥ 0`, bidder `0` wins and pays bidder `1`'s bid. -/
example (θ : Fin 2 → ℝ) (h1 : 0 ≤ θ 1) (h : θ 1 ≤ θ 0) :
    highBidder θ = 0 ∧ clarkeTransfer auctionValue highBidder 0 θ = -θ 1 := by
  have hk : highBidder θ = 0 := by simp [highBidder, h]
  refine ⟨hk, ?_⟩
  have herase : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  simp only [clarkeTransfer, grovesTransfer, othersMax, herase, Finset.sum_singleton, hk,
    auctionValue]
  have hsup : (univ : Finset (Fin 2)).sup' univ_nonempty
      (fun x => if x = (1 : Fin 2) then θ 1 else 0) = θ 1 := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun x _ => by split_ifs <;> linarith
    · exact Finset.le_sup'_of_le _ (mem_univ 1) (by simp)
  rw [hsup]
  simp

end Econ
