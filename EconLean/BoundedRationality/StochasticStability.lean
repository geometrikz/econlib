/-
# Stochastic stability and risk dominance

References. M. Kandori, G. Mailath and R. Rob (1993), "Learning, Mutation, and
Long Run Equilibria in Games", *Econometrica* 61(1); H. P. Young (1993),
"The Evolution of Conventions", *Econometrica* 61(1); J. Harsanyi and
R. Selten (1988) (risk dominance).

A symmetric 2×2 coordination game with strategies `A` and `B`: `A` against
`A` pays `a`, `A` against `B` pays `b`, `B` against `A` pays `c`, `B` against
`B` pays `d`, with `a > c` and `d > b` (both conventions are strict Nash
equilibria). Against a population in which a share `x` plays `A`, `A` is a
best reply iff `x ≥ p*`, where `p* = (d − b)/((a − c) + (d − b))`
(`bestA_iff`). `A` **risk-dominates** `B` when `a − c > d − b`, i.e.
`p* < 1/2` (`riskDominant_iff`).

**Basins.** In a population of `N`, leaving the `B` convention needs
`⌈N p*⌉` simultaneous mutations to `A` before `A` becomes a best reply
(`resistB`), and leaving the `A` convention needs `⌈N (1 − p*)⌉` mutations to
`B` (`resistA`). If `A` is risk dominant, then for large `N` the `A` basin is
strictly harder to leave (`resistB_lt_resistA`).

**Payoffs and thresholds.** Payoffs are against the population share
including the player itself ("playing the field", Young-style); KMR's uniform
random matching without self-matching shifts the thresholds by `O(1/N)` in
share, which does not affect the large-`N` statements. A convention is left
once the other strategy is a weak best reply.

**Selection (two-state reduction).** Following KMR's reduction to the two
conventions, the chain moves from one convention to the other with a
probability of order `ε^r`, `r` the number of mutations needed.
* `tendsto_weightA_of_bounds`: if the transition probabilities `p_AB(ε)`,
  `p_BA(ε)` are bounded above and below by constant multiples of `ε^{r_A}` and
  `ε^{r_B}` near `0`, and `r_B < r_A`, then the stationary weight of the `A`
  convention, `p_BA/(p_AB + p_BA)`, tends to `1`. The special case of
  transition probabilities exactly `ε^r` is `stationaryA`
  (`stationaryA_balance`, `tendsto_stationaryA`).
* `riskDominant_selected_twoState`, `riskDominant_selected_of_bounds`
  (**KMR/Young, in the two-state reduction**): if `A` is risk dominant, then
  in every large enough population, with transition exponents equal to the
  basin radii, the weight on the `A` convention tends to `1` as `ε → 0`.

The reduction of the full best-response-with-mutation chain on `{0, …, N}`
to its two conventions (via the Freidlin–Wentzell tree formula) is not
formalized, so "stochastically stable" is not defined here for the full
chain; the transition probabilities between conventions are inputs. The
full one-revision (birth–death) chain is treated in `KMRChain.lean`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

noncomputable section

namespace Econ

namespace StochasticStability

open Filter Topology

/-- A symmetric 2×2 coordination game. -/
structure Coord where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  hA : c < a
  hB : b < d

namespace Coord

variable (G : Coord)

/-- Expected payoff of `A` against a population with share `x` playing `A`. -/
def payA (x : ℝ) : ℝ := x * G.a + (1 - x) * G.b

/-- Expected payoff of `B` against a population with share `x` playing `A`. -/
def payB (x : ℝ) : ℝ := x * G.c + (1 - x) * G.d

/-- The mixed-equilibrium threshold `p* = (d − b)/((a − c) + (d − b))`. -/
def pstar : ℝ := (G.d - G.b) / ((G.a - G.c) + (G.d - G.b))

theorem den_pos : 0 < (G.a - G.c) + (G.d - G.b) := by linarith [G.hA, G.hB]

theorem pstar_pos : 0 < G.pstar := div_pos (by linarith [G.hB]) G.den_pos

theorem pstar_lt_one : G.pstar < 1 := by
  rw [pstar, div_lt_one G.den_pos]; linarith [G.hA]

/-- `A` is a best reply iff at least a share `p*` plays `A`. -/
theorem bestA_iff (x : ℝ) : G.payB x ≤ G.payA x ↔ G.pstar ≤ x := by
  rw [pstar, div_le_iff₀ G.den_pos, payA, payB]
  constructor <;> intro h <;> nlinarith

/-- `B` is a best reply iff at most a share `p*` plays `A`. -/
theorem bestB_iff (x : ℝ) : G.payA x ≤ G.payB x ↔ x ≤ G.pstar := by
  rw [pstar, le_div_iff₀ G.den_pos, payA, payB]
  constructor <;> intro h <;> nlinarith

/-- Risk dominance of `A`. -/
def RiskDominant : Prop := G.d - G.b < G.a - G.c

theorem riskDominant_iff : G.RiskDominant ↔ G.pstar < 1 / 2 := by
  rw [RiskDominant, pstar, div_lt_iff₀ G.den_pos]
  constructor <;> intro h <;> linarith

/-- Mutations needed to leave the `B` convention: the least `m` with `A` a best
reply when `m` of `N` play `A`. -/
def resistB (N : ℕ) : ℕ := ⌈N * G.pstar⌉₊

/-- Mutations needed to leave the `A` convention: the least `m` with `B` a best
reply when `m` of `N` play `B`. -/
def resistA (N : ℕ) : ℕ := ⌈N * (1 - G.pstar)⌉₊

/-- `resistB N` mutants to `A` make `A` a best reply, and fewer do not. -/
theorem resistB_spec {N : ℕ} (hN : 0 < N) :
    G.payB (G.resistB N / N) ≤ G.payA (G.resistB N / N) ∧
      ∀ m : ℕ, m < G.resistB N → G.payA (m / N) < G.payB (m / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(G.bestA_iff _).2 ?_, fun m hm => ?_⟩
  · rw [le_div_iff₀ hN', mul_comm]; exact Nat.le_ceil _
  · have h1 : (m : ℝ) < N * G.pstar := Nat.lt_ceil.1 hm
    have h2 : (m : ℝ) / N < G.pstar := by rw [div_lt_iff₀ hN']; linarith
    by_contra h
    rw [not_lt] at h
    exact absurd ((G.bestA_iff _).1 h) (not_le.2 h2)

/-- `resistA N` mutants to `B` make `B` a best reply, and fewer do not. -/
theorem resistA_spec {N : ℕ} (hN : 0 < N) :
    G.payA ((N - G.resistA N : ℝ) / N) ≤ G.payB ((N - G.resistA N : ℝ) / N) ∧
      ∀ m : ℕ, m < G.resistA N → G.payB ((N - m : ℝ) / N) < G.payA ((N - m : ℝ) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(G.bestB_iff _).2 ?_, fun m hm => ?_⟩
  · rw [div_le_iff₀ hN']
    have := Nat.le_ceil ((N : ℝ) * (1 - G.pstar))
    simp only [resistA] at *
    nlinarith
  · have h1 : (m : ℝ) < N * (1 - G.pstar) := Nat.lt_ceil.1 hm
    have h2 : G.pstar < ((N : ℝ) - m) / N := by rw [lt_div_iff₀ hN']; nlinarith
    by_contra h
    rw [not_lt] at h
    exact absurd ((G.bestB_iff _).1 h) (not_le.2 h2)

/-- **Risk dominance gives the larger basin**: for large populations, leaving
the `A` convention needs strictly more mutations than leaving `B`. -/
theorem resistB_lt_resistA (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, G.resistB N < G.resistA N := by
  rw [riskDominant_iff] at h
  have hgap : 0 < 1 - 2 * G.pstar := by linarith
  -- once `N (1 − 2p*) > 1`, the ceilings are separated
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / (1 - 2 * G.pstar))
  filter_upwards [eventually_ge_atTop N0] with N hN
  have hN1 : (N0 : ℝ) ≤ N := by exact_mod_cast hN
  have hbig : 1 < N * (1 - 2 * G.pstar) := by
    rw [div_lt_iff₀ hgap] at hN0; nlinarith
  unfold resistB resistA
  have hc : ⌈(N : ℝ) * G.pstar⌉₊ < (N : ℝ) * G.pstar + 1 :=
    Nat.ceil_lt_add_one (by have := G.pstar_pos; positivity)
  have : (⌈(N : ℝ) * G.pstar⌉₊ : ℝ) < N * (1 - G.pstar) := by nlinarith
  exact_mod_cast (Nat.lt_ceil.2 this)

end Coord

/-! ### The two-convention chain -/

/-- Stationary weight of the `A` convention when leaving `A` has probability
`ε^{rA}` and leaving `B` has probability `ε^{rB}`. -/
def stationaryA (rA rB : ℕ) (ε : ℝ) : ℝ := ε ^ rB / (ε ^ rA + ε ^ rB)

/-- It is the stationary distribution: flows balance,
`π_A ε^{rA} = π_B ε^{rB}`. -/
theorem stationaryA_balance {rA rB : ℕ} {ε : ℝ} (hε : 0 < ε) :
    stationaryA rA rB ε * ε ^ rA = (1 - stationaryA rA rB ε) * ε ^ rB := by
  have h : 0 < ε ^ rA + ε ^ rB := by positivity
  unfold stationaryA
  field_simp
  ring

/-- **Selection**: if leaving `B` is cheaper (`rB < rA`), the stationary weight
of `A` tends to `1` as mutations vanish. -/
theorem tendsto_stationaryA {rA rB : ℕ} (h : rB < rA) :
    Tendsto (stationaryA rA rB) (𝓝[>] 0) (𝓝 1) := by
  -- `π_A = 1/(1 + ε^{rA − rB})`
  have e : ∀ ε : ℝ, 0 < ε → stationaryA rA rB ε = 1 / (1 + ε ^ (rA - rB)) := fun ε hε => by
    unfold stationaryA
    have hpow : ε ^ rA = ε ^ rB * ε ^ (rA - rB) := by
      rw [← pow_add, Nat.add_sub_cancel' h.le]
    rw [hpow]
    have : 0 < ε ^ rB := by positivity
    field_simp
    ring
  have hk : 0 < rA - rB := Nat.sub_pos_of_lt h
  have hlim : Tendsto (fun ε : ℝ => 1 / (1 + ε ^ (rA - rB))) (𝓝[>] 0) (𝓝 (1 / (1 + 0 ^ (rA - rB)))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact (tendsto_const_nhds.div (tendsto_const_nhds.add
      ((continuous_pow (rA - rB)).tendsto 0)) (by simp [zero_pow hk.ne']))
  rw [zero_pow hk.ne', add_zero, div_one] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => (e ε hε).symm)

/-- **Kandori–Mailath–Rob / Young.** If `A` risk-dominates `B`, then in every
large enough population the `A` convention is stochastically stable: its
stationary weight tends to `1` as mutations vanish. -/
theorem riskDominant_selected_twoState (G : Coord) (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop,
      Tendsto (stationaryA (G.resistA N) (G.resistB N)) (𝓝[>] 0) (𝓝 1) :=
  (G.resistB_lt_resistA h).mono fun _ hN => tendsto_stationaryA hN

/-- **Selection with transition probabilities of order `ε^r`**: if
`c ε^{r_A} ≤ p_AB(ε) ≤ C ε^{r_A}` and `c ε^{r_B} ≤ p_BA(ε) ≤ C ε^{r_B}` for small
`ε > 0` (constants `0 < c ≤ C`), and `r_B < r_A`, then the stationary weight of
`A`, `p_BA/(p_AB + p_BA)`, tends to `1`. -/
theorem tendsto_weightA_of_bounds {rA rB : ℕ} (h : rB < rA) {pAB pBA : ℝ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c * ε ^ rA ≤ pAB ε ∧ pAB ε ≤ C * ε ^ rA ∧ c * ε ^ rB ≤ pBA ε ∧ pBA ε ≤ C * ε ^ rB) :
    Tendsto (fun ε => pBA ε / (pAB ε + pBA ε)) (𝓝[>] 0) (𝓝 1) := by
  have hk : 0 < rA - rB := Nat.sub_pos_of_lt h
  -- `1 − weight = p_AB/(p_AB + p_BA) ≤ (C/c) ε^{rA − rB}`
  have hup : Tendsto (fun ε : ℝ => C / c * ε ^ (rA - rB)) (𝓝[>] 0) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have := (tendsto_const_nhds (x := C / c)).mul ((continuous_pow (rA - rB)).tendsto (0 : ℝ))
    simpa [zero_pow hk.ne'] using this
  have hsq : Tendsto (fun ε => pAB ε / (pAB ε + pBA ε)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hbd, self_mem_nhdsWithin] with ε hb hε
      obtain ⟨h1, _, h3, _⟩ := hb
      have hε' : (0 : ℝ) < ε := hε
      have : 0 < pBA ε := lt_of_lt_of_le (by positivity) h3
      have : 0 ≤ pAB ε := le_trans (by positivity) h1
      positivity
    · filter_upwards [hbd, self_mem_nhdsWithin] with ε hb hε
      obtain ⟨h1, h2, h3, _⟩ := hb
      have hε' : (0 : ℝ) < ε := hε
      have hB : 0 < pBA ε := lt_of_lt_of_le (by positivity) h3
      have hA : 0 ≤ pAB ε := le_trans (by positivity) h1
      have hpow : ε ^ rA = ε ^ rB * ε ^ (rA - rB) := by
        rw [← pow_add, Nat.add_sub_cancel' h.le]
      have hεB : 0 < ε ^ rB := by positivity
      rw [div_le_iff₀ (by positivity)]
      calc pAB ε ≤ C * ε ^ rA := h2
        _ = C / c * ε ^ (rA - rB) * (c * ε ^ rB) := by rw [hpow]; field_simp
        _ ≤ C / c * ε ^ (rA - rB) * (pAB ε + pBA ε) := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          have hp : 0 < ε ^ rA := by positivity
          have hC : 0 ≤ C := by nlinarith [h1.trans h2]
          positivity
  have e : ∀ᶠ ε in 𝓝[>] (0 : ℝ), pBA ε / (pAB ε + pBA ε) = 1 - pAB ε / (pAB ε + pBA ε) := by
    filter_upwards [hbd, self_mem_nhdsWithin] with ε hb hε
    obtain ⟨h1, _, h3, _⟩ := hb
    have hε' : (0 : ℝ) < ε := hε
    have hB : 0 < pBA ε := lt_of_lt_of_le (by positivity) h3
    have hA : 0 ≤ pAB ε := le_trans (by positivity) h1
    field_simp
    ring
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub hsq
  rw [sub_zero] at this
  exact this.congr' (e.mono fun _ h => h.symm)

/-- **KMR/Young with transition probabilities of order `ε^r`** (two-state
reduction): if `A` is risk dominant, then in every large enough population,
transition probabilities between conventions that are of order `ε` to the
basin radii select `A`. -/
theorem riskDominant_selected_of_bounds (G : Coord) (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ (pAB pBA : ℝ → ℝ) (c C : ℝ), 0 < c →
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε ^ G.resistA N ≤ pAB ε ∧ pAB ε ≤ C * ε ^ G.resistA N ∧
        c * ε ^ G.resistB N ≤ pBA ε ∧ pBA ε ≤ C * ε ^ G.resistB N) →
      Tendsto (fun ε => pBA ε / (pAB ε + pBA ε)) (𝓝[>] 0) (𝓝 1) :=
  (G.resistB_lt_resistA h).mono fun _ hN _ _ _ _ hc hbd => tendsto_weightA_of_bounds hN hc hbd

/-- Non-vacuity: a stag hunt where `A` is the safe action (`3` whatever the
opponent does) and `B` hunts the stag (`4` if the opponent does too, `0`
otherwise). Then `p* = 1/4`, so the safe action is risk dominant (although the
stag convention is payoff dominant) and is selected. -/
def stagHunt : Coord := ⟨3, 3, 0, 4, by norm_num, by norm_num⟩

theorem stagHunt_riskDominant : stagHunt.RiskDominant := by
  simp [Coord.RiskDominant, stagHunt]; norm_num

theorem stagHunt_pstar : stagHunt.pstar = 1 / 4 := by
  simp [Coord.pstar, stagHunt]; norm_num

theorem stagHunt_selected : ∀ᶠ N : ℕ in atTop,
    Tendsto (stationaryA (stagHunt.resistA N) (stagHunt.resistB N)) (𝓝[>] 0) (𝓝 1) :=
  riskDominant_selected_twoState stagHunt stagHunt_riskDominant

end StochasticStability

end Econ
