/-
# KMR's simultaneous-revision ("Darwinian") chain

Reference. M. Kandori, G. Mailath and R. Rob (1993), "Learning, Mutation, and
Long Run Equilibria in Games", *Econometrica* 61(1), §3–4 (the Darwinian
dynamic with independent mutations, Theorem 3).

`N` players play the coordination game `G` of `StochasticStability.lean`
against the field. Each period **every** player switches to a best reply to
the current share `z/N` of `A` players (ties to `A`; payoffs against the
population share including oneself, as in `StochasticStability.lean`), so the
population jumps to all-`A` or all-`B` (KMR's best-response dynamic, the
extreme case of their Darwinian dynamics); then every player independently
mutates to the other action with probability `ε`. The number of `A` players
is a Markov chain on `{0, …, N}` (`darwin`) with binomial transitions:
from the all-`A` target, `z'` players end on `A` with probability
`C(N, z') ε^{N−z'} (1−ε)^{z'}` (`mutProb`).

**Results.**
* `darwin_isStochastic`, `darwin_exists_invariant`: for `ε ∈ [0, 1]` the
  matrix is stochastic and has a stationary distribution.
* `flux_cut`: for any stationary distribution and any set `S` of states,
  the probability flow from `S` to its complement equals the flow back.
* `darwin_last_ge` (the key bound): if `2 m ≤ N`, where `m = resistB N` is
  the number of `A` players needed to make `A` a best reply, then every
  stationary distribution puts probability at least
  `(1 − ε)^N − 2^N ε^{N + 1 − 2m}` on all-`A`. Leaving the `A` basin takes
  `N + 1 − m` mutations, entering it from the `B` basin takes `m`.
* `darwin_selects` (**KMR Theorem 3**, best-response special case): if `A` is risk dominant, then in every
  large enough population the stationary probability of all-`A` tends to `1`
  as `ε → 0`, and that of every other state to `0`
  (`darwin_tendsto_zero`). No tree formula is needed: the cut-flow identity
  for the two basins suffices.
* `stagHunt_darwin`: the stag hunt's risk-dominant (safe) convention is
  selected.

Only the best-response dynamic is treated (KMR allow any Darwinian dynamic
that moves toward the best reply), and only selection of `A` when `A` is
risk dominant is stated (the case of `B` is analogous, but with ties broken
toward `A` the resistances differ by one, so it needs strict risk
dominance of `B`). The stag hunt's `A` is the safe (risk-dominant) action.
-/
module

public import EconLean.BoundedRationality.KMRChain
public import EconLean.Macro.DP.MarkovChain

@[expose] public section

noncomputable section

namespace Econ

namespace StochasticStability

open Finset Filter Topology Matrix

/-! ### Cut flows of stationary distributions -/

section Flux

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- **Cut-flow identity**: under a stationary distribution, the flow out of a
set of states equals the flow into it. -/
theorem flux_cut {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) {μ : Z → ℝ} (hμ : IsInvariant Q μ)
    (S : Finset Z) :
    ∑ x ∈ S, ∑ y ∈ Sᶜ, μ x * Q x y = ∑ y ∈ Sᶜ, ∑ x ∈ S, μ y * Q y x := by
  have hinv : ∀ y, ∑ z, μ z * Q z y = μ y := fun y => by
    have := congrFun hμ.2 y
    rwa [vecMul_apply'] at this
  -- total mass of `Sᶜ`, computed two ways
  have h1 : ∑ y ∈ Sᶜ, μ y = ∑ y ∈ Sᶜ, (∑ x ∈ S, μ x * Q x y + ∑ y' ∈ Sᶜ, μ y' * Q y' y) := by
    refine sum_congr rfl fun y _ => ?_
    rw [← hinv y, ← sum_add_sum_compl S]
  have h2 : ∑ y ∈ Sᶜ, μ y = ∑ y ∈ Sᶜ, (∑ x ∈ S, μ y * Q y x + ∑ y' ∈ Sᶜ, μ y * Q y y') := by
    refine sum_congr rfl fun y _ => ?_
    rw [← mul_sum, ← mul_sum, ← mul_add, sum_add_sum_compl S, hQ.2 y, mul_one]
  rw [sum_add_distrib] at h1 h2
  have h3 : ∑ y ∈ Sᶜ, ∑ y' ∈ Sᶜ, μ y' * Q y' y = ∑ y ∈ Sᶜ, ∑ y' ∈ Sᶜ, μ y * Q y y' := sum_comm
  rw [sum_comm] at h1
  linarith

end Flux

namespace Coord

variable (G : Coord)

/-! ### The chain -/

/-- Mutation probabilities: from the all-`A` target (`allA`) or the all-`B`
target, the probability that `z'` players end up on `A`. -/
def mutProb (N : ℕ) (ε : ℝ) (allA : Prop) [Decidable allA] (z' : Fin (N + 1)) : ℝ :=
  (N.choose z') * if allA then ε ^ (N - z') * (1 - ε) ^ (z' : ℕ) else ε ^ (z' : ℕ) * (1 - ε) ^ (N - z')

/-- **KMR's chain**: best response by everybody, then independent mutations. -/
def darwin (N : ℕ) (ε : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun z z' =>
  open Classical in mutProb N ε (G.pstar ≤ (z : ℝ) / N) z'

theorem sum_binom (N : ℕ) (x y : ℝ) :
    ∑ z' : Fin (N + 1), (N.choose z' : ℝ) * (x ^ (z' : ℕ) * y ^ (N - z')) = (x + y) ^ N := by
  rw [add_pow, Fin.sum_univ_eq_sum_range (fun m => (N.choose m : ℝ) * (x ^ m * y ^ (N - m)))]
  exact sum_congr rfl fun m _ => by ring

theorem darwin_isStochastic (N : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsStochastic (G.darwin N ε) := by
  classical
  have h1' : 0 ≤ 1 - ε := by linarith
  refine ⟨fun z z' => ?_, fun z => ?_⟩
  · unfold darwin mutProb; split_ifs <;> positivity
  · unfold darwin mutProb
    split_ifs
    · have := sum_binom N (1 - ε) ε
      rw [show (1 - ε) + ε = 1 by ring, one_pow] at this
      exact (sum_congr rfl fun z' _ => by ring).trans this
    · have := sum_binom N ε (1 - ε)
      rw [show ε + (1 - ε) = 1 by ring, one_pow] at this
      exact this

/-- Non-vacuity: the chain has a stationary distribution. -/
theorem darwin_exists_invariant (N : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ μ, IsInvariant (G.darwin N ε) μ :=
  exists_invariant (G.darwin_isStochastic N h0 h1)

/-! ### The basin bound -/

/-- The basin of the `A` convention: states where `A` is a best reply. -/
def basinA (N : ℕ) : Finset (Fin (N + 1)) := by
  classical exact univ.filter fun z => G.pstar ≤ (z : ℝ) / N

theorem lt_resistB_of_not_mem {N : ℕ} (hN : 0 < N) {y : Fin (N + 1)} (hy : y ∉ G.basinA N) :
    (y : ℕ) < G.resistB N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [basinA, mem_filter, mem_univ, true_and, not_le] at hy
  rw [div_lt_iff₀ hN'] at hy
  exact Nat.lt_ceil.2 (by linarith)

theorem resistB_le {N : ℕ} (hN : 0 < N) : G.resistB N ≤ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine Nat.ceil_le.2 ?_
  have := G.pstar_lt_one
  nlinarith

theorem mem_basinA_iff {N : ℕ} (z : Fin (N + 1)) :
    z ∈ G.basinA N ↔ G.pstar ≤ (z : ℝ) / N := by
  simp [basinA]

theorem last_mem_basinA {N : ℕ} (hN : 0 < N) : Fin.last N ∈ G.basinA N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mem_basinA_iff G, Fin.val_last, div_self hN'.ne']
  exact G.pstar_lt_one.le

theorem resistB_mem_basinA {N : ℕ} (hN : 0 < N) :
    (⟨G.resistB N, Nat.lt_succ_of_le (G.resistB_le hN)⟩ : Fin (N + 1)) ∈ G.basinA N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mem_basinA_iff G, le_div_iff₀ hN', mul_comm]
  exact Nat.le_ceil _

/-- **The key bound**: all-`A` has stationary probability at least
`(1 − ε)^N − 2^N ε^{N + 1 − 2m}`. -/
theorem darwin_last_ge {N : ℕ} (hN : 0 < N) (hm : 2 * G.resistB N ≤ N) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1) {μ : Fin (N + 1) → ℝ} (hμ : IsInvariant (G.darwin N ε) μ) :
    (1 - ε) ^ N - 2 ^ N * ε ^ (N + 1 - 2 * G.resistB N) ≤ μ (Fin.last N) := by
  classical
  set m := G.resistB N
  set S := G.basinA N
  have hQ := G.darwin_isStochastic N h0.le h1.le
  have hμ0 : ∀ z, 0 ≤ μ z := hμ.1.1
  have hμ1 : ∑ z, μ z = 1 := hμ.1.2
  have h1' : 0 < 1 - ε := by linarith
  have hS : ∀ x ∈ S, G.darwin N ε x = fun z' : Fin (N + 1) => (N.choose z' : ℝ) *
      (ε ^ (N - z') * (1 - ε) ^ (z' : ℕ)) := fun x hx => by
    funext z'
    have := (G.mem_basinA_iff x).1 hx
    simp only [darwin, mutProb, this, ite_true]
  have hSc : ∀ y ∈ Sᶜ, G.darwin N ε y = fun z' : Fin (N + 1) => (N.choose z' : ℝ) *
      (ε ^ (z' : ℕ) * (1 - ε) ^ (N - z')) := fun y hy => by
    funext z'
    have : ¬ G.pstar ≤ (y : ℝ) / N := fun h =>
      (mem_compl.1 hy) ((G.mem_basinA_iff y).2 h)
    simp only [darwin, mutProb, this, ite_false]
  -- flow out of the `A` basin
  have hout : ∑ x ∈ S, ∑ y ∈ Sᶜ, μ x * G.darwin N ε x y ≤ 2 ^ N * ε ^ (N + 1 - m) := by
    have hrow : ∀ x ∈ S, ∑ y ∈ Sᶜ, G.darwin N ε x y ≤ 2 ^ N * ε ^ (N + 1 - m) := by
      intro x hx
      rw [hS x hx]
      calc ∑ y ∈ Sᶜ, (N.choose y : ℝ) * (ε ^ (N - y) * (1 - ε) ^ (y : ℕ))
          ≤ ∑ y ∈ Sᶜ, (N.choose y : ℝ) * ε ^ (N + 1 - m) := by
            refine sum_le_sum fun y hy => mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hy' := G.lt_resistB_of_not_mem hN (mem_compl.1 hy)
            have e1 : ε ^ (N - y) ≤ ε ^ (N + 1 - m) :=
              pow_le_pow_of_le_one h0.le h1.le (by omega)
            have e2 : (1 - ε) ^ (y : ℕ) ≤ 1 := pow_le_one₀ h1'.le (by linarith)
            calc ε ^ (N - y) * (1 - ε) ^ (y : ℕ) ≤ ε ^ (N - y) * 1 :=
                  mul_le_mul_of_nonneg_left e2 (by positivity)
              _ ≤ _ := by rw [mul_one]; exact e1
        _ ≤ ∑ y : Fin (N + 1), (N.choose y : ℝ) * ε ^ (N + 1 - m) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
        _ = 2 ^ N * ε ^ (N + 1 - m) := by
            rw [← sum_mul]
            congr 1
            have := sum_binom N 1 1
            simp only [one_pow, mul_one] at this
            rw [this]; norm_num
    calc ∑ x ∈ S, ∑ y ∈ Sᶜ, μ x * G.darwin N ε x y
        = ∑ x ∈ S, μ x * ∑ y ∈ Sᶜ, G.darwin N ε x y := by simp only [mul_sum]
      _ ≤ ∑ x ∈ S, μ x * (2 ^ N * ε ^ (N + 1 - m)) :=
          sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hrow x hx) (hμ0 x)
      _ ≤ ∑ x, μ x * (2 ^ N * ε ^ (N + 1 - m)) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
            mul_nonneg (hμ0 x) (by positivity)
      _ = 2 ^ N * ε ^ (N + 1 - m) := by rw [← sum_mul, hμ1, one_mul]
  -- flow into the `A` basin
  set zm : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le (G.resistB_le hN)⟩
  have hzm : zm ∈ S := G.resistB_mem_basinA hN
  have hin : (∑ y ∈ Sᶜ, μ y) * (ε ^ m * (1 - ε) ^ N) ≤
      ∑ y ∈ Sᶜ, ∑ x ∈ S, μ y * G.darwin N ε y x := by
    rw [sum_mul]
    refine sum_le_sum fun y hy => ?_
    have hP : ε ^ m * (1 - ε) ^ N ≤ G.darwin N ε y zm := by
      rw [hSc y hy]
      have hc : (1 : ℝ) ≤ N.choose m := by exact_mod_cast Nat.choose_pos (G.resistB_le hN)
      have hp : (1 - ε) ^ N ≤ (1 - ε) ^ (N - m) :=
        pow_le_pow_of_le_one h1'.le (by linarith) (Nat.sub_le N m)
      show ε ^ m * (1 - ε) ^ N ≤ (N.choose m : ℝ) * (ε ^ m * (1 - ε) ^ (N - m))
      have : ε ^ m * (1 - ε) ^ N ≤ ε ^ m * (1 - ε) ^ (N - m) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      nlinarith [mul_nonneg (pow_nonneg h0.le m) (pow_nonneg h1'.le (N - m))]
    calc μ y * (ε ^ m * (1 - ε) ^ N) ≤ μ y * G.darwin N ε y zm :=
          mul_le_mul_of_nonneg_left hP (hμ0 y)
      _ ≤ ∑ x ∈ S, μ y * G.darwin N ε y x :=
          single_le_sum (f := fun x => μ y * G.darwin N ε y x)
            (fun x _ => mul_nonneg (hμ0 y) (hQ.1 y x)) hzm
  have hflux := flux_cut hQ hμ S
  -- mass of the `B` basin
  have hB : (∑ y ∈ Sᶜ, μ y) * (ε ^ m * (1 - ε) ^ N) ≤ 2 ^ N * ε ^ (N + 1 - m) := by
    linarith
  have hpow : ε ^ (N + 1 - m) = ε ^ m * ε ^ (N + 1 - 2 * m) := by
    rw [← pow_add]; congr 1; omega
  have hεm : 0 < ε ^ m := by positivity
  have hB' : (∑ y ∈ Sᶜ, μ y) * (1 - ε) ^ N ≤ 2 ^ N * ε ^ (N + 1 - 2 * m) := by
    rw [hpow] at hB
    have : ε ^ m * ((∑ y ∈ Sᶜ, μ y) * (1 - ε) ^ N) ≤ ε ^ m * (2 ^ N * ε ^ (N + 1 - 2 * m)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hεm
  -- inflow to all-`A`
  have hlast : (∑ x ∈ S, μ x) * (1 - ε) ^ N ≤ μ (Fin.last N) := by
    have hinv := congrFun hμ.2 (Fin.last N)
    rw [vecMul_apply'] at hinv
    rw [← hinv, sum_mul]
    calc ∑ x ∈ S, μ x * (1 - ε) ^ N = ∑ x ∈ S, μ x * G.darwin N ε x (Fin.last N) := by
          refine sum_congr rfl fun x hx => ?_
          rw [hS x hx]; simp
      _ ≤ ∑ x, μ x * G.darwin N ε x (Fin.last N) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
            mul_nonneg (hμ0 x) (hQ.1 x _)
  have hsplit : ∑ x ∈ S, μ x = 1 - ∑ y ∈ Sᶜ, μ y := by
    rw [← hμ1, ← sum_add_sum_compl S]; ring
  rw [hsplit] at hlast
  nlinarith

/-- **KMR Theorem 3 (Darwinian chain)**: if `A` is risk dominant, then in every
large enough population the stationary probability of all-`A` tends to `1` as
the mutation rate vanishes. -/
theorem darwin_selects (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → Fin (N + 1) → ℝ,
      (∀ ε, 0 < ε → ε < 1 → IsInvariant (G.darwin N ε) (μ ε)) →
      Tendsto (fun ε => μ ε (Fin.last N)) (𝓝[>] 0) (𝓝 1) := by
  rw [riskDominant_iff] at h
  have hgap : 0 < 1 - 2 * G.pstar := by linarith
  filter_upwards [eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / (1 - 2 * G.pstar))] with N hN hNb
  intro μ hμ
  have hm : 2 * G.resistB N < N := by
    have hc : (G.resistB N : ℝ) < N * G.pstar + 1 :=
      Nat.ceil_lt_add_one (by have := G.pstar_pos; positivity)
    have : 2 ≤ (N : ℝ) * (1 - 2 * G.pstar) := by rwa [div_le_iff₀ hgap] at hNb
    have : (2 * G.resistB N : ℝ) < N := by linarith
    exact_mod_cast this
  set k := N + 1 - 2 * G.resistB N
  have hk : 0 < k := by omega
  have hlo : Tendsto (fun ε : ℝ => (1 - ε) ^ N - 2 ^ N * ε ^ k) (𝓝[>] 0) (𝓝 1) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have hc : Continuous fun ε : ℝ => (1 - ε) ^ N - 2 ^ N * ε ^ k := by fun_prop
    have := hc.tendsto 0
    simpa [zero_pow hk.ne'] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact G.darwin_last_ge hN hm.le hε.1 hε.2 (hμ ε hε.1 hε.2)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hd := (hμ ε hε.1 hε.2).1
    rw [← hd.2]
    exact single_le_sum (fun z _ => hd.1 z) (mem_univ _)

/-- Every other state has vanishing stationary probability. -/
theorem darwin_tendsto_zero (h : G.RiskDominant) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → Fin (N + 1) → ℝ,
      (∀ ε, 0 < ε → ε < 1 → IsInvariant (G.darwin N ε) (μ ε)) →
      ∀ z ≠ Fin.last N, Tendsto (fun ε => μ ε z) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [G.darwin_selects h] with N hN μ hμ z hz
  have h1 := hN μ hμ
  have hup : Tendsto (fun ε => 1 - μ ε (Fin.last N)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (hμ ε hε.1 hε.2).1.1 z
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hd := (hμ ε hε.1 hε.2).1
    have : μ ε z + μ ε (Fin.last N) ≤ ∑ z', μ ε z' := by
      rw [← sum_pair hz]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z' _ _ => hd.1 z'
    rw [hd.2] at this
    linarith

end Coord

/-- Non-vacuity: in the stag hunt the safe convention is selected by KMR's
chain. -/
theorem stagHunt_darwin : ∀ᶠ N : ℕ in atTop, ∀ μ : ℝ → Fin (N + 1) → ℝ,
    (∀ ε, 0 < ε → ε < 1 → IsInvariant (stagHunt.darwin N ε) (μ ε)) →
    Tendsto (fun ε => μ ε (Fin.last N)) (𝓝[>] 0) (𝓝 1) :=
  stagHunt.darwin_selects stagHunt_riskDominant

end StochasticStability

end Econ
