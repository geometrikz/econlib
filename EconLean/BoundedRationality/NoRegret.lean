/-
# No-regret learning and (coarse) correlated equilibrium

References. S. Hart and A. Mas-Colell (2000), "A Simple Adaptive Procedure
Leading to Correlated Equilibrium", *Econometrica* 68(5), §2 (the link
between regrets and the empirical distribution of play); H. Moulin and
J.-P. Vial (1978) for coarse correlated equilibrium; T. Roughgarden (2016),
*Twenty Lectures on Algorithmic Game Theory*, Lecture 17.

Players repeatedly play a finite game; `h : Fin T → (∀ j, S j)` is a history
of `T ≥ 1` pure profiles and `emp h` its empirical distribution.

* **External regret** of `i` for `t'`: the average gain from having always
  played `t'` instead. `extRegret_eq` shows it equals the coarse-correlated
  deviation gain of `emp h`; so all external regrets are `≤ ε` iff the
  empirical distribution is an `ε`-coarse correlated equilibrium
  (`isCCE_emp_iff`).
* **Internal (conditional, pairwise) regret** of `i` for `t → t'`: the average gain from
  playing `t'` in the periods `i` played `t`. It equals the obedience gain
  of `emp h` (`intRegret_eq`); so all internal regrets are `≤ ε` iff the
  empirical distribution is an `ε`-correlated equilibrium
  (`isCorrelatedEq_emp_iff`). (This is the pairwise condition, not swap
  regret `Σ_t max_{t'}`, which can be up to `|S i|` times larger.) This is the reduction behind Hart–Mas-Colell's
  theorem: regret matching makes internal regrets vanish, hence the
  empirical distributions converge to the set of correlated equilibria.
* `isCorrelatedEq_of_limit`: if the maximal internal regret along a sequence
  of histories tends to `0` and the empirical distributions converge, the
  limit is a correlated equilibrium (likewise `isCCE_of_limit`).
* `isCCE_of_isCorrelatedEq`: every correlated equilibrium is coarse
  correlated (the converse fails, e.g. uniform play on the off-diagonal of
  rock–paper–scissors; not formalized).

That regret matching does drive internal regrets to zero almost surely
(Blackwell approachability) is not formalized here.
-/
module

public import EconLean.Games.Correlated
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

noncomputable section

namespace Econ

namespace NoRegret

open Function Finset Filter Topology

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Gain to `i` from unilaterally switching to `t'` under the joint
distribution `μ` (no conditioning on the recommendation). -/
def cceGain (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I) (t' : S i) : ℝ :=
  ∑ s, μ s * (u i (update s i t') - u i s)

/-- `ε`-coarse correlated equilibrium. -/
def IsCCE (u : I → (∀ j, S j) → ℝ) (ε : ℝ) (μ : (∀ j, S j) → ℝ) : Prop :=
  μ ∈ lotteries (∀ j, S j) ∧ ∀ i (t' : S i), cceGain u μ i t' ≤ ε

/-- `ε`-correlated equilibrium. -/
def IsCE (u : I → (∀ j, S j) → ℝ) (ε : ℝ) (μ : (∀ j, S j) → ℝ) : Prop :=
  μ ∈ lotteries (∀ j, S j) ∧ ∀ i (t t' : S i), obedienceGain u μ i t t' ≤ ε

theorem isCE_zero_iff (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) :
    IsCE u 0 μ ↔ IsCorrelatedEq u μ := Iff.rfl

/-- The coarse gain is the sum of the obedience gains over recommendations. -/
theorem cceGain_eq_sum (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) (i : I) (t' : S i) :
    cceGain u μ i t' = ∑ t, obedienceGain u μ i t t' := by
  unfold cceGain obedienceGain
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_ite_eq]
  simp

/-- **Every correlated equilibrium is a coarse correlated equilibrium.** -/
theorem isCCE_of_isCorrelatedEq {u : I → (∀ j, S j) → ℝ} {μ : (∀ j, S j) → ℝ}
    (h : IsCorrelatedEq u μ) : IsCCE u 0 μ :=
  ⟨h.1, fun i t' => by
    rw [cceGain_eq_sum]; exact sum_nonpos fun t _ => h.2 i t t'⟩

/-! ### Histories and regrets -/

variable {T : ℕ}

/-- The empirical distribution of a history. -/
def emp (h : Fin T → ∀ j, S j) (s : ∀ j, S j) : ℝ :=
  ((univ.filter fun k => h k = s).card : ℝ) / T

/-- Average external regret of `i` for always playing `t'`. -/
def extRegret (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (i : I) (t' : S i) : ℝ :=
  (∑ k, (u i (update (h k) i t') - u i (h k))) / T

/-- Average internal regret of `i` for playing `t'` whenever it played `t`. -/
def intRegret (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (i : I) (t t' : S i) : ℝ :=
  (∑ k, if h k i = t then u i (update (h k) i t') - u i (h k) else 0) / T

/-- Sum over periods = sum over profiles weighted by frequency. -/
theorem sum_periods (h : Fin T → ∀ j, S j) (f : (∀ j, S j) → ℝ) :
    ∑ k, f (h k) = ∑ s, ((univ.filter fun k => h k = s).card : ℝ) * f s := by
  rw [← sum_fiberwise univ h (fun k => f (h k))]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], sum_const, nsmul_eq_mul]

theorem emp_mem (hT : 0 < T) (h : Fin T → ∀ j, S j) : emp h ∈ lotteries (∀ j, S j) := by
  refine ⟨fun s => by unfold emp; positivity, ?_⟩
  unfold emp
  rw [← sum_div, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun k _ => mem_univ (h k))]
  simp only [card_univ, Fintype.card_fin]
  have : (T : ℝ) ≠ 0 := by positivity
  field_simp

/-- **External regret = coarse deviation gain of the empirical distribution.** -/
theorem extRegret_eq (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (i : I) (t' : S i) :
    extRegret u h i t' = cceGain u (emp h) i t' := by
  unfold extRegret cceGain emp
  rw [sum_periods h (fun s => u i (update s i t') - u i s), sum_div]
  refine sum_congr rfl fun s _ => by ring

/-- **Internal regret = obedience gain of the empirical distribution.** -/
theorem intRegret_eq (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (i : I) (t t' : S i) :
    intRegret u h i t t' = obedienceGain u (emp h) i t t' := by
  unfold intRegret obedienceGain emp
  rw [sum_periods h (fun s => if s i = t then u i (update s i t') - u i s else 0), sum_div]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

/-- **No external regret ⇔ coarse correlated equilibrium.** -/
theorem isCCE_emp_iff (hT : 0 < T) (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (ε : ℝ) :
    IsCCE u ε (emp h) ↔ ∀ i (t' : S i), extRegret u h i t' ≤ ε := by
  simp only [IsCCE, emp_mem hT h, true_and, extRegret_eq]

/-- **No internal regret ⇔ correlated equilibrium.** -/
theorem isCorrelatedEq_emp_iff (hT : 0 < T) (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j)
    (ε : ℝ) : IsCE u ε (emp h) ↔ ∀ i (t t' : S i), intRegret u h i t t' ≤ ε := by
  simp only [IsCE, emp_mem hT h, true_and, intRegret_eq]

/-! ### Limits -/

theorem continuous_obedienceGain (u : I → (∀ j, S j) → ℝ) (i : I) (t t' : S i) :
    Continuous fun μ : (∀ j, S j) → ℝ => obedienceGain u μ i t t' := by
  unfold obedienceGain
  refine continuous_finsetSum _ fun s _ => ?_
  split_ifs
  · exact (continuous_apply s).mul continuous_const
  · exact continuous_const

omit [∀ i, DecidableEq (S i)] in
theorem continuous_cceGain (u : I → (∀ j, S j) → ℝ) (i : I) (t' : S i) :
    Continuous fun μ : (∀ j, S j) → ℝ => cceGain u μ i t' :=
  continuous_finsetSum _ fun s _ => (continuous_apply s).mul continuous_const

omit [∀ i, DecidableEq (S i)] in
theorem isClosed_lotteries : IsClosed (lotteries (∀ j, S j)) := by
  have h1 : IsClosed {L : (∀ j, S j) → ℝ | ∀ c, 0 ≤ L c} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)
  have h2 : IsClosed {L : (∀ j, S j) → ℝ | ∑ c, L c = 1} :=
    isClosed_eq (continuous_finsetSum _ fun c _ => continuous_apply c) continuous_const
  exact h1.inter h2

/-- **Vanishing internal regret ⇒ correlated equilibrium in the limit**
(Hart–Mas-Colell 2000, the deterministic step). Histories `h n` of lengths
`T n ≥ 1` whose maximal internal regrets are at most `ε n → 0`, with
converging empirical distributions, have a correlated equilibrium as limit. -/
theorem isCorrelatedEq_of_limit (u : I → (∀ j, S j) → ℝ) {Tn : ℕ → ℕ} (hT : ∀ n, 0 < Tn n)
    (h : ∀ n, Fin (Tn n) → ∀ j, S j) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hreg : ∀ n i (t t' : S i), intRegret u (h n) i t t' ≤ ε n) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => emp (h n)) atTop (𝓝 μ)) : IsCorrelatedEq u μ := by
  refine ⟨isClosed_lotteries.mem_of_tendsto hμ (Eventually.of_forall fun n => emp_mem (hT n) _),
    fun i t t' => ?_⟩
  have hc := ((continuous_obedienceGain u i t t').tendsto μ).comp hμ
  refine le_of_tendsto_of_tendsto hc hε (Eventually.of_forall fun n => ?_)
  simp only [comp_apply, ← intRegret_eq]
  exact hreg n i t t'

/-- **Vanishing external regret ⇒ coarse correlated equilibrium in the limit.** -/
theorem isCCE_of_limit (u : I → (∀ j, S j) → ℝ) {Tn : ℕ → ℕ} (hT : ∀ n, 0 < Tn n)
    (h : ∀ n, Fin (Tn n) → ∀ j, S j) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hreg : ∀ n i (t' : S i), extRegret u (h n) i t' ≤ ε n) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => emp (h n)) atTop (𝓝 μ)) : IsCCE u 0 μ := by
  refine ⟨isClosed_lotteries.mem_of_tendsto hμ (Eventually.of_forall fun n => emp_mem (hT n) _),
    fun i t' => ?_⟩
  have hc := ((continuous_cceGain u i t').tendsto μ).comp hμ
  refine le_of_tendsto_of_tendsto hc hε (Eventually.of_forall fun n => ?_)
  simp only [comp_apply, ← extRegret_eq]
  exact hreg n i t'

end NoRegret

end Econ
