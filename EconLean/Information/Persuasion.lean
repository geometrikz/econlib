/-
# Bayesian persuasion

Reference: E. Kamenica and M. Gentzkow (2011), "Bayesian Persuasion",
*AER* 101(6): 2590–2615 (KG).

**Setting.** Finitely many states `Ω`, common prior `μ₀ ∈ Δ(Ω)`. The sender
commits to a signal `π : Ω → Δ(M)` (finite `M`). After message `m` the
receiver holds the posterior `μ_m` and acts; the sender's payoff depends only
on the posterior, through an arbitrary function `v̂ : Δ(Ω) → ℝ` (KG's
`v̂(μ) = E_μ v(â(μ), ω)`, with the receiver's tie-breaking built in).

**Bayes plausibility (KG Prop. 1).** The posteriors of any signal average back
to the prior (`signal_mean`), so every signal gives a *splitting* of `μ₀`: a
finite distribution `τ` over beliefs `ν k` with `Σ τ_k ν_k = μ₀`
(`Signal.toSplitting`, which preserves the sender's value). Conversely every
splitting is induced by some signal with the same value (`Splitting.toSignal`).

**Concavification (KG Cor. 1–2).** The best value over splittings,
`V μ₀ = sup Σ τ_k v̂(ν_k)`, is the concave closure of `v̂`: it lies above `v̂`
(`le_V`), is concave (`V_concave`), and lies below every concave function above
`v̂` (`V_le_of_concave`). The sender benefits from persuasion iff
`V μ₀ > v̂ μ₀` (`benefits_iff`). `v̂` is assumed bounded above on `Δ(Ω)` so the
sup is finite.

**Example (KG §2, the prosecutor).** Two states (innocent, guilty), prior
`P(guilty) = 3/10`; the judge convicts iff `P(guilty) ≥ 1/2`; the prosecutor
wants conviction. Without information the judge acquits (`v̂ μ₀ = 0`); the
optimal value is `3/5` (`prosecutor_V`), attained by a signal that sends
"guilty" always when guilty and with probability `3/7` when innocent
(`prosecutor_signal`).

Existence of an optimal signal attaining `V` when `v̂` is upper
semicontinuous is in `PersuasionExistence.lean` (with `|Ω| + 2` messages).
**Not formalized.** The receiver's problem is not modelled: `v̂` is taken as
given. KG's sharper bound of `|Ω|` messages.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace Econ

namespace Persuasion

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Beliefs: the probability simplex `Δ(Ω)`. -/
def beliefs (Ω : Type*) [Fintype Ω] : Set (Ω → ℝ) := {μ | (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1}

/-! ### Signals and posteriors -/

/-- A signal: for each state a probability over messages. -/
structure Signal (Ω M : Type*) [Fintype M] where
  /-- `π ω m`: probability of message `m` in state `ω` -/
  π : Ω → M → ℝ
  nonneg : ∀ ω m, 0 ≤ π ω m
  sum_one : ∀ ω, ∑ m, π ω m = 1

variable {M : Type*} [Fintype M]

/-- Unconditional probability of message `m`. -/
def msgProb (μ₀ : Ω → ℝ) (σ : Signal Ω M) (m : M) : ℝ := ∑ ω, μ₀ ω * σ.π ω m

/-- Posterior after `m` (Bayes' rule; the prior after a null message). -/
noncomputable def post (μ₀ : Ω → ℝ) (σ : Signal Ω M) (m : M) : Ω → ℝ := fun ω =>
  if msgProb μ₀ σ m = 0 then μ₀ ω else μ₀ ω * σ.π ω m / msgProb μ₀ σ m

/-- Sender's expected value from a signal. -/
noncomputable def signalValue (v : (Ω → ℝ) → ℝ) (μ₀ : Ω → ℝ) (σ : Signal Ω M) : ℝ :=
  ∑ m, msgProb μ₀ σ m * v (post μ₀ σ m)

theorem msgProb_nonneg {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) (m : M) :
    0 ≤ msgProb μ₀ σ m :=
  sum_nonneg fun ω _ => mul_nonneg (h₀.1 ω) (σ.nonneg ω m)

theorem sum_msgProb {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) :
    ∑ m, msgProb μ₀ σ m = 1 := by
  simp only [msgProb]
  rw [sum_comm]
  simp_rw [← mul_sum, σ.sum_one, mul_one]
  exact h₀.2

theorem joint_eq_zero {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) {m : M}
    (hm : msgProb μ₀ σ m = 0) (ω : Ω) : μ₀ ω * σ.π ω m = 0 :=
  (sum_eq_zero_iff_of_nonneg fun ω _ => mul_nonneg (h₀.1 ω) (σ.nonneg ω m)).1 hm ω (mem_univ ω)

theorem post_mem {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) (m : M) :
    post μ₀ σ m ∈ beliefs Ω := by
  by_cases hm : msgProb μ₀ σ m = 0
  · have e : post μ₀ σ m = μ₀ := funext fun ω => by simp [post, hm]
    rw [e]; exact h₀
  · have hpos : 0 < msgProb μ₀ σ m := lt_of_le_of_ne (msgProb_nonneg h₀ σ m) (Ne.symm hm)
    refine ⟨fun ω => ?_, ?_⟩
    · simp only [post, hm, ite_false]
      exact div_nonneg (mul_nonneg (h₀.1 ω) (σ.nonneg ω m)) hpos.le
    · simp only [post, hm, ite_false, ← sum_div]
      exact div_self hm

/-- **Bayes plausibility**: posteriors average back to the prior. -/
theorem signal_mean {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) (ω : Ω) :
    ∑ m, msgProb μ₀ σ m * post μ₀ σ m ω = μ₀ ω := by
  have : ∀ m, msgProb μ₀ σ m * post μ₀ σ m ω = μ₀ ω * σ.π ω m := by
    intro m
    by_cases hm : msgProb μ₀ σ m = 0
    · rw [hm, zero_mul, joint_eq_zero h₀ σ hm ω]
    · simp only [post, hm, ite_false]
      field_simp
  simp_rw [this, ← mul_sum, σ.sum_one, mul_one]

/-! ### Splittings -/

/-- A splitting of `μ₀`: a finite Bayes-plausible distribution of posteriors. -/
structure Splitting (μ₀ : Ω → ℝ) where
  /-- number of posteriors -/
  K : ℕ
  /-- weights -/
  τ : Fin K → ℝ
  /-- posteriors -/
  ν : Fin K → Ω → ℝ
  τ_nonneg : ∀ k, 0 ≤ τ k
  τ_sum : ∑ k, τ k = 1
  ν_mem : ∀ k, ν k ∈ beliefs Ω
  mean : ∀ ω, ∑ k, τ k * ν k ω = μ₀ ω

/-- Sender's value of a splitting. -/
noncomputable def Splitting.value {μ₀ : Ω → ℝ} (s : Splitting μ₀) (v : (Ω → ℝ) → ℝ) : ℝ :=
  ∑ k, s.τ k * v (s.ν k)

/-- The splitting induced by a signal. -/
noncomputable def Signal.toSplitting {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M) :
    Splitting μ₀ where
  K := Fintype.card M
  τ k := msgProb μ₀ σ ((Fintype.equivFin M).symm k)
  ν k := post μ₀ σ ((Fintype.equivFin M).symm k)
  τ_nonneg k := msgProb_nonneg h₀ σ _
  τ_sum := by
    rw [← sum_msgProb h₀ σ]
    exact Equiv.sum_comp (Fintype.equivFin M).symm (msgProb μ₀ σ)
  ν_mem k := post_mem h₀ σ _
  mean ω := by
    rw [← signal_mean h₀ σ ω]
    exact Equiv.sum_comp (Fintype.equivFin M).symm (fun m => msgProb μ₀ σ m * post μ₀ σ m ω)

theorem Signal.value_toSplitting {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) (σ : Signal Ω M)
    (v : (Ω → ℝ) → ℝ) : (σ.toSplitting h₀).value v = signalValue v μ₀ σ :=
  Equiv.sum_comp (Fintype.equivFin M).symm (fun m => msgProb μ₀ σ m * v (post μ₀ σ m))

theorem Splitting.ν_zero {μ₀ : Ω → ℝ} (s : Splitting μ₀) {k : Fin s.K} (hk : 0 < s.τ k)
    {ω : Ω} (h : μ₀ ω = 0) : s.ν k ω = 0 := by
  have hle : s.τ k * s.ν k ω ≤ μ₀ ω := by
    rw [← s.mean ω]
    exact single_le_sum (f := fun j => s.τ j * s.ν j ω)
      (fun j _ => mul_nonneg (s.τ_nonneg j) ((s.ν_mem j).1 ω)) (mem_univ k)
  rw [h] at hle
  have := mul_nonneg hk.le ((s.ν_mem k).1 ω)
  have h2 : s.τ k * s.ν k ω = 0 := le_antisymm hle this
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · exact h3

/-- The signal inducing a splitting: message `k` with probability
`τ_k ν_k(ω) / μ₀(ω)` (any distribution, here `τ`, in null states). -/
noncomputable def Splitting.toSignal {μ₀ : Ω → ℝ} (s : Splitting μ₀) : Signal Ω (Fin s.K) where
  π ω k := if μ₀ ω = 0 then s.τ k else s.τ k * s.ν k ω / μ₀ ω
  nonneg ω k := by
    split_ifs with h
    · exact s.τ_nonneg k
    · have : 0 ≤ μ₀ ω := by
        rw [← s.mean ω]
        exact sum_nonneg fun j _ => mul_nonneg (s.τ_nonneg j) ((s.ν_mem j).1 ω)
      exact div_nonneg (mul_nonneg (s.τ_nonneg k) ((s.ν_mem k).1 ω)) this
  sum_one ω := by
    split_ifs with h
    · exact s.τ_sum
    · rw [← sum_div, s.mean ω, div_self h]

theorem Splitting.joint {μ₀ : Ω → ℝ} (s : Splitting μ₀) (k : Fin s.K) (ω : Ω) :
    μ₀ ω * s.toSignal.π ω k = s.τ k * s.ν k ω := by
  simp only [Splitting.toSignal]
  split_ifs with h
  · rw [h, zero_mul]
    rcases (s.τ_nonneg k).lt_or_eq with hk | hk
    · rw [s.ν_zero hk h, mul_zero]
    · rw [← hk, zero_mul]
  · field_simp

theorem Splitting.msgProb_toSignal {μ₀ : Ω → ℝ} (s : Splitting μ₀) (k : Fin s.K) :
    msgProb μ₀ s.toSignal k = s.τ k := by
  simp only [msgProb, s.joint, ← mul_sum, (s.ν_mem k).2, mul_one]

/-- **KG Proposition 1 (converse half).** Every splitting is induced by a
signal with the same value. -/
theorem Splitting.value_toSignal {μ₀ : Ω → ℝ} (s : Splitting μ₀) (v : (Ω → ℝ) → ℝ) :
    signalValue v μ₀ s.toSignal = s.value v := by
  refine sum_congr rfl fun k _ => ?_
  rw [s.msgProb_toSignal]
  rcases (s.τ_nonneg k).lt_or_eq with hk | hk
  · congr 2
    funext ω
    simp only [post, s.msgProb_toSignal, hk.ne', ite_false, s.joint]
    field_simp
  · rw [← hk, zero_mul, zero_mul]

/-! ### Concavification -/

/-- The trivial splitting (no information). -/
def trivialSplitting {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) : Splitting μ₀ where
  K := 1
  τ _ := 1
  ν _ := μ₀
  τ_nonneg _ := zero_le_one
  τ_sum := by simp
  ν_mem _ := h₀
  mean ω := by simp

/-- The value of optimal persuasion. -/
noncomputable def V (v : (Ω → ℝ) → ℝ) (μ₀ : Ω → ℝ) : ℝ :=
  sSup (Set.range fun s : Splitting μ₀ => s.value v)

variable {v : (Ω → ℝ) → ℝ} {B : ℝ}

theorem value_le (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) {μ₀ : Ω → ℝ} (s : Splitting μ₀) :
    s.value v ≤ B := by
  calc s.value v ≤ ∑ k, s.τ k * B :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hB _ (s.ν_mem k)) (s.τ_nonneg k)
    _ = B := by rw [← sum_mul, s.τ_sum, one_mul]

theorem bddAbove (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) (μ₀ : Ω → ℝ) :
    BddAbove (Set.range fun s : Splitting μ₀ => s.value v) :=
  ⟨B, by rintro _ ⟨s, rfl⟩; exact value_le hB s⟩

theorem value_le_V (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) {μ₀ : Ω → ℝ} (s : Splitting μ₀) :
    s.value v ≤ V v μ₀ :=
  le_csSup (bddAbove hB μ₀) ⟨s, rfl⟩

/-- `V` lies above `v̂`. -/
theorem le_V (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    v μ₀ ≤ V v μ₀ := by
  have := value_le_V hB (trivialSplitting h₀)
  have e : (trivialSplitting h₀).value v = v μ₀ := by
    change ∑ _k : Fin 1, (1 : ℝ) * v μ₀ = v μ₀
    simp
  rwa [e] at this

/-- `V` lies below every concave function above `v̂` (Jensen). -/
theorem V_le_of_concave {g : (Ω → ℝ) → ℝ} (hg : ConcaveOn ℝ (beliefs Ω) g)
    (hvg : ∀ μ ∈ beliefs Ω, v μ ≤ g μ) {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    V v μ₀ ≤ g μ₀ := by
  refine csSup_le ⟨_, trivialSplitting h₀, rfl⟩ ?_
  rintro _ ⟨s, rfl⟩
  have hJ := hg.le_map_sum (t := univ) (w := s.τ) (p := s.ν) (fun k _ => s.τ_nonneg k) s.τ_sum
    (fun k _ => s.ν_mem k)
  have hmean : ∑ k, s.τ k • s.ν k = μ₀ := by
    funext ω; simp [Finset.sum_apply, s.mean ω]
  rw [hmean] at hJ
  calc s.value v ≤ ∑ k, s.τ k • g (s.ν k) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hvg _ (s.ν_mem k)) (s.τ_nonneg k)
    _ ≤ g μ₀ := hJ

theorem convex_beliefs : Convex ℝ (beliefs Ω) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun s => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 s)) (mul_nonneg hb (hq.1 s))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.2, hq.2]
    linarith

/-- Mixing two splittings. -/
def Splitting.mix {μ₁ μ₂ : Ω → ℝ} (s₁ : Splitting μ₁) (s₂ : Splitting μ₂) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : Splitting (a • μ₁ + b • μ₂) where
  K := s₁.K + s₂.K
  τ := Fin.append (fun k => a * s₁.τ k) (fun k => b * s₂.τ k)
  ν := Fin.append s₁.ν s₂.ν
  τ_nonneg k := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact mul_nonneg ha (s₁.τ_nonneg k)
    · rw [Fin.append_right]; exact mul_nonneg hb (s₂.τ_nonneg k)
  τ_sum := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← mul_sum, s₁.τ_sum, s₂.τ_sum]
    linarith
  ν_mem k := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact s₁.ν_mem k
    · rw [Fin.append_right]; exact s₂.ν_mem k
  mean ω := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, mul_assoc, ← mul_sum, s₁.mean, s₂.mean,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem Splitting.value_mix {μ₁ μ₂ : Ω → ℝ} (s₁ : Splitting μ₁) (s₂ : Splitting μ₂) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (s₁.mix s₂ ha hb hab).value v = a * s₁.value v + b * s₂.value v := by
  simp only [Splitting.value, Splitting.mix]
  change ∑ k : Fin (s₁.K + s₂.K), Fin.append (fun k => a * s₁.τ k) (fun k => b * s₂.τ k) k *
    v (Fin.append s₁.ν s₂.ν k) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, mul_assoc, ← mul_sum]

/-- `V` is concave. -/
theorem V_concave (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) : ConcaveOn ℝ (beliefs Ω) (V v) := by
  refine ⟨convex_beliefs, fun μ₁ h₁ μ₂ h₂ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set W := V v (a • μ₁ + b • μ₂)
  have key : ∀ (s₁ : Splitting μ₁) (s₂ : Splitting μ₂),
      a * s₁.value v + b * s₂.value v ≤ W := fun s₁ s₂ => by
    rw [← Splitting.value_mix s₁ s₂ ha hb hab]
    exact value_le_V hB _
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · -- sup over `s₁`, then over `s₂`
      have h2 : ∀ s₂ : Splitting μ₂, a * V v μ₁ + b * s₂.value v ≤ W := by
        intro s₂
        have : V v μ₁ ≤ (W - b * s₂.value v) / a := by
          refine csSup_le ⟨_, trivialSplitting h₁, rfl⟩ ?_
          rintro _ ⟨s₁, rfl⟩
          rw [le_div_iff₀ ha']
          linarith [key s₁ s₂]
        rw [le_div_iff₀ ha'] at this
        linarith
      have : V v μ₂ ≤ (W - a * V v μ₁) / b := by
        refine csSup_le ⟨_, trivialSplitting h₂, rfl⟩ ?_
        rintro _ ⟨s₂, rfl⟩
        rw [le_div_iff₀ hb']
        linarith [h2 s₂]
      rw [le_div_iff₀ hb'] at this
      linarith
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simp [W]
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simp [W]

/-- **KG Corollary 2.** The sender benefits from persuasion (some signal beats
no information) iff `V μ₀ > v̂ μ₀`. -/
theorem benefits_iff (hB : ∀ μ ∈ beliefs Ω, v μ ≤ B) {μ₀ : Ω → ℝ} (h₀ : μ₀ ∈ beliefs Ω) :
    (∃ K, ∃ σ : Signal Ω (Fin K), v μ₀ < signalValue v μ₀ σ) ↔ v μ₀ < V v μ₀ := by
  constructor
  · rintro ⟨K, σ, hσ⟩
    rw [← σ.value_toSplitting h₀] at hσ
    exact lt_of_lt_of_le hσ (value_le_V hB _)
  · intro h
    have hne : (Set.range fun s : Splitting μ₀ => s.value v).Nonempty :=
      ⟨_, trivialSplitting h₀, rfl⟩
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := exists_lt_of_lt_csSup hne h
    exact ⟨s.K, s.toSignal, by rwa [s.value_toSignal]⟩

/-! ### The prosecutor example -/

/-- Prior: innocent (`0`) with `7/10`, guilty (`1`) with `3/10`. -/
noncomputable def prior : Fin 2 → ℝ := ![7 / 10, 3 / 10]

/-- The prosecutor's value: conviction iff `P(guilty) ≥ 1/2`. -/
noncomputable def convict (μ : Fin 2 → ℝ) : ℝ := if 1 / 2 ≤ μ 1 then 1 else 0

theorem prior_mem : prior ∈ beliefs (Fin 2) := by
  refine ⟨fun ω => ?_, ?_⟩
  · fin_cases ω <;> norm_num [prior]
  · norm_num [prior, Fin.sum_univ_two]

theorem convict_le_one : ∀ μ ∈ beliefs (Fin 2), convict μ ≤ 1 := fun μ _ => by
  unfold convict; split_ifs <;> norm_num

/-- The concave majorant `min 1 (2 μ₁)`. -/
theorem concave_majorant : ConcaveOn ℝ (beliefs (Fin 2)) (fun μ => min 1 (2 * μ 1)) := by
  refine ⟨convex_beliefs, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  refine le_min ?_ ?_
  · have := min_le_left 1 (2 * x 1)
    have := min_le_left 1 (2 * y 1)
    nlinarith
  · have := min_le_right 1 (2 * x 1)
    have := min_le_right 1 (2 * y 1)
    nlinarith

/-- The optimal splitting: posterior `P(guilty) = 0` w.p. `2/5`, `= 1/2` w.p.
`3/5`. -/
noncomputable def prosecutorSplitting : Splitting prior where
  K := 2
  τ := ![2 / 5, 3 / 5]
  ν := ![![1, 0], ![1 / 2, 1 / 2]]
  τ_nonneg k := by fin_cases k <;> norm_num
  τ_sum := by norm_num [Fin.sum_univ_two]
  ν_mem k := by
    fin_cases k <;> exact ⟨fun ω => by fin_cases ω <;> norm_num, by norm_num [Fin.sum_univ_two]⟩
  mean ω := by fin_cases ω <;> norm_num [Fin.sum_univ_two, prior]

theorem prosecutor_value : prosecutorSplitting.value convict = 3 / 5 := by
  change ∑ k : Fin 2, prosecutorSplitting.τ k * convict (prosecutorSplitting.ν k) = 3 / 5
  simp [Fin.sum_univ_two, prosecutorSplitting, convict]

/-- **The prosecutor gets `3/5`**, against `0` without persuasion. -/
theorem prosecutor_V : V convict prior = 3 / 5 ∧ convict prior = 0 := by
  refine ⟨le_antisymm ?_ ?_, by norm_num [convict, prior]⟩
  · have := V_le_of_concave (v := convict) concave_majorant (fun μ _ => by
      unfold convict; split_ifs with h
      · exact le_min le_rfl (by linarith)
      · exact le_min zero_le_one (by
          have := (‹μ ∈ beliefs (Fin 2)›).1 1; linarith)) prior_mem
    norm_num [prior] at this
    exact this
  · have := value_le_V convict_le_one prosecutorSplitting
    rwa [prosecutor_value] at this

/-- The optimal signal: "guilty" always when guilty and w.p. `3/7` when
innocent; it attains `3/5`. -/
theorem prosecutor_signal : signalValue convict prior prosecutorSplitting.toSignal = 3 / 5 := by
  rw [Splitting.value_toSignal, prosecutor_value]

end Persuasion

end Econ
