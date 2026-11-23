/-
# Arrow–Debreu versus sequential (Radner) markets

Arrow (1953); MWG §19.D–19.E; Ljungqvist–Sargent §8.8; LeRoy–Werner ch. 4.

**Setup.** Two dates. Agents consume `x₀` today and `x_s` in each state `s`
tomorrow; a bundle is a pair `(x₀, x) ∈ ℝ × ℝ^σ` and endowments `e` are bundles.

* **Arrow–Debreu** markets: at date 0 the agent trades every state-contingent
  claim at state prices `m`. The budget is
  `x₀ + Σ_s m_s x_s ≤ e₀ + Σ_s m_s e_s` (`adBudget`).
* **Sequential** markets: the agent trades only the assets of a
  `Market σ ι` (payoffs `X`, prices `q`) at date 0, then spends the payoff in
  each state. The budget is: some portfolio `h` has `x₀ + q·h ≤ e₀` and
  `x_s ≤ e_s + (Xh)_s` in every state (`Market.SeqBudget`).

**Results.** Suppose `m` is a strictly positive state-price vector for the
asset prices, `q_i = Σ_s m_s X_{s i}` (it exists iff there is no arbitrage, by
`Market.ftap`).
* `seqBudget_adBudget`: every sequential-feasible bundle is AD-feasible.
* `seqBudget_iff_adBudget`: with complete markets the two budget sets coincide.
* `complete_iff_budget_eq`: conversely, the budget sets coincide for every
  endowment only if markets are complete.
* `isRadner_of_isAD` and `isAD_of_isRadner`: with complete markets an
  allocation is an AD equilibrium allocation at state prices `m` iff it is a
  Radner equilibrium allocation at asset prices `q`, with portfolios that clear
  the asset market. `exists_isAD_of_isRadner` derives the state prices from
  no arbitrage.

**Deviations.** Two dates; finitely many states, assets and agents.
Preferences are arbitrary utility functions; no monotonicity is used.
-/
module

public import EconLean.Finance.AssetPricing

@[expose] public section

noncomputable section

namespace Econ
namespace AssetPricing

open Finset

variable {σ ι : Type*} [Fintype ι]

/-- A consumption bundle: consumption today and in each state tomorrow. -/
abbrev Bundle (σ : Type*) := ℝ × (σ → ℝ)

variable [Fintype σ] in
/-- **Arrow–Debreu budget** at state prices `m` with endowment `e`. -/
def adBudget (m : σ → ℝ) (e x : Bundle σ) : Prop :=
  x.1 + ∑ s, m s * x.2 s ≤ e.1 + ∑ s, m s * e.2 s

namespace Market

variable (M : Market σ ι)

/-- **Sequential budget** with endowment `e`: some portfolio finances `x`. -/
def SeqBudget (e x : Bundle σ) : Prop :=
  ∃ h, x.1 + M.cost h ≤ e.1 ∧ ∀ s, x.2 s ≤ e.2 s + M.payoff h s

theorem payoff_add (h k : ι → ℝ) (s : σ) :
    M.payoff (h + k) s = M.payoff h s + M.payoff k s := by
  simp [payoff, mul_add, sum_add_distrib]

theorem payoff_sum {A : Type*} (t : Finset A) (h : A → ι → ℝ) (s : σ) :
    M.payoff (∑ a ∈ t, h a) s = ∑ a ∈ t, M.payoff (h a) s := by
  simp only [payoff, Finset.sum_apply, mul_sum]
  exact sum_comm

theorem payoff_neg (h : ι → ℝ) (s : σ) : M.payoff (-h) s = -M.payoff h s := by
  simp [payoff]

variable [Fintype σ] {M} {m : σ → ℝ}

/-- Sequential feasibility implies AD feasibility (only `m ≥ 0` and the pricing
equation are used). -/
theorem seqBudget_adBudget (hm : M.IsStatePrice m) {e x : Bundle σ} (hx : M.SeqBudget e x) :
    adBudget m e x := by
  obtain ⟨h, h0, h1⟩ := hx
  have : ∑ s, m s * x.2 s ≤ ∑ s, m s * e.2 s + M.cost h := by
    rw [M.cost_eq hm, ← sum_add_distrib]
    exact sum_le_sum fun s _ => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (h1 s) (hm.1 s).le
  unfold adBudget; linarith

/-- With complete markets, AD feasibility implies sequential feasibility: buy
the portfolio that pays exactly `x_s − e_s`. -/
theorem adBudget_seqBudget (hm : M.IsStatePrice m) (hc : M.Complete) {e x : Bundle σ}
    (hx : adBudget m e x) : M.SeqBudget e x := by
  obtain ⟨h, hh⟩ := hc (fun s => x.2 s - e.2 s)
  refine ⟨h, ?_, fun s => by rw [hh]; linarith⟩
  rw [M.cost_eq hm, hh]
  simp only [mul_sub, sum_sub_distrib]
  unfold adBudget at hx; linarith

/-- **Budget equivalence.** With complete markets and state prices `m`, the
sequential and Arrow–Debreu budget sets coincide. -/
theorem seqBudget_iff_adBudget (hm : M.IsStatePrice m) (hc : M.Complete) (e x : Bundle σ) :
    M.SeqBudget e x ↔ adBudget m e x :=
  ⟨seqBudget_adBudget hm, adBudget_seqBudget hm hc⟩

/-- **Completeness is needed.** If the sequential and AD budget sets coincide
for every endowment, markets are complete. -/
theorem complete_iff_budget_eq (hm : M.IsStatePrice m) :
    M.Complete ↔ ∀ e x : Bundle σ, M.SeqBudget e x ↔ adBudget m e x := by
  refine ⟨fun hc => seqBudget_iff_adBudget hm hc, fun H z => ?_⟩
  -- Take endowment `0` and the bundle `(−Σ m z, z)`, which is AD-affordable.
  obtain ⟨h, h0, h1⟩ := (H (0, 0) (-∑ s, m s * z s, z)).2 (by simp [adBudget])
  simp only [Pi.zero_apply, zero_add] at h0 h1
  rw [M.cost_eq hm] at h0
  have hsum : ∑ s, m s * (M.payoff h s - z s) = 0 := by
    apply le_antisymm
    · simp only [mul_sub, sum_sub_distrib]; linarith
    · exact sum_nonneg fun s _ => mul_nonneg (hm.1 s).le (by linarith [h1 s])
  rw [sum_eq_zero_iff_of_nonneg fun s _ => mul_nonneg (hm.1 s).le (by linarith [h1 s])] at hsum
  refine ⟨h, funext fun s => ?_⟩
  have := hsum s (mem_univ s)
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' (hm.1 s).ne'
  · linarith

end Market

/-- An exchange economy over two dates: endowments and utilities of finitely many agents. -/
structure Economy (A σ : Type*) where
  e : A → Bundle σ
  U : A → Bundle σ → ℝ

namespace Economy

variable [Fintype σ] {A : Type*} [Fintype A] (E : Economy A σ)

/-- Goods-market clearing today and in every state. -/
def Clears (x : A → Bundle σ) : Prop :=
  ∑ a, (x a).1 = ∑ a, (E.e a).1 ∧ ∀ s, ∑ a, (x a).2 s = ∑ a, (E.e a).2 s

/-- **Arrow–Debreu equilibrium** at state prices `m`: each agent maximizes
utility over the AD budget set, and goods markets clear. -/
def IsAD (m : σ → ℝ) (x : A → Bundle σ) : Prop :=
  (∀ a, adBudget m (E.e a) (x a) ∧ ∀ y, adBudget m (E.e a) y → E.U a y ≤ E.U a (x a)) ∧
    E.Clears x

/-- **Radner (sequential-markets) equilibrium** at asset market `M`:
portfolios `h` finance each agent's choice, each agent maximizes over the
sequential budget set, goods markets clear, and every asset is in zero net supply. -/
def IsRadner (M : Market σ ι) (x : A → Bundle σ) (h : A → ι → ℝ) : Prop :=
  (∀ a, ((x a).1 + M.cost (h a) ≤ (E.e a).1 ∧ ∀ s, (x a).2 s ≤ (E.e a).2 s + M.payoff (h a) s) ∧
      ∀ y, M.SeqBudget (E.e a) y → E.U a y ≤ E.U a (x a)) ∧
    E.Clears x ∧ ∀ i, ∑ a, h a i = 0

variable {E} {M : Market σ ι} {m : σ → ℝ}

/-- **AD ⟹ Radner.** With complete markets, an Arrow–Debreu equilibrium
allocation is a Radner equilibrium allocation at asset prices `q = Xᵀm`, with
portfolios clearing the asset market. -/
theorem isRadner_of_isAD [Nonempty A] (hm : M.IsStatePrice m) (hc : M.Complete)
    {x : A → Bundle σ} (hx : E.IsAD m x) : ∃ h, E.IsRadner M x h := by
  classical
  choose g hg using fun a => hc (fun s => (x a).2 s - (E.e a).2 s)
  obtain ⟨a₀⟩ := ‹Nonempty A›
  -- Agent `a₀` absorbs the aggregate portfolio, which pays zero in every state.
  set G := ∑ b, g b
  have hG : ∀ s, M.payoff G s = 0 := fun s => by
    rw [M.payoff_sum, sum_congr rfl fun b _ => congrFun (hg b) s, sum_sub_distrib, hx.2.2 s, sub_self]
  let h : A → ι → ℝ := fun a => g a + (if a = a₀ then -G else 0)
  have hh : ∀ a s, M.payoff (h a) s = (x a).2 s - (E.e a).2 s := fun a s => by
    simp only [h, M.payoff_add]
    split_ifs
    · rw [M.payoff_neg, hG, hg]; ring
    · rw [hg]; simp [Market.payoff]
  refine ⟨h, fun a => ⟨⟨?_, fun s => by rw [hh]; linarith⟩, fun y hy =>
    (hx.1 a).2 y (Market.seqBudget_adBudget hm hy)⟩, hx.2, fun i => ?_⟩
  · rw [M.cost_eq hm]
    simp only [hh, mul_sub, sum_sub_distrib]
    have := (hx.1 a).1; unfold adBudget at this; linarith
  · have : ∀ a, (if a = a₀ then -G else 0) i = if a = a₀ then -G i else 0 := fun a => by
      split_ifs <;> rfl
    simp only [h, Pi.add_apply, sum_add_distrib, this, Finset.sum_ite_eq', mem_univ, ite_true, G,
      Finset.sum_apply]
    ring

/-- **Radner ⟹ AD.** With complete markets, a Radner equilibrium allocation at
asset prices with state prices `m` is an Arrow–Debreu equilibrium allocation at `m`. -/
theorem isAD_of_isRadner (hm : M.IsStatePrice m) (hc : M.Complete) {x : A → Bundle σ}
    {h : A → ι → ℝ} (hx : E.IsRadner M x h) : E.IsAD m x :=
  ⟨fun a => ⟨Market.seqBudget_adBudget hm ⟨h a, (hx.1 a).1⟩, fun y hy =>
    (hx.1 a).2 y (Market.adBudget_seqBudget hm hc hy)⟩, hx.2.1⟩

/-- With complete markets and no arbitrage, every Radner equilibrium allocation
is an AD equilibrium allocation at some strictly positive state prices. -/
theorem exists_isAD_of_isRadner (hna : M.NoArbitrage) (hc : M.Complete) {x : A → Bundle σ}
    {h : A → ι → ℝ} (hx : E.IsRadner M x h) : ∃ m, M.IsStatePrice m ∧ E.IsAD m x := by
  obtain ⟨m, hm⟩ := M.ftap.1 hna
  exact ⟨m, hm, isAD_of_isRadner hm hc hx⟩

end Economy

/-- **Non-vacuity.** Two states, two Arrow securities priced at `1/2` each;
two agents with expected-utility-linear preferences and opposite endowments.
No trade is an AD equilibrium, hence a Radner equilibrium. -/
example : ∃ h, (⟨fun a : Bool => if a then (1, fun s => if s then 2 else 0) else
    (1, fun s => if s then 0 else 2), fun _ y => y.1 + ∑ s, (1 / 2 : ℝ) * y.2 s⟩ :
      Economy Bool Bool).IsRadner ⟨fun s i => if s = i then 1 else 0, fun _ => 1 / 2⟩
      (fun a => if a then (1, fun s => if s then 2 else 0) else
        (1, fun s => if s then 0 else 2)) h := by
  refine Economy.isRadner_of_isAD (m := fun _ => 1 / 2) ⟨fun _ => by norm_num, fun i => ?_⟩
    (fun z => ⟨z, funext fun s => ?_⟩) ⟨fun a => ⟨le_rfl, fun y hy => hy⟩, ?_⟩
  · simp
  · simp [Market.payoff]
  · refine ⟨by simp, fun s => ?_⟩
    cases s <;> simp

end AssetPricing
end Econ

end
