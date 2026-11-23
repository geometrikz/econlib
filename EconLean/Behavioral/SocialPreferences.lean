/-
# Social preferences: inequity aversion (Fehr–Schmidt, Bolton–Ockenfels)

References.
* E. Fehr and K. M. Schmidt (1999), "A Theory of Fairness, Competition, and
  Cooperation", *QJE* 114(3).
* G. E. Bolton and A. Ockenfels (2000), "ERC: A Theory of Equity,
  Reciprocity, and Competition", *AER* 90(1).

**Fehr–Schmidt.** With `n` players and material payoffs `x`, player `i` has

    Uᵢ(x) = xᵢ − αᵢ/(n−1) Σⱼ max(xⱼ − xᵢ, 0) − βᵢ/(n−1) Σⱼ max(xᵢ − xⱼ, 0),

with (in FS) `βᵢ ≤ αᵢ` and `0 ≤ βᵢ < 1`. We prove

* the ultimatum game (FS Proposition 1): an inequity-averse responder accepts
  a share `s` of the pie iff `s ≥ α/(1+2α)` (`accepts_iff`); the proposer's
  unique optimal offer is that threshold when `β < 1/2`
  (`ultimatum_offer_unique`) and the equal split is optimal when `β > 1/2`
  (`ultimatum_offer_half`, uniquely: `ultimatum_offer_half_unique`);
* the dictator game: a dictator with `β < 1/2` keeps everything, one with
  `β > 1/2` splits equally (`dictator_selfish`, `dictator_half`);
* the public-good game (FS Proposition 4): if `a + βᵢ < 1` (`a` the marginal
  per-capita return), contributing more strictly lowers `i`'s utility whatever
  the others do, so contributing nothing is strictly dominant
  (`publicGood_freeRide`).

**ERC (Bolton–Ockenfels).** Player `i` cares about own payoff `xᵢ` and relative
share `σᵢ = xᵢ / Σⱼ xⱼ` (`1/n` when the total is `0`), through a motive
function `v(x, σ)`. For two players we prove: a dictator never gives away more
than half when `v` is strictly increasing in `x` and nondecreasing in `σ` below
`1/2` (`erc_dictator_le_half`); the responder accepts the equal split
(`erc_accepts_half`); and if a zero offer is rejected and `v` is continuous at
`(0, 0)`, then all sufficiently small positive offers are rejected
(`erc_rejects_small`).
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Econ.SocialPreferences

open Finset

/-! ### Fehr–Schmidt inequity aversion -/

section FS

variable {ι : Type*} [Fintype ι]

/-- Fehr–Schmidt utility of player `i` with envy weight `α` and guilt weight
`β`, at material payoffs `x`. -/
noncomputable def fs (α β : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  x i - α / (Fintype.card ι - 1) * ∑ j, max (x j - x i) 0
    - β / (Fintype.card ι - 1) * ∑ j, max (x i - x j) 0

/-- Two-player Fehr–Schmidt utility: own payoff `x`, other's payoff `y`. -/
noncomputable def fs2 (α β x y : ℝ) : ℝ := x - α * max (y - x) 0 - β * max (x - y) 0

/-- With two players the general formula is the two-player one. -/
theorem fs_two (α β : ℝ) (x : Fin 2 → ℝ) : fs α β x 0 = fs2 α β (x 0) (x 1) := by
  simp [fs, fs2, Fin.sum_univ_two]
  norm_num

/-- Equal split gives material payoff only. -/
theorem fs2_self (α β x : ℝ) : fs2 α β x x = x := by simp [fs2]

/-- **Ultimatum responder** (FS Proposition 1). An inequity-averse responder
(`0 ≤ α`, `β ≤ 1`) accepts share `s ∈ [0, 1]` of a unit pie (rejection gives
both `0`) iff `s ≥ α/(1+2α)`. -/
theorem accepts_iff {α β s : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hs1 : s ≤ 1) :
    fs2 α β 0 0 ≤ fs2 α β s (1 - s) ↔ α / (1 + 2 * α) ≤ s := by
  rw [fs2_self, div_le_iff₀ (by linarith)]
  unfold fs2
  rcases le_total s (1 / 2) with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> intro h' <;> nlinarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> intro h' <;> nlinarith

/-- The responder's acceptance threshold. -/
noncomputable def threshold (α : ℝ) : ℝ := α / (1 + 2 * α)

theorem threshold_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ threshold α := by
  unfold threshold; positivity

theorem threshold_lt_half {α : ℝ} (hα : 0 ≤ α) : threshold α < 1 / 2 := by
  unfold threshold; rw [div_lt_iff₀ (by linarith)]; linarith

/-- The proposer's payoff from offering `s`: Fehr–Schmidt utility of the
outcome, `(1 − s, s)` if the responder (envy `αR`, guilt `βR`) accepts and
`(0, 0)` if she rejects. Indifferent responders accept. -/
noncomputable def proposerValue (αP βP αR βR s : ℝ) : ℝ :=
  if fs2 αR βR 0 0 ≤ fs2 αR βR s (1 - s) then fs2 αP βP (1 - s) s else 0

theorem proposerValue_of_le {αP βP αR βR s : ℝ} (hαR : 0 ≤ αR) (hβR : βR ≤ 1)
    (hs1 : s ≤ 1) (h : threshold αR ≤ s) : proposerValue αP βP αR βR s = fs2 αP βP (1 - s) s := by
  unfold proposerValue
  rw [ite_eq_left ((accepts_iff hαR hβR hs1).2 h)]

theorem proposerValue_of_lt {αP βP αR βR s : ℝ} (hαR : 0 ≤ αR) (hβR : βR ≤ 1)
    (hs1 : s ≤ 1) (h : s < threshold αR) : proposerValue αP βP αR βR s = 0 := by
  unfold proposerValue
  rw [ite_eq_right (fun h' => absurd ((accepts_iff hαR hβR hs1).1 h') (not_le.2 h))]

/-- Proposer's utility on accepted offers up to one half. -/
theorem fs2_offer_le_half {αP βP s : ℝ} (hs : s ≤ 1 / 2) :
    fs2 αP βP (1 - s) s = (1 - βP) + s * (2 * βP - 1) := by
  unfold fs2
  rw [max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

/-- Proposer's utility on accepted offers above one half is at most `1 − s`. -/
theorem fs2_offer_ge_half {αP βP s : ℝ} (hαP : 0 ≤ αP) (hs : 1 / 2 ≤ s) :
    fs2 αP βP (1 - s) s ≤ 1 - s := by
  unfold fs2
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  nlinarith

/-- **Ultimatum proposer, weak guilt** (FS Proposition 1). If the proposer's
guilt weight is below `1/2`, offering exactly the responder's threshold
`αR/(1+2αR)` is the unique optimal offer. -/
theorem ultimatum_offer_unique {αP βP αR βR : ℝ} (hαP : 0 ≤ αP) (hβP : βP < 1 / 2)
    (hαR : 0 ≤ αR) (hβR : βR ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : s ≠ threshold αR) :
    proposerValue αP βP αR βR s < proposerValue αP βP αR βR (threshold αR) := by
  have t0 := threshold_nonneg hαR
  have th := threshold_lt_half hαR
  rw [proposerValue_of_le hαR hβR (by linarith) le_rfl, fs2_offer_le_half th.le]
  have hstar : 1 / 2 ≤ (1 - βP) + threshold αR * (2 * βP - 1) := by nlinarith
  rcases lt_or_gt_of_ne hs with h | h
  · rw [proposerValue_of_lt hαR hβR hs1 h]; linarith
  · rw [proposerValue_of_le hαR hβR hs1 h.le]
    rcases le_total s (1 / 2) with h2 | h2
    · rw [fs2_offer_le_half h2]; nlinarith
    · have := fs2_offer_ge_half (βP := βP) hαP h2
      by_cases h3 : s = 1 / 2
      · subst h3; rw [fs2_offer_le_half le_rfl]; nlinarith
      · have : 1 / 2 < s := lt_of_le_of_ne h2 (Ne.symm h3)
        linarith

/-- **Ultimatum proposer, strong guilt** (FS Proposition 1). If the
proposer's guilt weight exceeds `1/2`, offering half the pie is optimal. -/
theorem ultimatum_offer_half {αP βP αR βR : ℝ} (hαP : 0 ≤ αP) (hβP : 1 / 2 < βP)
    (hαR : 0 ≤ αR) (hβR : βR ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    proposerValue αP βP αR βR s ≤ proposerValue αP βP αR βR (1 / 2) := by
  have th := threshold_lt_half hαR
  rw [proposerValue_of_le hαR hβR (by norm_num) th.le, fs2_offer_le_half le_rfl]
  rcases lt_or_ge s (threshold αR) with h | h
  · rw [proposerValue_of_lt hαR hβR hs1 h]; nlinarith
  · rw [proposerValue_of_le hαR hβR hs1 h]
    rcases le_total s (1 / 2) with h2 | h2
    · rw [fs2_offer_le_half h2]; nlinarith
    · have := fs2_offer_ge_half (βP := βP) hαP h2; linarith

/-- With strong guilt the equal split is the *unique* optimal offer. -/
theorem ultimatum_offer_half_unique {αP βP αR βR : ℝ} (hαP : 0 ≤ αP) (hβP : 1 / 2 < βP)
    (hαR : 0 ≤ αR) (hβR : βR ≤ 1) {s : ℝ} (hs1 : s ≤ 1) (hs : s ≠ 1 / 2) :
    proposerValue αP βP αR βR s < proposerValue αP βP αR βR (1 / 2) := by
  have th := threshold_lt_half hαR
  rw [proposerValue_of_le hαR hβR (by norm_num) th.le, fs2_offer_le_half le_rfl]
  rcases lt_or_ge s (threshold αR) with h | h
  · rw [proposerValue_of_lt hαR hβR hs1 h]; nlinarith
  · rw [proposerValue_of_le hαR hβR hs1 h]
    rcases lt_or_gt_of_ne hs with h2 | h2
    · rw [fs2_offer_le_half h2.le]; nlinarith
    · have := fs2_offer_ge_half (βP := βP) hαP h2.le; linarith

/-- **Dictator game, weak guilt.** A dictator with `βD < 1/2` strictly prefers
keeping the whole pie to any positive gift `g > 0`. -/
theorem dictator_selfish {αD βD g : ℝ} (hαD : 0 ≤ αD) (hβD : βD < 1 / 2) (hg0 : 0 < g) : fs2 αD βD (1 - g) g < fs2 αD βD 1 0 := by
  have h10 : fs2 αD βD 1 0 = 1 - βD := by
    unfold fs2; rw [max_eq_right (by norm_num), max_eq_left (by norm_num)]; ring
  rw [h10]
  rcases le_total g (1 / 2) with h | h
  · rw [fs2_offer_le_half h]; nlinarith
  · have := fs2_offer_ge_half (βP := βD) hαD h; linarith

/-- **Dictator game, strong guilt.** A dictator with `βD > 1/2` weakly prefers
the equal split to any gift `g`. -/
theorem dictator_half {αD βD g : ℝ} (hαD : 0 ≤ αD) (hβD : 1 / 2 < βD) : fs2 αD βD (1 - g) g ≤ fs2 αD βD (1 / 2) (1 / 2) := by
  rw [fs2_self]
  rcases le_total g (1 / 2) with h | h
  · rw [fs2_offer_le_half h]; nlinarith
  · have := fs2_offer_ge_half (βP := βD) hαD h; linarith

/-! #### Public goods -/

/-- Material payoffs in the linear public-good game: endowment `y`,
contributions `g`, marginal per-capita return `a`. -/
def pgPayoff (y a : ℝ) (g : ι → ℝ) (i : ι) : ℝ := y - g i + a * ∑ j, g j

/-- **Free riding is dominant** (FS Proposition 4). If `0 ≤ α`, `0 ≤ β` and
`a + β < 1`, then raising one's contribution by `d > 0` strictly lowers one's
Fehr–Schmidt utility, whatever the others contribute. -/
theorem publicGood_freeRide [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) {α β a y d : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : a + β < 1) (hd : 0 < d) (g : ι → ℝ) (i : ι) :
    fs α β (pgPayoff y a (Function.update g i (g i + d))) i < fs α β (pgPayoff y a g) i := by
  set x := pgPayoff y a g
  set x' := pgPayoff y a (Function.update g i (g i + d))
  have hsum : ∑ j, Function.update g i (g i + d) j = ∑ j, g j + d := by
    rw [Finset.sum_update_of_mem (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i),
      sdiff_singleton_eq_erase]
    ring
  have hxi : x' i = x i - (1 - a) * d := by
    simp only [x, x', pgPayoff, hsum, Function.update_self]; ring
  have hxj : ∀ j, j ≠ i → x' j = x j + a * d := by
    intro j hj
    simp only [x, x', pgPayoff, hsum, Function.update_of_ne hj]; ring
  have hN : (0 : ℝ) < Fintype.card ι - 1 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    linarith
  -- envy can only rise
  have henvy : ∑ j, max (x j - x i) 0 ≤ ∑ j, max (x' j - x' i) 0 := by
    refine sum_le_sum fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp
    · rw [hxj j hj, hxi]
      exact max_le_max (by nlinarith) le_rfl
  -- guilt falls by at most `d` per other player
  have hguilt : ∑ j, max (x i - x j) 0 - (Fintype.card ι - 1) * d ≤
      ∑ j, max (x' i - x' j) 0 := by
    have hterm : ∀ j, max (x i - x j) 0 - (if j = i then 0 else d) ≤ max (x' i - x' j) 0 := by
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · rw [ite_eq_right hj, hxj j hj, hxi, sub_le_iff_le_add]
        refine max_le ?_ ?_
        · have := le_max_left (x i - (1 - a) * d - (x j + a * d)) 0
          linarith
        · have := le_max_right (x i - (1 - a) * d - (x j + a * d)) 0
          linarith
    have hcount : ∑ j : ι, (if j = i then (0 : ℝ) else d) = (Fintype.card ι - 1) * d := by
      rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
      congr 1
      rw [filter_ne' univ i, card_erase_of_mem (mem_univ i), card_univ,
        Nat.cast_sub (by omega)]
      simp
    rw [← hcount, ← sum_sub_distrib]
    exact sum_le_sum fun j _ => hterm j
  unfold fs
  have h1 : α / (Fintype.card ι - 1) * ∑ j, max (x j - x i) 0 ≤
      α / (Fintype.card ι - 1) * ∑ j, max (x' j - x' i) 0 :=
    mul_le_mul_of_nonneg_left henvy (div_nonneg hα hN.le)
  have h2 : β / (Fintype.card ι - 1) * (∑ j, max (x i - x j) 0 - (Fintype.card ι - 1) * d) ≤
      β / (Fintype.card ι - 1) * ∑ j, max (x' i - x' j) 0 :=
    mul_le_mul_of_nonneg_left hguilt (div_nonneg hβ hN.le)
  have h3 : β / (Fintype.card ι - 1) * ((Fintype.card ι - 1) * d) = β * d := by
    field_simp
  rw [mul_sub, h3] at h2
  have h4 : β * d < (1 - a) * d := mul_lt_mul_of_pos_right (by linarith) hd
  show x' i - _ - _ < x i - _ - _
  linarith [hxi]

end FS

/-! ### ERC (Bolton–Ockenfels) -/

section ERC

/-- Relative share `xᵢ / Σⱼ xⱼ`, equal to `1/n` when the total is `0`. -/
noncomputable def relShare {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : ℝ :=
  if ∑ j, x j = 0 then 1 / Fintype.card ι else x i / ∑ j, x j

/-- ERC utility `v(xᵢ, σᵢ)` of player `i`. -/
noncomputable def erc {ι : Type*} [Fintype ι] (v : ℝ → ℝ → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  v (x i) (relShare x i)

/-- In a two-player unit pie split `(1 − s, s)`, the responder's relative share
is `s`; after rejection `(0, 0)` it is `1/2`. -/
theorem relShare_split (s : ℝ) : relShare ![1 - s, s] 1 = s := by
  simp [relShare, Fin.sum_univ_two]

theorem relShare_zero : relShare (![0, 0] : Fin 2 → ℝ) 1 = 1 / 2 := by
  simp [relShare, Fin.sum_univ_two]

/-- **Dictators give at most half** (BO 2000). If `v` is strictly increasing in
own payoff and nondecreasing in the relative share below `1/2`, every gift
`g > 1/2` is strictly worse than giving exactly half. -/
theorem erc_dictator_le_half {v : ℝ → ℝ → ℝ} (hx : ∀ σ, StrictMono fun x => v x σ)
    (hσ : ∀ x σ σ', σ ≤ σ' → σ' ≤ 1 / 2 → v x σ ≤ v x σ') {g : ℝ} (hg : 1 / 2 < g) :
    erc v ![1 - g, g] 0 < erc v ![1 - (1 / 2 : ℝ), 1 / 2] 0 := by
  have hsh : ∀ s : ℝ, relShare ![1 - s, s] 0 = 1 - s := by intro s; simp [relShare, Fin.sum_univ_two]
  simp only [erc, hsh, Matrix.cons_val_zero]
  calc v (1 - g) (1 - g) < v (1 / 2) (1 - g) := hx _ (by linarith)
    _ ≤ v (1 / 2) (1 / 2) := hσ _ _ _ (by linarith) le_rfl
    _ = v (1 - 1 / 2) (1 - 1 / 2) := by norm_num

/-- **The equal split is accepted** in the ultimatum game when `v` is
nondecreasing in own payoff. -/
theorem erc_accepts_half {v : ℝ → ℝ → ℝ} (hx : ∀ σ, Monotone fun x => v x σ) :
    erc v (![0, 0] : Fin 2 → ℝ) 1 ≤ erc v ![1 - (1 / 2 : ℝ), 1 / 2] 1 := by
  simp only [erc, relShare_split, relShare_zero]
  exact hx _ (by norm_num)

/-- **Small positive offers are rejected** (BO 2000). If the responder rejects
the zero offer (`v(0,0) < v(0,1/2)`) and `v` is continuous at `(0,0)`, then
every sufficiently small positive offer is rejected. -/
theorem erc_rejects_small {v : ℝ → ℝ → ℝ}
    (hc : ContinuousAt (fun p : ℝ × ℝ => v p.1 p.2) (0, 0)) (h0 : v 0 0 < v 0 (1 / 2)) :
    ∃ ε > 0, ∀ s, 0 < s → s < ε → erc v ![1 - s, s] 1 < erc v (![0, 0] : Fin 2 → ℝ) 1 := by
  simp only [erc, relShare_split, relShare_zero]
  have hcs : ContinuousAt (fun s : ℝ => v s s) 0 :=
    hc.comp (f := fun s : ℝ => (s, s)) (Continuous.continuousAt (by fun_prop))
  have hev : ∀ᶠ s in nhds (0 : ℝ), v s s < v 0 (1 / 2) :=
    hcs.eventually (gt_mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun s hs hsε => ?_⟩
  have := hball (y := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; exact hsε)
  simpa using this

end ERC

end Econ.SocialPreferences
