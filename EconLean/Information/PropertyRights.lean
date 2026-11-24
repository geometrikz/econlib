/-
# Property rights and relationship-specific investment (Grossman–Hart 1986; Hart–Moore 1990)

Hart, *Firms, Contracts, and Financial Structure* (1995), Ch. 2; Grossman–Hart (1986);
Hart–Moore (1990); Bolton–Dewatripont §11.1. A manager invests `i` (at cost `i`) before
trading with a partner. Investment is not contractible; ex post the parties trade and split
the gains from trade equally (Nash bargaining), so the manager's payoff is
`v(i) + (V(i) − v(i) − w)/2 − i = (V(i) + v(i) − w)/2 − i`, where `V(i)` is the joint surplus
inside the relationship, `v(i)` the manager's outside option, which depends on the assets
she owns (the **ownership structure**), and `w` the partner's outside option, which does not
depend on `i`. Efficiency requires maximizing `V(i) − i`.

Hart's assumptions are that investment is relationship-specific: its marginal return inside
the relationship is at least its marginal return outside, `V − v` nondecreasing; and that
owning more assets raises the marginal return of the outside option, `v' − v` nondecreasing.

Main results (reduced to monotone comparative statics, with no differentiability):
* `monotone_argmax`: if `F − G` is nondecreasing, `x` maximizes `G` and `y` maximizes `F`,
  then `max x y` maximizes `F` and `min x y` maximizes `G` (Topkis, one dimension).
* `underinvestment`: when the efficient investment is unique, the manager invests weakly
  less than it (the hold-up problem), whatever the ownership structure.
* `ownership_raises_investment`: giving the manager more assets weakly raises her investment
  (if her choice under the larger ownership is unique).
* `more_ownership_raises_surplus`: if only this manager's investment matters and total
  surplus increases up to the efficient level, giving her more assets weakly raises total
  surplus (Hart 1995, Ch. 2: the party whose investment matters should own the assets).
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace Econ

/-- `x` maximizes `F` over the nonnegative investments. -/
def IsInvestmentMax (F : ℝ → ℝ) (x : ℝ) : Prop := 0 ≤ x ∧ ∀ y, 0 ≤ y → F y ≤ F x

/-- **One-dimensional Topkis theorem**: maximizers of `F` lie above maximizers of `G` in the
strong set order when `F − G` is nondecreasing on the nonnegative investments. -/
theorem monotone_argmax {F G : ℝ → ℝ} (hFG : MonotoneOn (fun i => F i - G i) (Set.Ici 0))
    {x y : ℝ}
    (hx : IsInvestmentMax G x) (hy : IsInvestmentMax F y) :
    IsInvestmentMax F (max x y) ∧ IsInvestmentMax G (min x y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_left h]; exact ⟨hy, hx⟩
  · rw [max_eq_left h, min_eq_right h]
    have hd := hFG hy.1 hx.1 h
    have h1 := hy.2 x hx.1
    have h2 := hx.2 y hy.1
    simp only at hd
    refine ⟨⟨hx.1, fun z hz => ?_⟩, ⟨hy.1, fun z hz => ?_⟩⟩
    · have := hy.2 z hz; linarith
    · have := hx.2 z hz; linarith

/-- The manager's payoff under Nash bargaining. -/
noncomputable def managerPayoff (V v : ℝ → ℝ) (w : ℝ) (i : ℝ) : ℝ := (V i + v i - w) / 2 - i

/-- Total surplus net of the investment cost. -/
def netSurplus (V : ℝ → ℝ) (i : ℝ) : ℝ := V i - i

/-- **Hold-up: underinvestment** (Grossman–Hart 1986). If the investment is
relationship-specific (`V − v` nondecreasing) and `y` is the unique efficient investment,
then any investment `x` the manager chooses satisfies `x ≤ y`. -/
theorem underinvestment {V v : ℝ → ℝ} {w : ℝ} (hspec : MonotoneOn (fun i => V i - v i) (Set.Ici 0)) {x y : ℝ}
    (hx : IsInvestmentMax (managerPayoff V v w) x) (hy : IsInvestmentMax (netSurplus V) y)
    (huniq : ∀ z, IsInvestmentMax (netSurplus V) z → z = y) : x ≤ y := by
  have hFG : MonotoneOn (fun i => netSurplus V i - managerPayoff V v w i) (Set.Ici 0) :=
      fun a ha b hb hab => by
    have := hspec ha hb hab
    simp only [netSurplus, managerPayoff] at this ⊢
    linarith
  have := (monotone_argmax hFG hx hy).1
  rw [← huniq _ this]
  exact le_max_left x y

/-- **More assets, more investment** (Hart 1995, Ch. 2). If owning more assets raises the
manager's marginal outside return (`v' − v` nondecreasing), then her investment `x'` under the
larger ownership is weakly above her investment `x` under the smaller one, when `x'` is her
unique choice. -/
theorem ownership_raises_investment {V v v' : ℝ → ℝ} {w w' : ℝ}
    (hmore : MonotoneOn (fun i => v' i - v i) (Set.Ici 0)) {x x' : ℝ}
    (hx : IsInvestmentMax (managerPayoff V v w) x) (hx' : IsInvestmentMax (managerPayoff V v' w') x')
    (huniq : ∀ z, IsInvestmentMax (managerPayoff V v' w') z → z = x') : x ≤ x' := by
  have hFG : MonotoneOn (fun i => managerPayoff V v' w' i - managerPayoff V v w i)
      (Set.Ici 0) := fun a ha b hb hab => by
    have := hmore ha hb hab
    simp only [managerPayoff] at this ⊢
    linarith
  have := (monotone_argmax hFG hx hx').1
  rw [← huniq _ this]
  exact le_max_left x x'

/-- **Who should own the assets** (Hart 1995, Ch. 2, the case where one party's investment matters). Compare two
ownership structures, the second giving the manager more assets (`v' − v` nondecreasing).
If the investment is relationship-specific under the larger one (hence under both), the efficient investment `y` is unique,
the manager's choice `x'` under the larger ownership is unique, and net surplus is
nondecreasing on `[0, y]` (e.g. concave with peak `y`), then the larger ownership yields
weakly more total surplus. -/
theorem more_ownership_raises_surplus {V v v' : ℝ → ℝ} {w w' : ℝ}
    (hspec' : MonotoneOn (fun i => V i - v' i) (Set.Ici 0))
    (hmore : MonotoneOn (fun i => v' i - v i) (Set.Ici 0)) {x x' y : ℝ}
    (hx : IsInvestmentMax (managerPayoff V v w) x) (hx' : IsInvestmentMax (managerPayoff V v' w') x')
    (huniq' : ∀ z, IsInvestmentMax (managerPayoff V v' w') z → z = x')
    (hy : IsInvestmentMax (netSurplus V) y) (huniq : ∀ z, IsInvestmentMax (netSurplus V) z → z = y)
    (hmono : MonotoneOn (netSurplus V) (Set.Icc 0 y)) :
    netSurplus V x ≤ netSurplus V x' :=
  have hspec : MonotoneOn (fun i => V i - v i) (Set.Ici 0) := fun a ha b hb hab => by
    have h1 := hspec' ha hb hab
    have h2 := hmore ha hb hab
    simp only at h1 h2 ⊢
    linarith
  hmono ⟨hx.1, underinvestment hspec hx hy huniq⟩ ⟨hx'.1, underinvestment hspec' hx' hy huniq⟩
    (ownership_raises_investment hmore hx hx' huniq')

/-- Witness: `V(i) = 2 log(1 + i)` with outside option `v = 0` (a fully specific
investment) and `w = 0`. The efficient investment is `1` (`V' = 1`); the manager, who gets half
the marginal return, chooses `0`. This checks the maximizers and specificity only; it does not
prove uniqueness. -/
example : IsInvestmentMax (netSurplus fun i => 2 * Real.log (1 + i)) 1 ∧
    IsInvestmentMax (managerPayoff (fun i => 2 * Real.log (1 + i)) (fun _ => 0) 0) 0 ∧
    MonotoneOn (fun i => 2 * Real.log (1 + i) - 0) (Set.Ici 0) := by
  refine ⟨⟨zero_le_one, fun z hz => ?_⟩, ⟨le_rfl, fun z hz => ?_⟩, fun a ha b hb hab => ?_⟩
  · simp only [netSurplus]
    have := Real.log_le_sub_one_of_pos (show 0 < (1 + z) / 2 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    norm_num
    linarith
  · simp only [managerPayoff]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + z by linarith)
    norm_num
    linarith
  · simp only [Set.mem_Ici] at ha hb
    have := Real.log_le_log (by linarith) (show 1 + a ≤ 1 + b by linarith)
    linarith

/-- Witness that all hypotheses of `more_ownership_raises_surplus` hold together:
`V(i) = 2 log(1 + i)`, outside option `v = 0` without the assets and `v' = log(1 + i)` with
them, `w = w' = 0`. The manager invests `0` without the assets and `1/2` with them (uniquely),
the efficient investment is `1` (uniquely), and net surplus rises on `[0, 1]`. -/
example : netSurplus (fun i => 2 * Real.log (1 + i)) 0 ≤
    netSurplus (fun i => 2 * Real.log (1 + i)) (1 / 2) := by
  have hlogmono : MonotoneOn (fun i : ℝ => Real.log (1 + i)) (Set.Ici 0) := fun a ha b hb hab => by
    simp only [Set.mem_Ici] at ha hb
    exact Real.log_le_log (by linarith) (by linarith)
  -- strict concavity bound: `log t ≤ t − 1` with equality only at `t = 1`
  have key : ∀ c z : ℝ, 0 < c → 0 ≤ z →
      Real.log (1 + z) - Real.log c ≤ (1 + z) / c - 1 ∧
        (z ≠ c - 1 → Real.log (1 + z) - Real.log c < (1 + z) / c - 1) := by
    intro c z hc hz
    have hpos : 0 < (1 + z) / c := div_pos (by linarith) hc
    rw [← Real.log_div (by linarith) hc.ne']
    refine ⟨Real.log_le_sub_one_of_pos hpos, fun hne => Real.log_lt_sub_one_of_pos hpos ?_⟩
    intro h1
    rw [div_eq_one_iff_eq hc.ne'] at h1
    exact hne (by linarith)
  have hx' : ∀ z, 0 ≤ z → managerPayoff (fun i => 2 * Real.log (1 + i))
      (fun i => Real.log (1 + i)) 0 z ≤ managerPayoff (fun i => 2 * Real.log (1 + i))
      (fun i => Real.log (1 + i)) 0 (1 / 2) ∧ (z ≠ 1 / 2 →
      managerPayoff (fun i => 2 * Real.log (1 + i)) (fun i => Real.log (1 + i)) 0 z <
      managerPayoff (fun i => 2 * Real.log (1 + i)) (fun i => Real.log (1 + i)) 0 (1 / 2)) := by
    intro z hz
    obtain ⟨h1, h2⟩ := key (3 / 2) z (by norm_num) hz
    have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    simp only [managerPayoff, e]
    refine ⟨by linarith, fun hne => ?_⟩
    have := h2 (by intro h; apply hne; linarith)
    linarith
  have hy : ∀ z, 0 ≤ z → netSurplus (fun i => 2 * Real.log (1 + i)) z ≤
      netSurplus (fun i => 2 * Real.log (1 + i)) 1 ∧ (z ≠ 1 →
      netSurplus (fun i => 2 * Real.log (1 + i)) z < netSurplus (fun i => 2 * Real.log (1 + i)) 1) := by
    intro z hz
    obtain ⟨h1, h2⟩ := key 2 z (by norm_num) hz
    have e : (1 : ℝ) + 1 = 2 := by norm_num
    simp only [netSurplus, e]
    refine ⟨by linarith, fun hne => ?_⟩
    have := h2 (by intro h; apply hne; linarith)
    linarith
  refine more_ownership_raises_surplus (V := fun i => 2 * Real.log (1 + i)) (v := fun _ => 0)
    (v' := fun i => Real.log (1 + i)) (w := 0) (w' := 0) (y := 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a ha b hb hab
    have := hlogmono ha hb hab
    simp only at this ⊢
    linarith
  · intro a ha b hb hab
    have := hlogmono ha hb hab
    simp only at this ⊢
    linarith
  · refine ⟨le_rfl, fun z hz => ?_⟩
    have := (key 1 z one_pos hz).1
    simp only [managerPayoff, Real.log_one, add_zero] at this ⊢
    linarith
  · exact ⟨by norm_num, fun z hz => (hx' z hz).1⟩
  · intro z hz
    by_contra hne
    exact absurd (hz.2 _ (by norm_num)) (not_le.2 ((hx' z hz.1).2 hne))
  · exact ⟨zero_le_one, fun z hz => (hy z hz).1⟩
  · intro z hz
    by_contra hne
    exact absurd (hz.2 _ zero_le_one) (not_le.2 ((hy z hz.1).2 hne))
  · intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    simp only [netSurplus]
    have h1 := (key (1 + b) a (by linarith) ha.1).1
    have hd : (1 + a) / (1 + b) - 1 = (a - b) / (1 + b) := by
      rw [div_sub_one (show (1 + b) ≠ 0 by linarith)]; congr 1; ring
    have hq : (a - b) / (1 + b) ≤ (a - b) / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith

end Econ
