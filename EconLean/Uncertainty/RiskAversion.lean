/-
# Risk aversion, certainty equivalents, Arrow–Pratt and Pratt's theorem

MWG §6.C (Def. 6.C.1, Props. 6.C.1, 6.C.2).

**The economics.** A vN–M decision maker with Bernoulli utility `u` over
money is **risk averse** if for every lottery `F` she weakly prefers the
sure amount `E_F[x]` to `F` itself: `E_F[u] ≤ u(E_F[x])`.
* **Prop. 6.C.1**: risk aversion ⟺ `u` concave ⟺ certainty equivalent
  `c(F, u) ≤ E_F[x]` for all `F`.
* **Arrow–Pratt** coefficient `r_A(x) = -u''(x)/u'(x)`; for increasing
  twice-differentiable `u`, risk aversion ⟺ `r_A ≥ 0`.
* **Pratt's theorem** (Prop. 6.C.2, (ii) ⟺ (iii)): `u₂` is more risk
  averse than `u₁` (lower certainty equivalent for every lottery) iff
  `u₂ = ψ ∘ u₁` for an increasing concave `ψ`.

The "⟸" directions are Jensen's inequality (`ConcaveOn.le_map_sum` in
Mathlib); the "⟹" directions test the definition on two-point lotteries.
The Arrow–Pratt clause (i) of Pratt's theorem is in `Pratt.lean`.

**Domains.** The certainty-equivalent and Arrow–Pratt characterizations come in two
forms: on all of `ℝ` (`riskAverse_iff_…`), and on a convex (for Arrow–Pratt: open convex)
set of wealth levels `I` (`riskAverseOn_iff_…`), which covers `log`, `√` and CRRA
utilities on `(0, ∞)`. Pratt's theorem (comparing two utilities) is stated on `ℝ` only;
its interval version is not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import EconLean.Uncertainty.MoneyLottery
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

namespace Econ

open Set Finset SimpleLottery

/-- `F` only pays amounts in `I`. -/
def SimpleLottery.SupportedIn (F : SimpleLottery) (I : Set ℝ) : Prop :=
  (F.prob.support : Set ℝ) ⊆ I

/-- **Risk aversion** on a set of wealth levels `I` (MWG Def. 6.C.1):
every lottery paying in `I` is weakly worse than its mean for sure.
Intended for convex `I` (an interval), so that the mean lies in `I`; the
characterization `riskAverseOn_iff_concaveOn` assumes this. Lotteries are
finitely supported (see `MoneyLottery.lean`). -/
def RiskAverseOn (u : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ F : SimpleLottery, F.SupportedIn I → F.expect u ≤ u F.mean

/-- **Jensen for simple lotteries.** A concave `u` on a convex set `I`
satisfies `E_F[u] ≤ u(E_F[x])` for lotteries in `I`. -/
theorem ConcaveOn.expect_le {u : ℝ → ℝ} {I : Set ℝ} (hu : ConcaveOn ℝ I u)
    (F : SimpleLottery) (hF : F.SupportedIn I) : F.expect u ≤ u F.mean := by
  have h := hu.le_map_sum (t := F.prob.support) (w := F.prob) (p := id)
    (fun x _ => F.nonneg x) F.sum_prob (fun x hx => hF hx)
  simpa [expect_eq_sum, mean, smul_eq_mul] using h

/-- **Risk aversion ⟺ concave Bernoulli utility** (MWG Prop. 6.C.1,
(i) ⟺ (ii)). -/
theorem riskAverseOn_iff_concaveOn {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I) :
    RiskAverseOn u I ↔ ConcaveOn ℝ I u := by
  refine ⟨fun h => ⟨hI, fun x hx y hy a b ha hb hab => ?_⟩, fun h F hF => ConcaveOn.expect_le h F hF⟩
  -- Test risk aversion on the two-point lottery (x w.p. a, y w.p. b).
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha1 : a ≤ 1 := by linarith
  have := h (twoPoint x y a ha ha1) fun z hz => by
    rcases support_twoPoint_subset x y a ha ha1 hz with h | h
    · rw [h]; exact hx
    · rw [Set.mem_singleton_iff.1 h]; exact hy
  rw [expect_twoPoint, mean, expect_twoPoint] at this
  simpa [smul_eq_mul] using this

/-! ### Certainty equivalents -/

/-- `c` is a **certainty equivalent** of `F` for `u`: `u(c) = E_F[u]`. -/
def IsCertaintyEquivalent (u : ℝ → ℝ) (F : SimpleLottery) (c : ℝ) : Prop :=
  u c = F.expect u

/-- Expected utility lies between the worst and best payoff in the support. -/
theorem SimpleLottery.exists_min_max_expect (F : SimpleLottery) (u : ℝ → ℝ) :
    ∃ x ∈ F.prob.support, ∃ y ∈ F.prob.support, u x ≤ F.expect u ∧ F.expect u ≤ u y := by
  obtain ⟨x, hx, hxmin⟩ := F.prob.support.exists_min_image u F.support_nonempty
  obtain ⟨y, hy, hymax⟩ := F.prob.support.exists_max_image u F.support_nonempty
  refine ⟨x, hx, y, hy, ?_, ?_⟩
  · simpa [expect_const] using F.expect_mono (u := fun _ => u x) hxmin
  · simpa [expect_const] using F.expect_mono (v := fun _ => u y) hymax

/-- A continuous `u` gives every lottery a certainty equivalent
(intermediate value theorem). -/
theorem exists_certaintyEquivalent {u : ℝ → ℝ} (hu : Continuous u) (F : SimpleLottery) :
    ∃ c, IsCertaintyEquivalent u F c := by
  obtain ⟨x, -, y, -, hx, hy⟩ := F.exists_min_max_expect u
  obtain ⟨c, -, hc⟩ := intermediate_value_uIcc hu.continuousOn
    (Set.Icc_subset_uIcc ⟨hx, hy⟩)
  exact ⟨c, hc⟩

/-- **Risk aversion ⟺ certainty equivalent below the mean** (MWG Prop.
6.C.1, (i) ⟺ (iii)), for continuous strictly increasing `u`. -/
theorem riskAverse_iff_certaintyEquivalent_le_mean {u : ℝ → ℝ} (hc : Continuous u)
    (hm : StrictMono u) :
    RiskAverseOn u univ ↔ ∀ F c, IsCertaintyEquivalent u F c → c ≤ F.mean := by
  constructor
  · intro h F c hce
    exact hm.le_iff_le.1 (hce ▸ h F (subset_univ _))
  · intro h F _
    obtain ⟨c, hce⟩ := exists_certaintyEquivalent hc F
    rw [← hce]
    exact hm.monotone (h F c hce)

/-! ### Comparing risk aversion: Pratt's theorem -/

/-- `u₂` is **more risk averse** than `u₁` (MWG Def. 6.C.3 via (iii)): for
every lottery, `u₂`'s certainty equivalent is at most `u₁`'s. -/
def MoreRiskAverse (u₂ u₁ : ℝ → ℝ) : Prop :=
  ∀ F c₁ c₂, IsCertaintyEquivalent u₁ F c₁ → IsCertaintyEquivalent u₂ F c₂ → c₂ ≤ c₁

/-- **Pratt's theorem** (MWG Prop. 6.C.2, (ii) ⟺ (iii)). For continuous,
strictly increasing `u₁, u₂`: `u₂` is more risk averse than `u₁` iff
`u₂ = ψ ∘ u₁` for some increasing concave `ψ` (on the range of `u₁`). -/
theorem moreRiskAverse_iff {u₁ u₂ : ℝ → ℝ} (hc₁ : Continuous u₁) (hm₁ : StrictMono u₁)
    (hc₂ : Continuous u₂) (hm₂ : StrictMono u₂) :
    MoreRiskAverse u₂ u₁ ↔ ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (range u₁) ∧
      ConcaveOn ℝ (range u₁) ψ ∧ ∀ x, u₂ x = ψ (u₁ x) := by
  have hconv : Convex ℝ (range u₁) :=
    (isPreconnected_range hc₁).ordConnected.convex
  constructor
  · intro h
    -- `ψ = u₂ ∘ u₁⁻¹`.
    set ψ : ℝ → ℝ := fun t => u₂ (Function.invFun u₁ t) with hψ
    have hinv : ∀ x, Function.invFun u₁ (u₁ x) = x :=
      Function.leftInverse_invFun hm₁.injective
    have hψu : ∀ x, ψ (u₁ x) = u₂ x := fun x => by simp only [hψ, hinv]
    refine ⟨ψ, ?_, ⟨hconv, ?_⟩, fun x => (hψu x).symm⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      rw [hψu, hψu]
      exact hm₂ (hm₁.lt_iff_lt.1 hxy)
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb hab
      have hb' : b = 1 - a := by linarith
      subst hb'
      have ha1 : a ≤ 1 := by linarith
      -- The two-point lottery on `x, y` with weights `a, 1-a`.
      set F := twoPoint x y a ha ha1
      obtain ⟨c₁, hc₁'⟩ := exists_certaintyEquivalent hc₁ F
      obtain ⟨c₂, hc₂'⟩ := exists_certaintyEquivalent hc₂ F
      have hle := hm₂.monotone (h F c₁ c₂ hc₁' hc₂')
      have e1 : u₁ c₁ = a * u₁ x + (1 - a) * u₁ y := by rw [hc₁', expect_twoPoint]
      have e2 : u₂ c₂ = a * u₂ x + (1 - a) * u₂ y := by rw [hc₂', expect_twoPoint]
      simp only [smul_eq_mul]
      rw [hψu, hψu, ← e1, hψu, ← e2]
      exact hle
  · rintro ⟨ψ, -, hψc, hψ⟩ F c₁ c₂ hc₁' hc₂'
    -- `u₂(c₂) = E[ψ(u₁)] ≤ ψ(E[u₁]) = ψ(u₁(c₁)) = u₂(c₁)`.
    have hJ := hψc.le_map_sum (t := F.prob.support) (w := F.prob) (p := u₁)
      (fun x _ => F.nonneg x) F.sum_prob (fun x _ => mem_range_self x)
    simp only [smul_eq_mul] at hJ
    have : u₂ c₂ ≤ u₂ c₁ := by
      rw [hc₂', hψ c₁, hc₁', expect_eq_sum, expect_eq_sum]
      simpa only [hψ] using hJ
    exact hm₂.le_iff_le.1 this

/-! ### The Arrow–Pratt coefficient -/

/-- The **Arrow–Pratt coefficient of absolute risk aversion**
`r_A(x) = -u''(x)/u'(x)`. -/
noncomputable def arrowPratt (u : ℝ → ℝ) (x : ℝ) : ℝ := -deriv (deriv u) x / deriv u x

/-- **Risk aversion ⟺ nonnegative Arrow–Pratt coefficient** for a twice
differentiable, strictly increasing (`u' > 0`) Bernoulli utility. -/
theorem riskAverse_iff_arrowPratt_nonneg {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (hpos : ∀ x, 0 < deriv u x) :
    RiskAverseOn u univ ↔ ∀ x, 0 ≤ arrowPratt u x := by
  rw [riskAverseOn_iff_concaveOn convex_univ]
  have key : ∀ x, 0 ≤ arrowPratt u x ↔ deriv (deriv u) x ≤ 0 := fun x => by
    rw [arrowPratt, le_div_iff₀ (hpos x), zero_mul, neg_nonneg]
  simp only [key]
  constructor
  · intro hc x
    have hanti : AntitoneOn (deriv u) univ := hc.antitoneOn_deriv fun x _ => hu x
    exact (antitoneOn_univ.1 hanti).deriv_nonpos
  · intro h
    exact concaveOn_univ_of_deriv2_nonpos hu hu' fun x => by simpa using h x

/-- The mean of a lottery paying in a convex set lies in that set. -/
theorem SimpleLottery.mean_mem {F : SimpleLottery} {I : Set ℝ} (hI : Convex ℝ I)
    (hF : F.SupportedIn I) : F.mean ∈ I := by
  have h := hI.sum_mem (t := F.prob.support) (w := F.prob) (z := id) (fun x _ => F.nonneg x)
    F.sum_prob (fun x hx => hF hx)
  simpa [mean, expect_eq_sum, smul_eq_mul] using h

/-- A continuous `u` on a convex `I` gives every lottery paying in `I` a certainty
equivalent in `I`. -/
theorem exists_certaintyEquivalent_mem {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hu : ContinuousOn u I) {F : SimpleLottery} (hF : F.SupportedIn I) :
    ∃ c ∈ I, IsCertaintyEquivalent u F c := by
  obtain ⟨x, hx, y, hy, hxe, hye⟩ := F.exists_min_max_expect u
  have hsub : uIcc x y ⊆ I := hI.ordConnected.uIcc_subset (hF hx) (hF hy)
  obtain ⟨c, hc, hce⟩ := intermediate_value_uIcc (hu.mono hsub) (Set.Icc_subset_uIcc ⟨hxe, hye⟩)
  exact ⟨c, hsub hc, hce⟩

/-- **MWG Prop. 6.C.1 (i) ⟺ (iii) on an interval.** For `u` continuous and strictly
increasing on a convex set `I` of wealth levels (e.g. `(0, ∞)` for `log` or `√`): `u` is
risk averse on `I` iff every lottery paying in `I` has its certainty equivalents in `I`
below its mean. -/
theorem riskAverseOn_iff_certaintyEquivalent_le_mean {u : ℝ → ℝ} {I : Set ℝ}
    (hI : Convex ℝ I) (hc : ContinuousOn u I) (hm : StrictMonoOn u I) :
    RiskAverseOn u I ↔
      ∀ F : SimpleLottery, F.SupportedIn I → ∀ c ∈ I, IsCertaintyEquivalent u F c → c ≤ F.mean := by
  constructor
  · intro h F hF c hcI hce
    exact (hm.le_iff_le hcI (F.mean_mem hI hF)).1 (hce ▸ h F hF)
  · intro h F hF
    obtain ⟨c, hcI, hce⟩ := exists_certaintyEquivalent_mem hI hc hF
    rw [← hce]
    exact hm.monotoneOn hcI (F.mean_mem hI hF) (h F hF c hcI hce)

/-- **Risk aversion ⟺ nonnegative Arrow–Pratt coefficient, on an open interval** (MWG
§6.C). For `u` twice differentiable with `u' > 0` on an open convex `I` (such as
`(0, ∞)`, which covers `log`, `√` and CRRA utilities). -/
theorem riskAverseOn_iff_arrowPratt_nonneg {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (ho : IsOpen I) (hu : DifferentiableOn ℝ u I) (hu' : DifferentiableOn ℝ (deriv u) I)
    (hpos : ∀ x ∈ I, 0 < deriv u x) :
    RiskAverseOn u I ↔ ∀ x ∈ I, 0 ≤ arrowPratt u x := by
  rw [riskAverseOn_iff_concaveOn hI]
  have key : ∀ x ∈ I, 0 ≤ arrowPratt u x ↔ deriv (deriv u) x ≤ 0 := fun x hx => by
    rw [arrowPratt, le_div_iff₀ (hpos x hx), zero_mul, neg_nonneg]
  constructor
  · intro hc x hx
    rw [key x hx]
    have hanti : AntitoneOn (deriv u) I :=
      hc.antitoneOn_deriv fun y hy => hu.differentiableAt (ho.mem_nhds hy)
    rw [← derivWithin_of_isOpen ho hx]
    exact hanti.derivWithin_nonpos
  · intro h
    refine concaveOn_of_deriv2_nonpos hI hu.continuousOn (by rwa [ho.interior_eq])
      (by rwa [ho.interior_eq]) fun x hx => ?_
    rw [ho.interior_eq] at hx
    simpa using (key x hx).1 (h x hx)

/-- **Witness: log utility** is risk averse on `(0, ∞)`, with `r_A(x) = 1/x`. -/
example : (∀ x, 0 < x → arrowPratt Real.log x = 1 / x) ∧ RiskAverseOn Real.log (Ioi 0) := by
  have hd : deriv Real.log = fun x => x⁻¹ := Real.deriv_log'
  have hAP : ∀ x, 0 < x → arrowPratt Real.log x = 1 / x := by
    intro x hx
    rw [arrowPratt, hd, deriv_inv]
    field_simp
  refine ⟨hAP, (riskAverseOn_iff_arrowPratt_nonneg (convex_Ioi 0) isOpen_Ioi
    (Real.differentiableOn_log.mono fun x hx => ne_of_gt hx) ?_ ?_).2 fun x hx => ?_⟩
  · rw [hd]; exact differentiableOn_inv.mono fun x hx => ne_of_gt hx
  · intro x hx; rw [hd]; exact inv_pos.2 hx
  · rw [hAP x hx]; exact (one_div_pos.2 hx).le

/-- **Non-vacuity: CARA utility.** `u(x) = -e^{-a x}` with `a > 0` has
constant absolute risk aversion `r_A ≡ a`, and is risk averse. -/
example (a : ℝ) (ha : 0 < a) :
    (∀ x, arrowPratt (fun x => -Real.exp (-a * x)) x = a) ∧
      RiskAverseOn (fun x => -Real.exp (-a * x)) univ := by
  set u : ℝ → ℝ := fun x => -Real.exp (-a * x)
  have hl : ∀ x : ℝ, HasDerivAt (fun y => -a * y) (-a) x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (-a)
  have h1 : ∀ x, HasDerivAt u (a * Real.exp (-a * x)) x := fun x => by
    have := (hl x).exp.neg
    convert this using 1
    ring
  have hd1 : deriv u = fun x => a * Real.exp (-a * x) := funext fun x => (h1 x).deriv
  have h2 : ∀ x, HasDerivAt (deriv u) (-(a * a) * Real.exp (-a * x)) x := fun x => by
    rw [hd1]
    have := ((hl x).exp).const_mul a
    convert this using 1
    ring
  have hd2 : ∀ x, deriv (deriv u) x = -(a * a) * Real.exp (-a * x) := fun x => (h2 x).deriv
  have hAP : ∀ x, arrowPratt u x = a := fun x => by
    rw [arrowPratt, hd2, hd1]
    have := Real.exp_pos (-a * x)
    field_simp
  refine ⟨hAP, ?_⟩
  refine (riskAverse_iff_arrowPratt_nonneg (fun x => (h1 x).differentiableAt)
    (fun x => (h2 x).differentiableAt) fun x => ?_).2 fun x => (hAP x).symm ▸ ha.le
  rw [hd1]; exact mul_pos ha (Real.exp_pos _)

end Econ
