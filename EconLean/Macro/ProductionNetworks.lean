/-
# Production networks: Hulten's theorem, Domar weights and aggregate volatility

Hulten (1978); Long–Plosser (1983); Acemoglu, Carvalho, Ozdaglar and
Tahbaz-Salehi (2012), "The Network Origins of Aggregate Fluctuations",
Econometrica; Carvalho–Tahbaz-Salehi (2019), "Production Networks: A Primer", §2–3.

**The economy.** Sectors `i ∈ n`. Sector `i` produces with constant returns
`yᵢ = zᵢ · lᵢ^{αᵢ} · Πⱼ xᵢⱼ^{ωᵢⱼ}`, `αᵢ = 1 − Σⱼ ωᵢⱼ > 0`. A representative
household supplies one unit of labour and has Cobb–Douglas preferences with
expenditure shares `βᵢ ≥ 0`, `Σ βᵢ = 1`. The wage is the numeraire.

* **Prices.** With CRS, competitive prices equal unit cost. For a Cobb–Douglas
  technology the log unit cost is linear, so log prices `πᵢ = log pᵢ` solve
  `πᵢ = −log zᵢ + kᵢ + Σⱼ ωᵢⱼ πⱼ` with `kᵢ = −αᵢ log αᵢ − Σⱼ ωᵢⱼ log ωᵢⱼ`
  (`IsPriceSystem`). `existsUnique_price`: a unique solution exists because the
  input–output matrix `Ω` has row sums `< 1` (`I − Ω` is invertible).
* **Real GDP** is the wage divided by the Cobb–Douglas consumer price index,
  `log Y = Σ βᵢ log βᵢ − Σ βᵢ πᵢ` (`logGDP`).
* **Domar weights** `λ = β'(I − Ω)⁻¹` (`domar`). Goods-market clearing with
  Cobb–Douglas spending (`IsSales`: `Sᵢ = βᵢ + Σⱼ ωⱼᵢ Sⱼ`, sales over nominal
  GDP `= 1`) has the unique solution `S = λ` (`isSales_iff`): `λᵢ` is sector
  `i`'s sales over GDP. `domar_nonneg`; `sum_domar_mul_α` (`Σ λᵢαᵢ = 1`);
  `one_le_sum_domar`: Domar weights sum to at least 1.

**Results.**
* `hulten`: for any two productivity vectors, `log Y(z') − log Y(z) = Σᵢ λᵢ (log z'ᵢ − log zᵢ)`:
  the elasticity of real GDP to sector `i`'s productivity is its Domar weight,
  globally in the Cobb–Douglas case (Hulten's theorem).
* `aggVar`: with independent sectoral log-productivity shocks of variance `σ²`,
  aggregate log-GDP variance is `σ² Σ λᵢ²` (Acemoglu et al. 2012, eq. (4)).
  `aggVar_symmetric`: with `n` symmetric sectors and no intermediates it is
  `σ²/n` (diversification), and `aggVar_ge_div` shows `σ²/n` is a lower bound
  for every network. `aggVar_ge`: it is at least `σ² λᵢ²` for every sector. `star_domar`, `star_aggVar_ge`: in a **star network** where every
  sector uses the hub's output with share `a`, the hub's Domar weight is
  `(1 + a m)/(m + 1)` (with `m` spokes), so aggregate volatility stays
  at least `σ a/2` however many sectors there are (micro shocks do not wash out).

**Deviations.** Cobb–Douglas technologies and preferences (log-linear economy);
labour is the only primary factor. Prices are defined by the zero-profit
(unit-cost) conditions rather than derived from firms' cost minimization;
sales by the market-clearing identities. The variance formula `σ² Σ λᵢ²` is
used as the definition of aggregate volatility (it is the variance of
`Σ λᵢ εᵢ` for uncorrelated shocks); no probability space is set up.
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Order
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

noncomputable section

namespace Econ
namespace ProdNetworks

open Matrix Finset Real

/-- A Cobb–Douglas production network. -/
structure Network (n : Type*) [Fintype n] where
  /-- Input–output shares `ωᵢⱼ` (sector `i` buys from sector `j`). -/
  Ω : Matrix n n ℝ
  /-- Household expenditure shares. -/
  β : n → ℝ
  hΩ : ∀ i j, 0 ≤ Ω i j
  /-- Labour shares `αᵢ = 1 − Σⱼ ωᵢⱼ` are positive. -/
  hrow : ∀ i, ∑ j, Ω i j < 1
  hβ : ∀ i, 0 ≤ β i
  sum_β : ∑ i, β i = 1

namespace Network

variable {n : Type*} [Fintype n] [DecidableEq n] (N : Network n)

/-- Labour share of sector `i`. -/
def α (i : n) : ℝ := 1 - ∑ j, N.Ω i j

/-- Constant in the log unit-cost function. -/
def k (i : n) : ℝ := -(N.α i * log (N.α i)) - ∑ j, N.Ω i j * log (N.Ω i j)

/-- Log prices are a **price system** if each equals log unit cost. -/
def IsPriceSystem (z : n → ℝ) (π : n → ℝ) : Prop :=
  ∀ i, π i = -log (z i) + N.k i + ∑ j, N.Ω i j * π j

omit [DecidableEq n] in
/-- If `δ = Ω δ` then `δ = 0` (row sums `< 1`). -/
theorem eq_zero_of_fixed {δ : n → ℝ} (h : ∀ i, δ i = ∑ j, N.Ω i j * δ j) : δ = 0 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact funext fun i => hn.elim i
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => |δ i|
  have hb : |δ i₀| ≤ (∑ j, N.Ω i₀ j) * |δ i₀| := by
    calc |δ i₀| = |∑ j, N.Ω i₀ j * δ j| := by rw [← h i₀]
      _ ≤ ∑ j, |N.Ω i₀ j * δ j| := abs_sum_le_sum_abs _ _
      _ = ∑ j, N.Ω i₀ j * |δ j| := sum_congr rfl fun j _ => by
          rw [abs_mul, abs_of_nonneg (N.hΩ _ _)]
      _ ≤ ∑ j, N.Ω i₀ j * |δ i₀| := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hi₀ j) (N.hΩ _ _)
      _ = _ := by rw [sum_mul]
  have hr := N.hrow i₀
  have h0 : |δ i₀| = 0 := by nlinarith [abs_nonneg (δ i₀), sum_nonneg fun j (_ : j ∈ univ) => N.hΩ i₀ j]
  funext i
  have := hi₀ i
  rw [h0] at this
  exact abs_nonpos_iff.1 this

/-- `I − Ω` is invertible (the **Leontief inverse** exists). -/
theorem isUnit_det : IsUnit (1 - N.Ω).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, h⟩ := exists_mulVec_eq_zero_iff.2 h0
  apply hv
  refine N.eq_zero_of_fixed fun i => ?_
  have := congrFun h i
  simp only [sub_mulVec, one_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  simpa [mulVec, dotProduct] using this

/-- The Leontief inverse `L = (I − Ω)⁻¹`. -/
def L : Matrix n n ℝ := (1 - N.Ω)⁻¹

/-- **Domar weights** `λ = β'(I − Ω)⁻¹`. -/
def domar : n → ℝ := N.β ᵥ* N.L

/-- Log real GDP given log prices (wage = 1): minus the log CPI. -/
def logGDP (π : n → ℝ) : ℝ := ∑ i, N.β i * log (N.β i) - ∑ i, N.β i * π i

theorem isPriceSystem_iff (z π : n → ℝ) :
    N.IsPriceSystem z π ↔ (1 - N.Ω) *ᵥ π = fun i => -log (z i) + N.k i := by
  simp only [IsPriceSystem, funext_iff, sub_mulVec, one_mulVec, Pi.sub_apply]
  refine forall_congr' fun i => ?_
  simp only [mulVec, dotProduct]
  constructor <;> intro h <;> linarith

/-- **Existence and uniqueness of equilibrium prices.** -/
theorem existsUnique_price (z : n → ℝ) : ∃! π, N.IsPriceSystem z π := by
  refine ⟨N.L *ᵥ fun i => -log (z i) + N.k i, ?_, fun π hπ => ?_⟩
  · show N.IsPriceSystem z _
    rw [isPriceSystem_iff, L, mulVec_mulVec, mul_nonsing_inv _ N.isUnit_det, one_mulVec]
  · replace hπ : N.IsPriceSystem z π := hπ
    rw [isPriceSystem_iff] at hπ
    rw [← hπ, L, mulVec_mulVec, nonsing_inv_mul _ N.isUnit_det, one_mulVec]

/-- **Hulten's theorem (Cobb–Douglas networks).** For any productivity vectors
`z, z' ≫ 0` and their equilibrium prices, the change in log real GDP is the
Domar-weighted sum of the changes in log productivity. (Positivity of `z`
is the economic domain; the proof is linear algebra in log prices and does not
use it.) -/
theorem hulten {z z' π π' : n → ℝ} (_hz : ∀ i, 0 < z i) (_hz' : ∀ i, 0 < z' i)
    (hπ : N.IsPriceSystem z π) (hπ' : N.IsPriceSystem z' π') :
    N.logGDP π' - N.logGDP π = ∑ i, N.domar i * (log (z' i) - log (z i)) := by
  rw [isPriceSystem_iff] at hπ hπ'
  have hd : π' - π = N.L *ᵥ fun i => -(log (z' i) - log (z i)) := by
    have : (1 - N.Ω) *ᵥ (π' - π) = fun i => -(log (z' i) - log (z i)) := by
      rw [mulVec_sub, hπ, hπ']; funext i; simp; ring
    rw [← this, L, mulVec_mulVec, nonsing_inv_mul _ N.isUnit_det, one_mulVec]
  have e : N.logGDP π' - N.logGDP π = -(N.β ⬝ᵥ (π' - π)) := by
    simp only [logGDP, dotProduct, Pi.sub_apply, mul_sub, sum_sub_distrib]; ring
  rw [e, hd, dotProduct_mulVec, domar]
  simp only [dotProduct, mul_neg, sum_neg_distrib, neg_neg]

/-- Sales over nominal GDP satisfy **goods-market clearing**: sector `i` sells
`βᵢ` to the household and the share `ωⱼᵢ` of every sector `j`'s sales. -/
def IsSales (S : n → ℝ) : Prop := ∀ i, S i = N.β i + ∑ j, N.Ω j i * S j

/-- **Domar weights are sales shares.** The market-clearing sales vector is
unique and equals `λ`. -/
theorem isSales_iff (S : n → ℝ) : N.IsSales S ↔ S = N.domar := by
  have hT : IsUnit (1 - N.Ωᵀ).det := by
    rw [show (1 - N.Ωᵀ) = (1 - N.Ω)ᵀ by simp, det_transpose]; exact N.isUnit_det
  have key : N.IsSales S ↔ S ᵥ* (1 - N.Ω) = N.β := by
    simp only [IsSales, funext_iff, vecMul_sub, vecMul_one, Pi.sub_apply]
    refine forall_congr' fun i => ?_
    simp only [vecMul, dotProduct]
    rw [show ∑ x, S x * N.Ω x i = ∑ j, N.Ω j i * S j from
      sum_congr rfl fun _ _ => mul_comm _ _]
    constructor <;> intro h <;> linarith
  rw [key, domar, L]
  constructor
  · rintro h; rw [← h, vecMul_vecMul, mul_nonsing_inv _ N.isUnit_det, vecMul_one]
  · rintro rfl; rw [vecMul_vecMul, nonsing_inv_mul _ N.isUnit_det, vecMul_one]

theorem isSales_domar : N.IsSales N.domar := (N.isSales_iff _).2 rfl

omit [DecidableEq n] in
/-- Any market-clearing sales vector is non-negative. The negative part
`w = min(S, 0)` satisfies `w ≥ Ω'w`; summing gives `Σⱼ wⱼ αⱼ ≥ 0`, which forces
`w = 0` because labour shares are positive. -/
theorem nonneg_of_isSales {S : n → ℝ} (hS : N.IsSales S) (i : n) : 0 ≤ S i := by
  set w : n → ℝ := fun i => min (S i) 0 with hw
  have hw0 : ∀ i, w i ≤ 0 := fun i => min_le_right _ _
  have hge : ∀ i, ∑ j, N.Ω j i * w j ≤ w i := by
    intro i
    have h1 : ∑ j, N.Ω j i * w j ≤ ∑ j, N.Ω j i * S j :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (N.hΩ _ _)
    have h2 : ∑ j, N.Ω j i * w j ≤ 0 :=
      sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (N.hΩ _ _) (hw0 j)
    have h3 := hS i
    have h4 := N.hβ i
    simp only [hw, le_min_iff]
    exact ⟨by linarith, h2⟩
  have hsum : ∑ j, w j * (1 - ∑ i, N.Ω j i) ≥ 0 := by
    have : ∑ i, ∑ j, N.Ω j i * w j ≤ ∑ i, w i := sum_le_sum fun i _ => hge i
    rw [sum_comm] at this
    simp only [mul_sub, mul_one, sum_sub_distrib, mul_sum]
    have e : ∑ y, ∑ x, w y * N.Ω y x = ∑ y, ∑ x, N.Ω y x * w y :=
      sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => mul_comm _ _
    rw [e]; linarith
  have hterm : ∀ j, w j * (1 - ∑ i, N.Ω j i) ≤ 0 := fun j =>
    mul_nonpos_of_nonpos_of_nonneg (hw0 j) (by linarith [N.hrow j])
  have hz : w i * (1 - ∑ k, N.Ω i k) = 0 := by
    have := (sum_eq_zero_iff_of_nonpos fun j _ => hterm j).1
      (le_antisymm (sum_nonpos fun j _ => hterm j) hsum) i (mem_univ _)
    exact this
  have hpos : 0 < 1 - ∑ k, N.Ω i k := by linarith [N.hrow i]
  have : w i = 0 := by
    rcases mul_eq_zero.1 hz with h | h
    · exact h
    · linarith
  have : min (S i) 0 = 0 := this
  rw [min_eq_right_iff] at this
  exact this

/-- Domar weights are non-negative. -/
theorem domar_nonneg (i : n) : 0 ≤ N.domar i := N.nonneg_of_isSales N.isSales_domar i

/-- **Domar weights sum to at least one** (sales exceed value added when there
are intermediate inputs): `Σ λᵢ αᵢ = Σ βᵢ = 1` with `αᵢ ≤ 1`. -/
theorem sum_domar_mul_α : ∑ i, N.domar i * N.α i = 1 := by
  have h := N.isSales_domar
  have : ∑ i, N.domar i = ∑ i, N.β i + ∑ i, ∑ j, N.Ω j i * N.domar j := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => h i
  rw [sum_comm, N.sum_β] at this
  simp only [α, mul_sub, mul_one, sum_sub_distrib, mul_sum]
  have e : ∑ i, ∑ j, N.domar i * N.Ω i j = ∑ y, ∑ x, N.Ω y x * N.domar y :=
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => mul_comm _ _
  rw [e]; linarith

theorem one_le_sum_domar : 1 ≤ ∑ i, N.domar i := by
  rw [← N.sum_domar_mul_α]
  refine sum_le_sum fun i _ => ?_
  have h0 : 0 ≤ ∑ j, N.Ω i j := sum_nonneg fun j _ => N.hΩ i j
  have := N.domar_nonneg i
  simp only [α]; nlinarith

/-- **Aggregate volatility** (Acemoglu et al. 2012, eq. (4)): the variance of
`Δ log Y = Σ λᵢ εᵢ` (by `hulten`) when sectoral log-productivity shocks `εᵢ`
are i.i.d. with variance `σ²` is `σ² Σ λᵢ²`. This value is the definition; no
probability space is constructed. -/
def aggVar (σ : ℝ) : ℝ := σ ^ 2 * ∑ i, N.domar i ^ 2

/-- **No diversification past the largest Domar weight.** -/
theorem aggVar_ge (σ : ℝ) (i : n) : σ ^ 2 * N.domar i ^ 2 ≤ N.aggVar σ := by
  unfold aggVar
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (f := fun j => N.domar j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i))
    (sq_nonneg σ)

/-- **Diversification bound.** Volatility is at least `σ²/n`: by Cauchy–Schwarz
and `Σ λᵢ ≥ 1`. Equality holds in the symmetric economy without intermediates. -/
theorem aggVar_ge_div (σ : ℝ) [Nonempty n] : σ ^ 2 / Fintype.card n ≤ N.aggVar σ := by
  have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have cs : (∑ i, N.domar i) ^ 2 ≤ Fintype.card n * ∑ i, N.domar i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := N.domar)
  have h1 := N.one_le_sum_domar
  have : 1 ≤ Fintype.card n * ∑ i, N.domar i ^ 2 := by nlinarith
  unfold aggVar
  rw [div_le_iff₀ hc]
  nlinarith [sq_nonneg σ]

end Network

/-! ### Two benchmark networks -/

/-- The **symmetric economy without intermediates**: `n` sectors, `Ω = 0`, equal
expenditure shares. -/
def symmetric (n : Type*) [Fintype n] [Nonempty n] : Network n where
  Ω := 0
  β := fun _ => 1 / Fintype.card n
  hΩ := fun _ _ => le_rfl
  hrow := fun _ => by simp
  hβ := fun _ => by positivity
  sum_β := by
    have : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [this]

/-- In the symmetric economy, volatility is `σ²/n`: independent micro shocks
wash out at rate `1/√n` (the diversification benchmark). -/
theorem aggVar_symmetric (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] (σ : ℝ) :
    (symmetric n).aggVar σ = σ ^ 2 / Fintype.card n := by
  have hS : (symmetric n).domar = fun _ => (1 : ℝ) / Fintype.card n := by
    refine (((symmetric n).isSales_iff _).1 fun i => ?_).symm
    simp [symmetric]
  have : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Network.aggVar, hS, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- A **star network**: a hub sector (`none`) and `m` spokes (`some k`); every
spoke buys the hub's output with input share `a`; the household spends equally
on all `m + 1` goods. -/
def star (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) : Network (Option (Fin m)) where
  Ω := fun i j => if i.isSome ∧ j = none then a else 0
  β := fun _ => 1 / (m + 1)
  hΩ := fun i j => by split_ifs <;> simp [ha]
  hrow := fun i => by
    cases i with
    | none => simp
    | some k =>
      rw [Fintype.sum_option]
      simp [ha1]
  hβ := fun _ => by positivity
  sum_β := by
    rw [Fintype.sum_option]; simp; field_simp; ring

/-- The hub's Domar weight in the star network is `(1 + a m)/(m + 1)`. -/
theorem star_domar (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (star m a ha ha1).domar none = (1 + a * m) / (m + 1) := by
  have hS : (star m a ha ha1).IsSales
      (fun i => if i = none then (1 + a * m) / (m + 1) else 1 / (m + 1)) := by
    intro i
    cases i with
    | none =>
      rw [Fintype.sum_option]; simp [star]; field_simp
    | some k =>
      rw [Fintype.sum_option]; simp [star]
  rw [← ((star m a ha ha1).isSales_iff _).1 hS]; simp

/-- **Networks defeat diversification.** In a star network with at least one
spoke, aggregate volatility is at least `σ² a²/4` for every number of sectors:
the hub's shock is transmitted to all spokes and never averages out. -/
theorem star_aggVar_ge (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 0 ≤ a) (_ha0 : 0 < a) (ha1 : a < 1) (σ : ℝ) :
    σ ^ 2 * a ^ 2 / 4 ≤ (star m a ha ha1).aggVar σ := by
  refine le_trans ?_ ((star m a ha ha1).aggVar_ge σ none)
  rw [star_domar]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m + 1 := by positivity
  have hl : a / 2 ≤ (1 + a * m) / (m + 1) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have h0 : 0 ≤ a / 2 := by positivity
  have := pow_le_pow_left₀ h0 hl 2
  have hs := sq_nonneg σ
  calc σ ^ 2 * a ^ 2 / 4 = σ ^ 2 * (a / 2) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hs
end ProdNetworks
end Econ

end
