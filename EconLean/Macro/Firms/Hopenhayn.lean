/-
# Hopenhayn (1992): firm dynamics in stationary equilibrium

Hopenhayn, "Entry, Exit, and Firm Dynamics in Long Run Equilibrium",
Econometrica 60 (1992). The exit decision is taken after production, as in
Hopenhayn (1992) and Hopenhayn–Rogerson (1993); the exogenous death shock `δ > 0`
is the common textbook device that keeps the stationary firm mass finite.

**The model** (finite productivity states `X`). The output price is `p`. A firm
with productivity `x` earns per-period profit `π p x` (net of the fixed
operating cost, so it may be negative) and produces `s p x > 0`. Productivity
follows a Markov chain `Q x x'`. After producing, a firm dies exogenously with
probability `δ`; a survivor then decides whether to continue (and draw `x'`)
or exit with value `0`. Entrants pay `cₑ`, draw `x ~ ν`, and produce at once.
Market demand is `D p > 0`. Prices are positive; monotonicity of profits and
positivity of output and demand are only assumed at positive prices.

**Incumbent value.** `V_p(x) = π p x + β(1-δ) max(E[V_p(x') | x], 0)`, the
unique fixed point of a `β(1-δ)`-contraction (`V_eq`). A surviving firm
continues iff `E[V_p(x') | x] ≥ 0` (`stays`; indifferent firms stay, and the
uniqueness results below are for this tie-breaking rule).

**Stationary equilibrium** (`IsEquilibrium`): a price `p`, an entry mass
`M > 0`, and a firm distribution `μ` with
* free entry: `Σ ν(x) V_p(x) = cₑ`;
* stationarity: `μ(x') = Σ_x μ(x)(1-δ)·1[stays]·Q x x' + M ν(x')`;
* market clearing: `Σ μ(x) s p x = D p`.

**Results.**
* `V_monotone_price`, `entryValue_strictMono`, `continuous_V`: values rise
  strictly (at positive prices) and continuously with the price.
* `stays_isUpperSet`: if profits rise with productivity and `Q` is monotone
  (persistence in the FOSD sense), exit follows a cutoff rule: the set of
  continuing states is an upper set (Hopenhayn's selection).
* `exists_unique_stationary`: for every price and entry mass the stationary
  distribution exists, is unique and is linear in `M`; it is nonnegative
  for `M ≥ 0` (`stationary_nonneg`).
* `exists_unique_equilibrium`: if some positive price makes every state
  unprofitable and some positive price makes expected entry profit at least
  `cₑ`, there is exactly one stationary equilibrium `(p, M, μ)`, and in it
  `μ ≥ 0`.

**Scope.** Finite productivity states, exogenous exit `δ > 0` (which makes the
firm distribution well defined), price-taking firms with reduced-form profit
and supply functions (`s` is not derived from `π`). Hopenhayn's general state space and his comparative
statics in `cₑ` are not formalized.
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace Econ

namespace Hopenhayn

open Filter Topology Set Finset Function

/-- Primitives of the Hopenhayn model on finitely many productivity states. -/
structure Model (X : Type*) [Fintype X] where
  /-- Discount factor. -/
  β : ℝ
  /-- Exogenous exit probability. -/
  δ : ℝ
  /-- Entry cost. -/
  ce : ℝ
  /-- Productivity transition probabilities. -/
  Q : X → X → ℝ
  /-- Distribution of entrants' productivity. -/
  ν : X → ℝ
  /-- Profit at output price `p` in state `x`, net of fixed operating cost. -/
  π : ℝ → X → ℝ
  /-- Output at price `p` in state `x`. -/
  s : ℝ → X → ℝ
  /-- Market demand. -/
  D : ℝ → ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  ce_pos : 0 < ce
  Q_nonneg : ∀ x x', 0 ≤ Q x x'
  Q_sum : ∀ x, ∑ x', Q x x' = 1
  ν_nonneg : ∀ x, 0 ≤ ν x
  ν_sum : ∑ x, ν x = 1
  π_cont : ∀ x, Continuous fun p => π p x
  π_strictMono : ∀ x, StrictMonoOn (fun p => π p x) (Ioi 0)
  s_pos : ∀ p, 0 < p → ∀ x, 0 < s p x
  D_pos : ∀ p, 0 < p → 0 < D p

variable {X : Type*} [Fintype X]

namespace Model

variable (m : Model X)

/-- Effective discount factor `ρ = β(1-δ)`. -/
def ρ : ℝ := m.β * (1 - m.δ)

theorem ρ_nonneg : 0 ≤ m.ρ := mul_nonneg m.β_pos.le (by linarith [m.δ_le_one])

theorem ρ_lt_one : m.ρ < 1 := by
  unfold ρ; nlinarith [m.β_pos, m.β_lt_one, m.δ_pos, m.δ_le_one]

/-- Conditional expectation `E[v(x') | x]`. -/
def EQ (v : X → ℝ) (x : X) : ℝ := ∑ x', m.Q x x' * v x'

/-- The incumbent's Bellman operator at price `p`. -/
def bellman (p : ℝ) (v : X → ℝ) : X → ℝ := fun x => m.π p x + m.ρ * max (m.EQ v x) 0

theorem abs_EQ_sub_le (v w : X → ℝ) (x : X) : |m.EQ v x - m.EQ w x| ≤ dist v w := by
  unfold EQ
  rw [← sum_sub_distrib]
  calc |∑ x', (m.Q x x' * v x' - m.Q x x' * w x')|
      ≤ ∑ x', |m.Q x x' * v x' - m.Q x x' * w x'| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', m.Q x x' * dist v w := sum_le_sum fun x' _ => by
        rw [← mul_sub, abs_mul, abs_of_nonneg (m.Q_nonneg x x')]
        refine mul_le_mul_of_nonneg_left ?_ (m.Q_nonneg x x')
        have := dist_le_pi_dist v w x'
        rwa [Real.dist_eq] at this
    _ = dist v w := by rw [← sum_mul, m.Q_sum, one_mul]

theorem EQ_mono {v w : X → ℝ} (h : v ≤ w) (x : X) : m.EQ v x ≤ m.EQ w x :=
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (h x') (m.Q_nonneg x x')

theorem bellman_contracting (p : ℝ) : ContractingWith (Real.toNNReal m.ρ) (m.bellman p) := by
  refine ⟨by rw [Real.toNNReal_lt_one]; exact m.ρ_lt_one, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [Real.coe_toNNReal _ m.ρ_nonneg]
  refine (dist_pi_le_iff (mul_nonneg m.ρ_nonneg dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq]
  have e : m.bellman p v x - m.bellman p w x = m.ρ * (max (m.EQ v x) 0 - max (m.EQ w x) 0) := by
    unfold bellman; ring
  rw [e, abs_mul, abs_of_nonneg m.ρ_nonneg]
  exact mul_le_mul_of_nonneg_left ((abs_max_sub_max_le_abs _ _ _).trans (m.abs_EQ_sub_le v w x))
    m.ρ_nonneg

/-- The incumbent value function at price `p`. -/
noncomputable def V (p : ℝ) : X → ℝ :=
  ContractingWith.fixedPoint (m.bellman p) (m.bellman_contracting p)

theorem V_fixed (p : ℝ) : m.bellman p (m.V p) = m.V p :=
  ContractingWith.fixedPoint_isFixedPt (f := m.bellman p) (m.bellman_contracting p)

/-- **Incumbent Bellman equation.** -/
theorem V_eq (p : ℝ) (x : X) : m.V p x = m.π p x + m.ρ * max (m.EQ (m.V p) x) 0 :=
  (congrFun (m.V_fixed p) x).symm

/-- `V_p` is the only solution of the Bellman equation. -/
theorem V_unique (p : ℝ) (v : X → ℝ) (hv : ∀ x, v x = m.π p x + m.ρ * max (m.EQ v x) 0) :
    v = m.V p :=
  ContractingWith.fixedPoint_unique (f := m.bellman p) (m.bellman_contracting p)
    (funext fun x => (hv x).symm)

/-- A fixed point of a contraction lies in every closed set that the map
preserves and that meets the space. -/
theorem fixedPoint_mem {f : (X → ℝ) → X → ℝ} {K} (hf : ContractingWith K f) {S : Set (X → ℝ)}
    (hS : IsClosed S) {v : X → ℝ} (hv : v ∈ S) (hmap : MapsTo f S S) :
    ContractingWith.fixedPoint f hf ∈ S :=
  hS.mem_of_tendsto (ContractingWith.tendsto_iterate_fixedPoint hf v)
    (Eventually.of_forall fun n => hmap.iterate n hv)

theorem le_V (p : ℝ) (x : X) : m.π p x ≤ m.V p x := by
  rw [m.V_eq]; nlinarith [m.ρ_nonneg, le_max_right (m.EQ (m.V p) x) 0]

/-- Values rise with the price. -/
theorem V_monotone_price {p p' : ℝ} (hp : 0 < p) (h : p ≤ p') : m.V p ≤ m.V p' := by
  have hS : IsClosed {v : X → ℝ | v ≤ m.V p'} := isClosed_le continuous_id continuous_const
  refine fixedPoint_mem (m.bellman_contracting _) hS (le_refl (m.V p')) fun v (hv : v ≤ m.V p') x => ?_
  rw [m.V_eq p' x]
  show m.π p x + m.ρ * max (m.EQ v x) 0 ≤ _
  have h1 : m.π p x ≤ m.π p' x :=
    (m.π_strictMono x).monotoneOn (mem_Ioi.2 hp) (mem_Ioi.2 (hp.trans_le h)) h
  have h2 : max (m.EQ v x) 0 ≤ max (m.EQ (m.V p') x) 0 := max_le_max (m.EQ_mono hv x) le_rfl
  have := mul_le_mul_of_nonneg_left h2 m.ρ_nonneg
  linarith

/-- Strict version: `V_{p'}(x) - V_p(x) ≥ π(p', x) - π(p, x) > 0`. -/
theorem V_strictMono_price {p p' : ℝ} (hp : 0 < p) (h : p < p') (x : X) :
    m.V p x < m.V p' x := by
  rw [m.V_eq p x, m.V_eq p' x]
  have h1 : m.π p x < m.π p' x := m.π_strictMono x (mem_Ioi.2 hp) (mem_Ioi.2 (hp.trans h)) h
  have h2 : max (m.EQ (m.V p) x) 0 ≤ max (m.EQ (m.V p') x) 0 :=
    max_le_max (m.EQ_mono (m.V_monotone_price hp h.le) x) le_rfl
  have := mul_le_mul_of_nonneg_left h2 m.ρ_nonneg
  linarith

/-- `‖V_p - V_{p'}‖ ≤ ‖π_p - π_{p'}‖ / (1 - β(1-δ))`. -/
theorem dist_V_le (p p' : ℝ) : dist (m.V p) (m.V p') ≤ dist (m.π p) (m.π p') / (1 - m.ρ) := by
  have h := ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le' (m.bellman_contracting p)
    (m.bellman p') (m.V_fixed p) (m.V_fixed p') (C := dist (m.π p) (m.π p')) fun v => by
      refine (dist_pi_le_iff dist_nonneg).2 fun x => ?_
      rw [Real.dist_eq]
      have := dist_le_pi_dist (m.π p) (m.π p') x
      rw [Real.dist_eq] at this
      unfold bellman
      simpa using this
  rwa [Real.coe_toNNReal _ m.ρ_nonneg] at h

theorem continuous_π : Continuous m.π := continuous_pi fun x => m.π_cont x

/-- Values are continuous in the price. -/
theorem continuous_V : Continuous m.V := by
  have h1 : 0 < 1 - m.ρ := by linarith [m.ρ_lt_one]
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hπ : Tendsto (fun q => dist (m.π q) (m.π p) / (1 - m.ρ)) (𝓝 p) (𝓝 0) := by
    have := ((m.continuous_π.tendsto p).dist (tendsto_const_nhds (x := m.π p))).div_const (1 - m.ρ)
    simpa using this
  exact squeeze_zero (fun _ => dist_nonneg) (fun q => m.dist_V_le q p) hπ

/-- Expected value of entering, before the productivity draw. -/
noncomputable def entryValue (p : ℝ) : ℝ := ∑ x, m.ν x * m.V p x

theorem exists_ν_pos : ∃ x, 0 < m.ν x := by
  by_contra h
  have : ∑ x, m.ν x ≤ 0 := sum_nonpos fun x _ => not_lt.1 fun hx => h ⟨x, hx⟩
  linarith [m.ν_sum]

theorem entryValue_strictMono : StrictMonoOn m.entryValue (Ioi 0) := fun p hp p' _ h => by
  obtain ⟨x₀, hx₀⟩ := m.exists_ν_pos
  refine sum_lt_sum
    (fun x _ => mul_le_mul_of_nonneg_left (m.V_monotone_price hp h.le x) (m.ν_nonneg x))
    ⟨x₀, mem_univ _, mul_lt_mul_of_pos_left (m.V_strictMono_price hp h x₀) hx₀⟩

theorem continuous_entryValue : Continuous m.entryValue :=
  continuous_finsetSum _ fun x _ => continuous_const.mul ((continuous_apply x).comp m.continuous_V)

/-- If every state is unprofitable at `p`, incumbents' values are nonpositive. -/
theorem V_nonpos {p : ℝ} (hp : ∀ x, m.π p x ≤ 0) : m.V p ≤ 0 := by
  have hS : IsClosed {v : X → ℝ | v ≤ 0} := isClosed_le continuous_id continuous_const
  refine fixedPoint_mem (m.bellman_contracting _) hS (le_refl (0 : X → ℝ)) fun v (hv : v ≤ 0) x => ?_
  show m.π p x + m.ρ * max (m.EQ v x) 0 ≤ 0
  have : m.EQ v x ≤ 0 := by simpa [EQ] using m.EQ_mono hv x
  rw [max_eq_right this, mul_zero, add_zero]
  exact hp x

/-- **Free-entry price.** Under the boundary conditions there is exactly one
positive price at which expected entry value equals the entry cost. -/
theorem exists_unique_entry_price {plo phi : ℝ} (hplo : 0 < plo) (hphi : 0 < phi)
    (hlo : ∀ x, m.π plo x ≤ 0) (hhi : m.ce ≤ ∑ x, m.ν x * m.π phi x) :
    ∃! p, 0 < p ∧ m.entryValue p = m.ce := by
  have hElo : m.entryValue plo ≤ 0 :=
    sum_nonpos fun x _ => mul_nonpos_of_nonneg_of_nonpos (m.ν_nonneg x) (m.V_nonpos hlo x)
  have hEhi : m.ce ≤ m.entryValue phi :=
    hhi.trans (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (m.le_V phi x) (m.ν_nonneg x))
  have hle : plo ≤ phi := by
    by_contra h
    have := m.entryValue_strictMono hphi hplo (not_le.1 h)
    linarith [m.ce_pos]
  obtain ⟨p, hpI, hp⟩ := intermediate_value_Icc hle m.continuous_entryValue.continuousOn
    ⟨hElo.trans m.ce_pos.le, hEhi⟩
  have hp0 : 0 < p := hplo.trans_le hpI.1
  exact ⟨p, ⟨hp0, hp⟩, fun q ⟨hq0, hq⟩ =>
    m.entryValue_strictMono.injOn hq0 hp0 (hq.trans hp.symm)⟩

/-! ### Exit -/

/-- A surviving firm in state `x` continues iff its expected continuation value
is nonnegative. -/
def stays (p : ℝ) (x : X) : Prop := 0 ≤ m.EQ (m.V p) x

/-- **Cutoff exit rule (selection).** If profits rise with productivity and the
transition is monotone, the continuation set is an upper set. -/
theorem stays_isUpperSet [Preorder X] (hπ : ∀ p, Monotone (m.π p))
    (hQ : ∀ v : X → ℝ, Monotone v → Monotone (m.EQ v)) (p : ℝ) :
    IsUpperSet {x | m.stays p x} := by
  have hS : IsClosed {v : X → ℝ | Monotone v} := by
    have : {v : X → ℝ | Monotone v} = ⋂ a, ⋂ b, ⋂ (_ : a ≤ b), {v | v a ≤ v b} := by
      ext v; simp [Monotone]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply a) (continuous_apply b)
  have hV : Monotone (m.V p) :=
    fixedPoint_mem (m.bellman_contracting _) hS (show Monotone (0 : X → ℝ) from fun _ _ _ => le_rfl)
      (fun v (hv : Monotone v) a b hab => by
        show m.π p a + m.ρ * max (m.EQ v a) 0 ≤ m.π p b + m.ρ * max (m.EQ v b) 0
        have h1 := hπ p hab
        have h2 := mul_le_mul_of_nonneg_left (max_le_max (hQ v hv hab) (le_refl (0 : ℝ)))
          m.ρ_nonneg
        linarith)
  exact fun a b hab (ha : 0 ≤ _) => le_trans ha (hQ _ hV hab)

/-! ### The stationary firm distribution -/

open Classical in
/-- Transition of incumbents: survive (`1-δ`), continue, and draw `x'`. -/
noncomputable def A (p : ℝ) (x x' : X) : ℝ :=
  (1 - m.δ) * (if m.stays p x then 1 else 0) * m.Q x x'

theorem A_nonneg (p : ℝ) (x x' : X) : 0 ≤ m.A p x x' := by
  unfold A
  have : 0 ≤ 1 - m.δ := by linarith [m.δ_le_one]
  split_ifs <;> simp [mul_nonneg this (m.Q_nonneg x x')]

theorem sum_A_le (p : ℝ) (x : X) : ∑ x', m.A p x x' ≤ 1 - m.δ := by
  unfold A
  rw [← mul_sum, m.Q_sum, mul_one]
  have : 0 ≤ 1 - m.δ := by linarith [m.δ_le_one]
  split_ifs <;> simp [this]

/-- `μ` is stationary at price `p` with entry mass `M`. -/
def IsStationary (p M : ℝ) (μ : X → ℝ) : Prop :=
  ∀ x', μ x' = ∑ x, μ x * m.A p x x' + M * m.ν x'

/-- A solution of the homogeneous equation `d = d A` is zero (`ℓ¹` contraction,
since a fraction `δ` of firms exits every period). -/
theorem eq_zero_of_fixed (p : ℝ) {d : X → ℝ} (hd : ∀ x', d x' = ∑ x, d x * m.A p x x') : d = 0 := by
  have key : ∑ x', |d x'| ≤ (1 - m.δ) * ∑ x, |d x| := by
    calc ∑ x', |d x'| = ∑ x', |∑ x, d x * m.A p x x'| := by simp_rw [← hd]
      _ ≤ ∑ x', ∑ x, |d x| * m.A p x x' := sum_le_sum fun x' _ =>
          (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun x _ => by
            rw [abs_mul, abs_of_nonneg (m.A_nonneg p x x')])
      _ = ∑ x, |d x| * ∑ x', m.A p x x' := by rw [sum_comm]; simp_rw [mul_sum]
      _ ≤ ∑ x, |d x| * (1 - m.δ) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (m.sum_A_le p x) (abs_nonneg _)
      _ = (1 - m.δ) * ∑ x, |d x| := by rw [← sum_mul, mul_comm]
  have h0 : ∑ x, |d x| ≤ 0 := by
    have := m.δ_pos
    have hnn : 0 ≤ ∑ x, |d x| := sum_nonneg fun _ _ => abs_nonneg _
    nlinarith
  funext x
  have := (sum_eq_zero_iff_of_nonneg fun x _ => abs_nonneg (d x)).1
    (le_antisymm h0 (sum_nonneg fun _ _ => abs_nonneg _)) x (mem_univ x)
  simpa using this

/-- The linear map `μ ↦ μ - μA`. -/
noncomputable def L (p : ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun μ := fun x' => μ x' - ∑ x, μ x * m.A p x x'
  map_add' μ ν := by
    funext x'; simp only [Pi.add_apply, add_mul, sum_add_distrib]; ring
  map_smul' c μ := by
    funext x'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_sub, mul_sum]; congr 1; exact sum_congr rfl fun x _ => by ring

theorem L_injective (p : ℝ) : Injective (m.L p) := by
  intro μ μ' h
  have hd : ∀ x', (μ - μ') x' = ∑ x, (μ - μ') x * m.A p x x' := fun x' => by
    have := congrFun h x'
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]
    linarith
  exact sub_eq_zero.1 (m.eq_zero_of_fixed p hd)

/-- A stationary solution with nonnegative inflow is nonnegative. -/
theorem nonneg_of_stationary (p : ℝ) {μ f : X → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hμ : ∀ x', μ x' = ∑ x, μ x * m.A p x x' + f x') (x : X) : 0 ≤ μ x := by
  set n : X → ℝ := fun x => min (μ x) 0
  have hn : ∀ x', ∑ x, n x * m.A p x x' ≤ n x' := fun x' => by
    have h1 : ∑ x, n x * m.A p x x' ≤ ∑ x, μ x * m.A p x x' :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (min_le_left _ _) (m.A_nonneg p x x')
    have h2 : ∑ x, n x * m.A p x x' ≤ 0 :=
      sum_nonpos fun x _ => mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _) (m.A_nonneg p x x')
    refine le_min ?_ h2
    linarith [hμ x', hf x']
  have hsum : (1 - m.δ) * ∑ x, n x ≤ ∑ x, n x := by
    calc (1 - m.δ) * ∑ x, n x = ∑ x, n x * (1 - m.δ) := by rw [mul_sum]; simp_rw [mul_comm]
      _ ≤ ∑ x, n x * ∑ x', m.A p x x' := sum_le_sum fun x _ =>
          mul_le_mul_of_nonpos_left (m.sum_A_le p x) (min_le_right _ _)
      _ = ∑ x', ∑ x, n x * m.A p x x' := by simp_rw [mul_sum]; rw [sum_comm]
      _ ≤ ∑ x', n x' := sum_le_sum fun x' _ => hn x'
  have hnpos : 0 ≤ ∑ x, n x := by nlinarith [m.δ_pos]
  have hall := (sum_eq_zero_iff_of_nonpos fun x _ => (min_le_right (μ x) 0)).1
    (le_antisymm (sum_nonpos fun x _ => min_le_right _ _) hnpos) x (mem_univ x)
  by_contra h
  rw [min_eq_left (not_le.1 h).le] at hall
  linarith

/-- The stationary distribution per unit of entry. -/
noncomputable def μ₁ (p : ℝ) : X → ℝ :=
  Classical.choose ((LinearMap.injective_iff_surjective.1 (m.L_injective p)) m.ν)

theorem L_μ₁ (p : ℝ) : m.L p (m.μ₁ p) = m.ν :=
  Classical.choose_spec ((LinearMap.injective_iff_surjective.1 (m.L_injective p)) m.ν)

theorem μ₁_stationary (p : ℝ) : m.IsStationary p 1 (m.μ₁ p) := fun x' => by
  have := congrFun (m.L_μ₁ p) x'
  change m.μ₁ p x' - ∑ x, m.μ₁ p x * m.A p x x' = m.ν x' at this
  rw [one_mul]; linarith

theorem ν_le_μ₁ (p : ℝ) (x : X) : m.ν x ≤ m.μ₁ p x := by
  have h := m.μ₁_stationary p x
  have : 0 ≤ ∑ y, m.μ₁ p y * m.A p y x := sum_nonneg fun y _ =>
    mul_nonneg (m.nonneg_of_stationary p m.ν_nonneg (fun x' => by
      simpa using m.μ₁_stationary p x') y) (m.A_nonneg p y x)
  linarith

/-- **Stationary distribution.** For every price and entry mass there is exactly
one stationary distribution, `M · μ₁`; for `M ≥ 0` it is nonnegative. -/
theorem exists_unique_stationary (p M : ℝ) :
    m.IsStationary p M (M • m.μ₁ p) ∧ ∀ μ, m.IsStationary p M μ → μ = M • m.μ₁ p := by
  refine ⟨fun x' => ?_, fun μ hμ => ?_⟩
  · have := m.μ₁_stationary p x'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [this, one_mul, mul_add, mul_sum]
    congr 1; exact sum_congr rfl fun x _ => by ring
  · have hd : ∀ x', (μ - M • m.μ₁ p) x' = ∑ x, (μ - M • m.μ₁ p) x * m.A p x x' := fun x' => by
      have h1 := hμ x'
      have h2 := m.μ₁_stationary p x'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, sum_sub_distrib]
      rw [h1, h2, one_mul, mul_add, mul_sum]
      have : ∑ x, M * m.μ₁ p x * m.A p x x' = ∑ x, M * (m.μ₁ p x * m.A p x x') :=
        sum_congr rfl fun x _ => by ring
      rw [this]; ring
    exact sub_eq_zero.1 (m.eq_zero_of_fixed p hd)

theorem stationary_nonneg {p M : ℝ} (hM : 0 ≤ M) {μ : X → ℝ} (hμ : m.IsStationary p M μ) :
    0 ≤ μ := fun x =>
  m.nonneg_of_stationary p (fun x => mul_nonneg hM (m.ν_nonneg x)) hμ x

/-- Aggregate supply per unit of entry. -/
noncomputable def supply₁ (p : ℝ) : ℝ := ∑ x, m.μ₁ p x * m.s p x

theorem supply₁_pos {p : ℝ} (hp : 0 < p) : 0 < m.supply₁ p := by
  obtain ⟨x₀, hx₀⟩ := m.exists_ν_pos
  have hμ0 : ∀ x, 0 ≤ m.μ₁ p x := fun x => (m.ν_nonneg x).trans (m.ν_le_μ₁ p x)
  calc 0 < m.μ₁ p x₀ * m.s p x₀ :=
        mul_pos (hx₀.trans_le (m.ν_le_μ₁ p x₀)) (m.s_pos p hp x₀)
    _ ≤ m.supply₁ p := single_le_sum (f := fun x => m.μ₁ p x * m.s p x)
        (fun x _ => mul_nonneg (hμ0 x) (m.s_pos p hp x).le) (mem_univ x₀)

/-! ### Stationary equilibrium -/

/-- A stationary competitive equilibrium with positive entry (exit rule:
`stays`, indifferent firms continue). -/
structure IsEquilibrium (p M : ℝ) (μ : X → ℝ) : Prop where
  price_pos : 0 < p
  free_entry : m.entryValue p = m.ce
  entry_pos : 0 < M
  stationary : m.IsStationary p M μ
  clearing : ∑ x, μ x * m.s p x = m.D p

/-- **Hopenhayn (1992), existence and uniqueness.** If some positive price
makes every productivity state unprofitable and some positive price makes
expected entry profit at least the entry cost, there is exactly one stationary
equilibrium. -/
theorem exists_unique_equilibrium {plo phi : ℝ} (hplo : 0 < plo) (hphi : 0 < phi)
    (hlo : ∀ x, m.π plo x ≤ 0) (hhi : m.ce ≤ ∑ x, m.ν x * m.π phi x) :
    ∃! e : ℝ × ℝ × (X → ℝ), m.IsEquilibrium e.1 e.2.1 e.2.2 := by
  obtain ⟨p, ⟨hp0, hp⟩, hpu⟩ := m.exists_unique_entry_price hplo hphi hlo hhi
  set M := m.D p / m.supply₁ p
  have hS := m.supply₁_pos hp0
  have hM : 0 < M := div_pos (m.D_pos p hp0) hS
  refine ⟨(p, M, M • m.μ₁ p), ⟨hp0, hp, hM, (m.exists_unique_stationary p M).1, ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    have : ∑ x, M * m.μ₁ p x * m.s p x = M * m.supply₁ p := by
      unfold supply₁; rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    rw [this]; simp only [M]; field_simp
  · rintro ⟨p', M', μ'⟩ ⟨hp', he, hM', hst, hcl⟩
    simp only at hp' he hM' hst hcl
    obtain rfl := hpu p' ⟨hp', he⟩
    have hμ := (m.exists_unique_stationary p' M').2 μ' hst
    subst hμ
    have : M' * m.supply₁ p' = m.D p' := by
      rw [← hcl]; unfold supply₁; rw [mul_sum]
      exact sum_congr rfl fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hM'eq : M' = M := by simp only [M]; field_simp; linarith
    rw [hM'eq]

theorem IsEquilibrium.nonneg {p M : ℝ} {μ : X → ℝ} (h : m.IsEquilibrium p M μ) : 0 ≤ μ :=
  m.stationary_nonneg h.entry_pos.le h.stationary

end Model

/-- A non-vacuity witness: two productivity levels `{1, 2}`, persistence `0.8`,
entrants split evenly, profit `p·x - 1`, output `x`, demand `1 / (1 + p²)`. -/
noncomputable def example₁ : Model (Fin 2) where
  β := 9 / 10
  δ := 1 / 10
  ce := 1
  Q := fun x x' => if x = x' then 4 / 5 else 1 / 5
  ν := fun _ => 1 / 2
  π := fun p x => p * ((x : ℝ) + 1) - 1
  s := fun _ x => (x : ℝ) + 1
  D := fun p => 1 / (1 + p ^ 2)
  β_pos := by norm_num
  β_lt_one := by norm_num
  δ_pos := by norm_num
  δ_le_one := by norm_num
  ce_pos := by norm_num
  Q_nonneg := fun _ _ => by split_ifs <;> norm_num
  Q_sum := fun x => by fin_cases x <;> norm_num [Fin.sum_univ_two]
  ν_nonneg := fun _ => by norm_num
  ν_sum := by norm_num [Fin.sum_univ_two]
  π_cont := fun _ => by fun_prop
  π_strictMono := fun x p _ p' _ h => by
    have : (0 : ℝ) < (x : ℝ) + 1 := by positivity
    simp only; nlinarith
  s_pos := fun _ _ _ => by positivity
  D_pos := fun _ _ => by positivity

/-- In `example₁` the boundary conditions hold (`p = 1/2` and `p = 2`), so it
has a unique stationary equilibrium. -/
theorem example₁_equilibrium :
    ∃! e : ℝ × ℝ × (Fin 2 → ℝ), example₁.IsEquilibrium e.1 e.2.1 e.2.2 :=
  example₁.exists_unique_equilibrium (plo := 1 / 2) (phi := 2) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> norm_num [example₁])
    (by simp [example₁, Fin.sum_univ_two]; norm_num)

end Hopenhayn

end Econ
