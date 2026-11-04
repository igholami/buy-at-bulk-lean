import BuyAtBulk.Model.CompactFlowLinear

/-! Exact rational minimum attainment for the fixed-data compact graph LP.
This is a mathematical optimizer-existence theorem, not a polynomial solver. -/
noncomputable section
namespace BuyAtBulk.CompactFlow.Solution
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance compactFlowOptimizerDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowOptimizerDecRel : DecidableRel G.Adj := Classical.decRel _
variable (f : Solution G h)

theorem balance_of_feasible (x : Coordinate V h) (hx : f.linearProblem.Feasible x)
    (incoming : Bool) (i : Fin h) (v : V) :
    balanceMap incoming i v x = f.balanceBound incoming i v := by
  have hpos := hx (Sum.inr (Sum.inr (Sum.inl ((true, incoming), (i, v)))))
  have hneg := hx (Sum.inr (Sum.inr (Sum.inl ((false, incoming), (i, v)))))
  simp only [linearProblem, Bool.false_eq_true, ↓reduceIte, LinearMap.smul_apply,
    smul_eq_mul, one_mul, neg_one_mul] at hpos hneg
  linarith

/-- Recover the actual compact graph flow from a feasible rational coordinate
vector of the explicitly encoded fixed-data linear program. -/
def ofCoordinates (x : Coordinate V h) (hx : f.linearProblem.Feasible x) : Solution G h where
  source := f.source
  target := f.target
  buying := f.buying
  physical := f.physical
  demand := f.demand
  opening := fun v => openingMap v x
  node := fun i v => nodeMap i v x
  transport := fun i u v => transportMap i u v x
  buying_nonneg := f.buying_nonneg
  physical_nonneg := f.physical_nonneg
  demand_pos := f.demand_pos
  opening_bounds := fun v => f.linearProblem_in_cube x hx (.inl v)
  node_nonneg := fun i v => (f.linearProblem_in_cube x hx (.inr (.inl (i, v)))).1
  transport_nonneg := fun i u v => (f.linearProblem_in_cube x hx (.inr (.inr (i, u, v)))).1
  transport_nonedge := by
    intro i u v hn
    have hle := hx (Sum.inr (Sum.inr (Sum.inr (i, u, v))))
    simp only [linearProblem, hn, ↓reduceIte] at hle
    exact le_antisymm hle (f.linearProblem_in_cube x hx (.inr (.inr (i, u, v)))).1
  capacity := by
    intro i v
    have hle := hx (Sum.inr (Sum.inl (i, v)))
    simpa only [linearProblem, LinearMap.sub_apply, sub_nonpos] using hle
  incoming_balance := by
    intro i v
    simpa [balanceMap, balanceBound, LinearMap.sum_apply] using f.balance_of_feasible x hx true i v
  outgoing_balance := by
    intro i v
    simpa [balanceMap, balanceBound, LinearMap.sum_apply] using f.balance_of_feasible x hx false i v
  source_buying := f.source_buying
  source_physical := f.source_physical
  target_buying := f.target_buying
  target_physical := f.target_physical

theorem ofCoordinates_objective (x : Coordinate V h) (hx : f.linearProblem.Feasible x) :
    (f.ofCoordinates x hx).buyingBudget + (f.ofCoordinates x hx).rentalBudget =
      f.linearProblem.objective x := by
  simp only [ofCoordinates, buyingBudget, rentalBudget, fractionalLength, linearProblem,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- Data fixed by the optimization problem, in contrast to its unknown flows. -/
def SameData (g : Solution G h) : Prop :=
  g.source = f.source ∧ g.target = f.target ∧ g.buying = f.buying ∧
    g.physical = f.physical ∧ g.demand = f.demand

theorem linearProblem_eq_of_sameData (g : Solution G h) (same : f.SameData g) :
    g.linearProblem = f.linearProblem := by
  rcases same with ⟨hs, ht, hb, hl, hd⟩
  simp only [linearProblem, balanceBound, hs, ht, hb, hl, hd]

theorem ofCoordinates_sameData (x : Coordinate V h) (hx : f.linearProblem.Feasible x) :
    f.SameData (f.ofCoordinates x hx) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The nonempty fixed-data compact LP attains its exact minimum at a feasible
rational flow. The objective is buying plus demand-weighted physical rental. -/
theorem minimum_attained :
    ∃ g : Solution G h, f.SameData g ∧
      ∀ z : Solution G h, f.SameData z →
        g.buyingBudget + g.rentalBudget ≤ z.buyingBudget + z.rentalBudget := by
  obtain ⟨x, hx, hmin⟩ := f.linearProblem.minimum_attained f.linearProblem_in_cube
    ⟨f.coordinates, f.coordinates_feasible⟩
  refine ⟨f.ofCoordinates x hx, f.ofCoordinates_sameData x hx, ?_⟩
  intro z same
  rw [f.ofCoordinates_objective]
  have hz : f.linearProblem.Feasible z.coordinates := by
    rw [← f.linearProblem_eq_of_sameData z same]
    exact z.coordinates_feasible
  calc
    f.linearProblem.objective x ≤ f.linearProblem.objective z.coordinates := hmin z.coordinates hz
    _ = z.buyingBudget + z.rentalBudget := by
      rw [← f.linearProblem_eq_of_sameData z same, z.objective_coordinates]

/-- A chosen exact rational optimum. This definition is noncomputable and
therefore carries no claim to implement the paper's polynomial LP solver. -/
def optimalCoordinates : Coordinate V h :=
  (f.linearProblem.minimum_attained f.linearProblem_in_cube
    ⟨f.coordinates, f.coordinates_feasible⟩).choose

theorem optimalCoordinates_feasible : f.linearProblem.Feasible f.optimalCoordinates :=
  (f.linearProblem.minimum_attained f.linearProblem_in_cube
    ⟨f.coordinates, f.coordinates_feasible⟩).choose_spec.1

abbrev optimal : Solution G h :=
  f.ofCoordinates f.optimalCoordinates f.optimalCoordinates_feasible

theorem optimal_sameData : f.SameData f.optimal := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem optimal_le (z : Solution G h) (same : f.SameData z) :
    f.optimal.buyingBudget + f.optimal.rentalBudget ≤ z.buyingBudget + z.rentalBudget := by
  rw [optimal, f.ofCoordinates_objective]
  have hz : f.linearProblem.Feasible z.coordinates := by
    rw [← f.linearProblem_eq_of_sameData z same]
    exact z.coordinates_feasible
  calc
    f.linearProblem.objective f.optimalCoordinates ≤ f.linearProblem.objective z.coordinates :=
      (f.linearProblem.minimum_attained f.linearProblem_in_cube
        ⟨f.coordinates, f.coordinates_feasible⟩).choose_spec.2 z.coordinates hz
    _ = z.buyingBudget + z.rentalBudget := by
      rw [← f.linearProblem_eq_of_sameData z same, z.objective_coordinates]

end BuyAtBulk.CompactFlow.Solution
