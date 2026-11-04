import BuyAtBulk.Model.CompactFlow
import BuyAtBulk.Model.RationalLP.Vertices

/-! Fixed-data rational inequality encoding of the compact node-split LP.
All unknowns have unit-box constraints; equalities use two opposite inequalities. -/
noncomputable section
namespace BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance compactFlowLinearDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowLinearDecRel : DecidableRel G.Adj := Classical.decRel _

abbrev Coordinate (V : Type) (h : ℕ) := VariableIndex V h → ℚ
abbrev ConstraintIndex (V : Type) (h : ℕ) :=
  (Bool × VariableIndex V h) ⊕ ((Fin h × V) ⊕
    (((Bool × Bool) × (Fin h × V)) ⊕ (Fin h × V × V)))

/-- Exact number of scalar inequalities, including two-sided balances. -/
theorem constraint_count :
    Fintype.card (ConstraintIndex V h) =
      2 * Fintype.card V + 7 * h * Fintype.card V + 3 * h * Fintype.card V ^ 2 := by
  simp [ConstraintIndex, VariableIndex, Fintype.card_sum, Fintype.card_prod]
  ring

/-- The compact formulation has quadratically many rows in the vertex count. -/
theorem constraint_count_le :
    Fintype.card (ConstraintIndex V h) ≤ (10 * h + 2) * Fintype.card V ^ 2 := by
  rw [constraint_count]
  have hn : Fintype.card V ≤ Fintype.card V ^ 2 := by
    cases hn : Fintype.card V with
    | zero => simp
    | succ n => nlinarith
  have hmul := Nat.mul_le_mul_left h hn
  nlinarith

def openingMap (v : V) : Coordinate V h →ₗ[ℚ] ℚ := LinearMap.proj (Sum.inl v)
def nodeMap (i : Fin h) (v : V) : Coordinate V h →ₗ[ℚ] ℚ :=
  LinearMap.proj (Sum.inr (Sum.inl (i, v)))
def transportMap (i : Fin h) (u v : V) : Coordinate V h →ₗ[ℚ] ℚ :=
  LinearMap.proj (Sum.inr (Sum.inr (i, u, v)))

def balanceMap (incoming : Bool) (i : Fin h) (v : V) : Coordinate V h →ₗ[ℚ] ℚ :=
  if incoming then nodeMap i v - ∑ u, transportMap i u v
  else (∑ u, transportMap i v u) - nodeMap i v

namespace Solution
variable (f : Solution G h)

def coordinates : Coordinate V h
  | .inl v => f.opening v
  | .inr (.inl (i, v)) => f.node i v
  | .inr (.inr (i, u, v)) => f.transport i u v

def balanceBound (incoming : Bool) (i : Fin h) (v : V) : ℚ :=
  if incoming then (if f.source i = v then 1 else 0)
  else -(if f.target i = v then 1 else 0)

def linearProblem : RationalLP.Problem (VariableIndex V h) (ConstraintIndex V h) where
  row
    | .inl (upper, c) => if upper then LinearMap.proj c else -LinearMap.proj c
    | .inr (.inl (i, v)) => nodeMap i v - openingMap v
    | .inr (.inr (.inl ((positive, incoming), (i, v)))) =>
      (if positive then (1 : ℚ) else -1) • balanceMap incoming i v
    | .inr (.inr (.inr (i, u, v))) => if G.Adj u v then 0 else transportMap i u v
  bound
    | .inl (upper, _) => if upper then 1 else 0
    | .inr (.inl _) => 0
    | .inr (.inr (.inl ((positive, incoming), (i, v)))) =>
      (if positive then (1 : ℚ) else -1) * f.balanceBound incoming i v
    | .inr (.inr (.inr _)) => 0
  objective := (∑ v, f.buying v • openingMap v) +
    ∑ i, ∑ v, (f.demand i * f.physical v) • nodeMap i v

theorem coordinate_bounds (c : VariableIndex V h) :
    0 ≤ f.coordinates c ∧ f.coordinates c ≤ 1 := by
  cases c with
  | inl v => exact f.opening_bounds v
  | inr c => cases c with
    | inl iv => exact ⟨f.node_nonneg iv.1 iv.2, (f.capacity iv.1 iv.2).trans (f.opening_bounds iv.2).2⟩
    | inr iuv => exact ⟨f.transport_nonneg iuv.1 iuv.2.1 iuv.2.2,
        f.transport_le_one iuv.1 iuv.2.1 iuv.2.2⟩

theorem linearProblem_in_cube : f.linearProblem.InUnitCube := by
  intro x hx c
  have hlo := hx (Sum.inl (false, c))
  have hhi := hx (Sum.inl (true, c))
  simp only [linearProblem, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply,
    LinearMap.proj_apply, neg_nonpos] at hlo
  simp only [linearProblem, ↓reduceIte, LinearMap.proj_apply] at hhi
  exact ⟨hlo, hhi⟩

theorem balanceMap_coordinates (incoming : Bool) (i : Fin h) (v : V) :
    balanceMap incoming i v f.coordinates = f.balanceBound incoming i v := by
  cases incoming
  · simpa [balanceMap, balanceBound, nodeMap, transportMap, coordinates,
      LinearMap.sum_apply] using f.outgoing_balance i v
  · simpa [balanceMap, balanceBound, nodeMap, transportMap, coordinates,
      LinearMap.sum_apply] using f.incoming_balance i v

theorem coordinates_feasible : f.linearProblem.Feasible f.coordinates := by
  intro c
  cases c with
  | inl uc =>
    rcases uc with ⟨upper, c⟩
    cases upper
    · simpa [linearProblem] using (f.coordinate_bounds c).1
    · simpa [linearProblem] using (f.coordinate_bounds c).2
  | inr c => cases c with
    | inl iv =>
      simpa [linearProblem, nodeMap, openingMap, coordinates] using f.capacity iv.1 iv.2
    | inr c => cases c with
      | inl bbiv =>
        rcases bbiv with ⟨⟨positive, incoming⟩, i, v⟩
        have hb := f.balanceMap_coordinates incoming i v
        simp only [linearProblem, LinearMap.smul_apply, smul_eq_mul, hb, le_refl]
      | inr iuv =>
        rcases iuv with ⟨i, u, v⟩
        by_cases hadj : G.Adj u v
        · simp [linearProblem, hadj]
        · simp [linearProblem, hadj, transportMap, coordinates, f.transport_nonedge i u v hadj]

theorem objective_coordinates :
    f.linearProblem.objective f.coordinates = f.buyingBudget + f.rentalBudget := by
  simp only [linearProblem, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, openingMap, nodeMap, LinearMap.proj_apply, coordinates,
    buyingBudget, rentalBudget, fractionalLength, Finset.mul_sum, mul_assoc]

end Solution
end BuyAtBulk.CompactFlow
