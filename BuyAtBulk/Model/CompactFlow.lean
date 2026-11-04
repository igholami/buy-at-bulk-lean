import BuyAtBulk.UpperBound.NodeLP

/-! A compact directed node-split LP. Each original vertex has an incoming and
outgoing copy and a paid split arc; original undirected edges give both directed
transport arcs. We index transport variables by all ordered pairs, forcing
nonedge entries to zero. Thus no path universe appears in the compact model. -/
noncomputable section
namespace BuyAtBulk.CompactFlow

variable {V : Type} [Fintype V]
local instance compactFlowDecEq : DecidableEq V := Classical.decEq _

/-- Directed split-network vertices: `false` is incoming, `true` outgoing. -/
abbrev SplitVertex (V : Type) := V × Bool

/-- Actual allowed arcs in the directed node-split network. -/
def SplitArc (G : SimpleGraph V) (a b : SplitVertex V) : Prop :=
  (a.2 = false ∧ b.2 = true ∧ a.1 = b.1) ∨
  (a.2 = true ∧ b.2 = false ∧ G.Adj a.1 b.1)

/-- Feasible rational compact flow with a separate resource capacity for each
commodity. Source is the incoming copy and sink the outgoing copy, so source
and target node arcs are included even for coincident original endpoints. -/
structure Solution (G : SimpleGraph V) (h : ℕ) where
  source : Fin h → V
  target : Fin h → V
  buying : V → ℚ
  physical : V → ℚ
  demand : Fin h → ℚ
  opening : V → ℚ
  node : Fin h → V → ℚ
  transport : Fin h → V → V → ℚ
  buying_nonneg : ∀ v, 0 ≤ buying v
  physical_nonneg : ∀ v, 0 ≤ physical v
  demand_pos : ∀ i, 0 < demand i
  opening_bounds : ∀ v, 0 ≤ opening v ∧ opening v ≤ 1
  node_nonneg : ∀ i v, 0 ≤ node i v
  transport_nonneg : ∀ i u v, 0 ≤ transport i u v
  transport_nonedge : ∀ i u v, ¬G.Adj u v → transport i u v = 0
  capacity : ∀ i v, node i v ≤ opening v
  incoming_balance : ∀ i v, node i v - ∑ u, transport i u v =
    if source i = v then 1 else 0
  outgoing_balance : ∀ i v, (∑ u, transport i v u) - node i v =
    -(if target i = v then 1 else 0)
  source_buying : ∀ i, buying (source i) = 0
  source_physical : ∀ i, physical (source i) = 0
  target_buying : ∀ i, buying (target i) = 0
  target_physical : ∀ i, physical (target i) = 0

namespace Solution
variable {G : SimpleGraph V} {h : ℕ} (f : Solution G h)
/-- Every compact transport coordinate is bounded by its head node throughput. -/
theorem transport_le_node (i : Fin h) (u v : V) : f.transport i u v ≤ f.node i v := by
  have hs : f.transport i u v ≤ ∑ x, f.transport i x v :=
    Finset.single_le_sum (fun x _ => f.transport_nonneg i x v) (Finset.mem_univ u)
  have hi := f.incoming_balance i v
  have hn : (0 : ℚ) ≤ if f.source i = v then 1 else 0 := by split_ifs <;> norm_num
  linarith

/-- All coordinates of the fixed-data compact feasible set lie in the unit cube. -/
theorem transport_le_one (i : Fin h) (u v : V) : f.transport i u v ≤ 1 :=
  (f.transport_le_node i u v).trans ((f.capacity i v).trans (f.opening_bounds v).2)

def buyingBudget : ℚ := ∑ v, f.buying v * f.opening v
def fractionalLength (i : Fin h) : ℚ := ∑ v, f.physical v * f.node i v
def rentalBudget : ℚ := ∑ i, f.demand i * f.fractionalLength i
end Solution

/-- Coordinates of the compact LP: shared node openings, commodity split arcs,
and commodity ordered-pair transport arcs. This index has no path coordinates. -/
abbrev VariableIndex (V : Type) (h : ℕ) := V ⊕ ((Fin h × V) ⊕ (Fin h × V × V))

theorem variable_count (h : ℕ) :
    Fintype.card (VariableIndex V h) =
      Fintype.card V + h * (Fintype.card V + Fintype.card V ^ 2) := by
  simp [VariableIndex, Fintype.card_sum, Fintype.card_prod]
  ring

/-- An explicit quadratic-in-vertices, linear-in-commodities coordinate bound. -/
theorem variable_count_le (h : ℕ) :
    Fintype.card (VariableIndex V h) ≤ (2 * h + 1) * Fintype.card V ^ 2 := by
  rw [variable_count]
  have hn : Fintype.card V ≤ Fintype.card V ^ 2 := by
    cases hn : Fintype.card V with
    | zero => simp
    | succ n => nlinarith
  nlinarith

end BuyAtBulk.CompactFlow
