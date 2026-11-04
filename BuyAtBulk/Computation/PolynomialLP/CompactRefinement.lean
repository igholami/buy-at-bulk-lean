import BuyAtBulk.Computation.PolynomialLP.CompactEncoding

set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP.CompactEncoding
open CompactFlow
variable {n h : ℕ} {G : SimpleGraph (Fin n)}

structure Matches (data : Data n h) (f : Solution G h) : Prop where
  adjacency : ∀ u v, data.adjacency[u.val][v.val]=true ↔ G.Adj u v
  source : ∀ i, data.source[i.val]=f.source i
  target : ∀ i, data.target[i.val]=f.target i
  buying : ∀ v, data.buying[v.val]=f.buying v
  physical : ∀ v, data.physical[v.val]=f.physical v
  demand : ∀ i, data.demand[i.val]=f.demand i

theorem coefficient_correct (data : Data n h) (f : Solution G h) (same : Matches data f)
    (r : ConstraintIndex (Fin n) h) (c : VariableIndex (Fin n) h) :
    coefficient data r c = f.linearProblem.row r (Pi.single c 1) := by
  classical
  rcases r with ⟨upper,r⟩ | ⟨i,v⟩ | ⟨⟨positive,incoming⟩,i,v⟩ | ⟨i,u,v⟩
  · cases upper <;> simp [coefficient,Solution.linearProblem,Pi.single_apply,eq_comm] <;> split_ifs <;> norm_num
  · rcases c with v' | ⟨j,w⟩ | ⟨j,u,w⟩ <;>
      simp [coefficient,nodeCoefficient,openingCoefficient,Solution.linearProblem,nodeMap,openingMap,Pi.single_apply,eq_comm,and_comm]
  · cases positive <;> cases incoming <;>
      rcases c with w | ⟨j,w⟩ | ⟨j,u,w⟩ <;>
      simp [coefficient,balanceCoefficient,nodeCoefficient,Solution.linearProblem,balanceMap,nodeMap,transportMap,LinearMap.sum_apply,Pi.single_apply,eq_comm,and_comm,ite_and] <;> split_ifs <;> simp_all
  · by_cases adj : G.Adj u v
    · have yes := (same.adjacency u v).mpr adj
      simp [coefficient,Solution.linearProblem,adj,yes]
    · have no : data.adjacency[u.val][v.val]=false := Bool.eq_false_iff.mpr (fun yes => adj ((same.adjacency u v).mp yes))
      simp [coefficient,Solution.linearProblem,adj,no,transportMap,Pi.single_apply,eq_comm]

theorem bound_correct (data : Data n h) (f : Solution G h) (same : Matches data f)
    (r : ConstraintIndex (Fin n) h) : bound data r = f.linearProblem.bound r := by
  classical
  rcases r with ⟨upper,r⟩ | ⟨i,v⟩ | ⟨⟨positive,incoming⟩,i,v⟩ | ⟨i,u,v⟩ <;>
    simp [bound,Solution.linearProblem,Solution.balanceBound,same.source,same.target]

theorem objective_correct (data : Data n h) (f : Solution G h) (same : Matches data f)
    (c : VariableIndex (Fin n) h) : objective data c = f.linearProblem.objective (Pi.single c 1) := by
  classical
  rcases c with v | ⟨i,v⟩ | ⟨i,u,v⟩ <;>
    simp [objective,Solution.linearProblem,openingMap,nodeMap,LinearMap.sum_apply,Pi.single_apply,same.buying,same.demand,same.physical,eq_comm,and_comm,ite_and]

def decode (x : Fin (variableCount n h) → ℚ) : Coordinate (Fin n) h :=
  fun c => x (variableEquiv n h c)

theorem row_correct (data : Data n h) (f : Solution G h) (same : Matches data f)
    (i : Fin (constraintCount n h)) (x : Fin (variableCount n h) → ℚ) :
    (stored data).problem.row i x = f.linearProblem.row ((constraints n h).symm i) (decode x) := by
  classical
  simp only [Stored.problem,stored,Vector.getElem_ofFn,rowForm_apply]
  rw [linearForm_expansion]
  apply Fintype.sum_equiv (variableEquiv n h).symm
  intro j
  rw [coefficient_correct data f same]
  simp [decode]

theorem feasible_correct (data : Data n h) (f : Solution G h) (same : Matches data f)
    (x : Fin (variableCount n h) → ℚ) :
    (stored data).problem.Feasible x ↔ f.linearProblem.Feasible (decode x) := by
  constructor
  · intro feasible r
    have inequality := feasible (constraints n h r)
    rw [row_correct data f same] at inequality
    simpa [Stored.problem,stored,bound_correct data f same] using inequality
  · intro feasible i
    rw [row_correct data f same]
    simpa [Stored.problem,stored,bound_correct data f same] using feasible ((constraints n h).symm i)

theorem objective_value (data : Data n h) (f : Solution G h) (same : Matches data f)
    (x : Fin (variableCount n h) → ℚ) :
    (stored data).problem.objective x = f.linearProblem.objective (decode x) := by
  classical
  simp only [Stored.problem,stored,Vector.getElem_ofFn,rowForm_apply]
  rw [linearForm_expansion]
  apply Fintype.sum_equiv (variableEquiv n h).symm
  intro j
  rw [objective_correct data f same]
  simp [decode]

end BuyAtBulk.PolynomialLP.CompactEncoding
