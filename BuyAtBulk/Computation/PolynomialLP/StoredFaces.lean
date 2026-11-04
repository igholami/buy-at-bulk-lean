import BuyAtBulk.Computation.PolynomialLP.CutData

namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

theorem Stored.fix_vertex (input : Stored (n := n) (m := m)) (value : ℚ) (x : Fin n → ℚ)
    (feasible : (input.fix input.objective value).problem.Feasible x)
    (minimal : ∀ y, input.problem.Feasible y → input.problem.objective x ≤ input.problem.objective y)
    (vertex : (input.fix input.objective value).problem.Vertex x) : input.problem.Vertex x := by
  classical
  obtain ⟨original_feasible,value_eq⟩ := (input.fix_feasible input.objective value x).mp feasible
  intro y equalities
  have direction : ∀ i ∈ input.problem.active x, input.problem.row i (y-x) = 0 := by
    intro i member
    have active := (Finset.mem_filter.mp member).2
    simp only [map_sub,equalities i member,active,sub_self]
  have flat := optimal_direction_flat input.problem x (y-x) original_feasible minimal direction
  have objective_y : rowForm input.objective y = value := by
    rw [map_sub] at flat
    change rowForm input.objective y-rowForm input.objective x=0 at flat
    linarith
  apply vertex y
  intro c member
  apply Fin.lastCases (motive:=fun c => c ∈ (input.fix input.objective value).problem.active x →
      (input.fix input.objective value).problem.row c y = (input.fix input.objective value).problem.bound c) _ _ c member
  · intro _
    simp [Stored.fix,Stored.addCut,Stored.problem,rowForm_neg,objective_y]
    simpa only [rowForm_apply] using objective_y
  · intro c member
    apply Fin.lastCases (motive:=fun c => c.castSucc ∈ (input.fix input.objective value).problem.active x →
      (input.fix input.objective value).problem.row c.castSucc y =
        (input.fix input.objective value).problem.bound c.castSucc) _ _ c member
    · intro _
      simp [Stored.fix,Stored.addCut,Stored.problem,rowForm_neg,objective_y]
    · intro c member
      have active := (Finset.mem_filter.mp member).2
      have original_active : c ∈ input.problem.active x := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        simpa [Stored.fix,Stored.addCut,Stored.problem] using active
      simpa [Stored.fix,Stored.addCut,Stored.problem] using equalities c original_active

end BuyAtBulk.PolynomialLP
