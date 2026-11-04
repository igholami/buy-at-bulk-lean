import BuyAtBulk.Computation.PolynomialLP.Optimization

/-! The actual returned vector inherits the ORIGINAL compact polytope's
Cramer encoding bound, independently of the number of successive face cuts. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP
open Computation.Rational RationalLP
variable {n m : ℕ}

theorem optimize_bits (input : Stored (n := n) (m := m)) (point : Vector ℚ n)
    (actual : optimize input = some point) :
    ∀ j : Fin n, (Code.ofRat point[j.val]).bits ≤ coordinateBits input := by
  have nonempty : ∃ x, input.problem.Feasible x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
    by_contra absent
    have no := (optimize_none_iff input).mpr absent
    rw [no] at actual
    cases actual
  let root := (integerize input).boxed
  have root_feasible (x : Fin n → ℚ) : root.problem.Feasible x ↔
      input.problem.Feasible x ∧ ∀ j, 0≤x j ∧ x j≤1 := by
    rw [Stored.boxed_feasible,integerize_feasible]
  have inhabited : ∃ x, root.problem.Feasible x := by
    obtain ⟨x,hx⟩ := nonempty
    exact ⟨x,(root_feasible x).mpr hx⟩
  have cube : root.problem.InUnitCube := (integerize input).boxed_in_cube
  have decision : decideBoxed root=true := (decide_correct_in_cube root cube).mpr inhabited
  have words : ∀ x, root.problem.Feasible x → root.problem.Vertex x →
      ∀ j, (Code.ofRat (x j)).bits ≤ coordinateBits input := fun x _ hv => root_vertex_words input x hv
  obtain ⟨value,returned,v,vfeasible,vvertex,value_eq,minimal⟩ :=
    recoverValue_correct root (coordinateBits input) cube inhabited words
  let face := root.fix root.objective value
  have subset : ∀ x, face.problem.Feasible x → root.problem.Feasible x :=
    fun x hx => ((root.fix_feasible root.objective value x).mp hx).1
  have vertices : ∀ x, face.problem.Feasible x → face.problem.Vertex x → root.problem.Vertex x := by
    intro x hx hv
    have equality := ((root.fix_feasible root.objective value x).mp hx).2
    apply root.fix_vertex value x hx _ hv
    intro y hy
    change rowForm root.objective x ≤ _
    rw [equality]
    exact minimal y hy
  have face_nonempty : ∃ x, face.problem.Feasible x :=
    ⟨v,(root.fix_feasible root.objective value v).mpr ⟨vfeasible,value_eq⟩⟩
  obtain ⟨values,computed,x,xfeasible,related,xvertex⟩ :=
    coordinateLoop_correct root (coordinateBits input) cube words (List.finRange n) face subset vertices face_nonempty
  have previous := (root.fix_feasible root.objective value x).mp xfeasible
  have original := (root_feasible x).mp previous.1
  have run : optimize input = some (Vector.ofFn x) := by
    unfold optimize
    change (if decideBoxed root then _ else _)=_
    rw [decision]
    simp only [ite_true]
    change ((recoverValue root (coordinateBits input)).bind fun q =>
      (coordinateLoop (coordinateBits input) (List.finRange n) (root.fix root.objective q)).bind
        fun values => vectorFromList values n) = _
    rw [returned]
    change (coordinateLoop (coordinateBits input) (List.finRange n) face).bind (fun values => vectorFromList values n) = _
    rw [computed]
    exact vectorFromList_correct values x related
  have same : point = Vector.ofFn x := Option.some.inj (actual.symm.trans run)
  intro j
  rw [same]
  simpa only [Vector.getElem_ofFn] using root_vertex_words input x xvertex j

end BuyAtBulk.PolynomialLP
