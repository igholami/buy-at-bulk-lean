import BuyAtBulk.Computation.PolynomialLP.ValueOptimization
import BuyAtBulk.Computation.PolynomialLP.StoredFaces

/-! Exact coordinate recovery by successive attained objective faces. Stored
constraints are appended by the program; every scalar comes from the actual
unconditional feasibility decision and rational reconstruction. -/
set_option maxHeartbeats 1600000
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
variable {n : ℕ}

def coordinateObjective (i : Fin n) : Vector ℚ n :=
  Vector.ofFn fun j => if j=i then 1 else 0

theorem coordinateObjective_value (i : Fin n) (x : Fin n → ℚ) :
    rowForm (coordinateObjective i) x = x i := by
  simp [coordinateObjective,rowForm_apply,ite_mul]

def coordinateLoop (K : ℕ) (indices : List (Fin n)) {m : ℕ} (input : Stored (n := n) (m := m)) : Option (List ℚ) :=
  match indices with
  | [] => some []
  | i::rest =>
      let current := input.withObjective (coordinateObjective i)
      (recoverValue current K).bind fun value =>
        (coordinateLoop K rest (current.fix current.objective value)).map (value::·)
termination_by indices.length

theorem coordinateLoop_correct {m₀ : ℕ} (original : Stored (n := n) (m := m₀)) (K : ℕ)
    (cube : original.problem.InUnitCube)
    (word_bound : ∀ x, original.problem.Feasible x → original.problem.Vertex x → ∀ j, (Code.ofRat (x j)).bits ≤ K)
    (indices : List (Fin n)) {m : ℕ} (input : Stored (n := n) (m := m))
    (subset : ∀ x, input.problem.Feasible x → original.problem.Feasible x)
    (vertices : ∀ x, input.problem.Feasible x → input.problem.Vertex x → original.problem.Vertex x)
    (nonempty : ∃ x, input.problem.Feasible x) :
    ∃ values, coordinateLoop K indices input = some values ∧
      ∃ x, input.problem.Feasible x ∧ List.Forall₂ (fun i value => x i=value) indices values ∧ original.problem.Vertex x := by
  induction indices generalizing m input with
  | nil =>
    obtain ⟨x,hx⟩ := nonempty
    obtain ⟨v,hv,vertex,_⟩ := input.problem.vertex_domination (fun y hy => cube y (subset y hy)) x hx
    exact ⟨[],by simp [coordinateLoop],v,hv,List.Forall₂.nil,vertices v hv vertex⟩
  | cons i rest ih =>
    let current := input.withObjective (coordinateObjective i)
    have current_cube : current.problem.InUnitCube := fun x hx => cube x (subset x hx)
    have current_words : ∀ x, current.problem.Feasible x → current.problem.Vertex x → ∀ j, (Code.ofRat (x j)).bits ≤ K :=
      fun x hx hv => word_bound x (subset x hx) (vertices x hx hv)
    obtain ⟨value,computed,v,vfeasible,vvertex,value_eq,minimal⟩ :=
      recoverValue_correct current K current_cube nonempty current_words
    let next := current.fix current.objective value
    have next_subset : ∀ x, next.problem.Feasible x → original.problem.Feasible x := by
      intro x hx
      exact subset x ((current.fix_feasible current.objective value x).mp hx).1
    have next_vertices : ∀ x, next.problem.Feasible x → next.problem.Vertex x → original.problem.Vertex x := by
      intro x hx hv
      have previous := (current.fix_feasible current.objective value x).mp hx
      have optimal : ∀ y, current.problem.Feasible y → current.problem.objective x ≤ current.problem.objective y := by
        intro y hy
        change rowForm current.objective x ≤ _
        rw [previous.2]
        exact minimal y hy
      have before := current.fix_vertex value x hx optimal hv
      exact vertices x previous.1 before
    have next_nonempty : ∃ x, next.problem.Feasible x :=
      ⟨v,(current.fix_feasible current.objective value v).mpr ⟨vfeasible,value_eq⟩⟩
    obtain ⟨tail,returned,x,xfeasible,related,xvertex⟩ := ih next next_subset next_vertices next_nonempty
    have previous := (current.fix_feasible current.objective value x).mp xfeasible
    have coordinate : x i=value := by
      simpa only [current,Stored.withObjective,coordinateObjective_value] using previous.2
    refine ⟨value::tail,?_,x,previous.1,List.Forall₂.cons coordinate related,xvertex⟩
    simp only [coordinateLoop]
    change ((recoverValue current K).bind fun q =>
      (coordinateLoop K rest (current.fix current.objective q)).map (q::·)) = some (value::tail)
    rw [computed]
    change (coordinateLoop K rest next).map (value::·) = some (value::tail)
    rw [returned]
    rfl

end BuyAtBulk.PolynomialLP
