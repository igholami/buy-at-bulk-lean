import BuyAtBulk.Computation.PolynomialLP.CoordinateOptimization
import BuyAtBulk.Computation.PolynomialLP.IntegerEncoding

/-! Exact optimal vectors computed using only stored rational data. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
variable {n m : ℕ}

def coordinateBits (input : Stored (n := n) (m := m)) : ℕ :=
  2*(n^2+n*integerL input+1)+2

theorem root_vertex_words (input : Stored (n := n) (m := m))
    (x : Fin n → ℚ) (vertex : (integerize input).boxed.problem.Vertex x) :
    ∀ j, (Code.ofRat (x j)).bits ≤ coordinateBits input := by
  obtain ⟨coefficients,bounds,abound,bbound⟩ := boxed_integer_data input
  obtain ⟨code,decoded,bits⟩ := vertex_encoded_general (integerize input).boxed.problem
    (fun i j => ((integerize input).boxed.coefficients[i.val][j.val]).num)
    (fun i => ((integerize input).boxed.bounds[i.val]).num)
    (by intro i j; simpa [Stored.problem,rowForm_apply,Pi.single_apply,mul_ite] using coefficients i j)
    bounds (integerH input) (integerL input) (by rfl) abound bbound x vertex
  intro j
  rw [← decoded j]
  exact (Code.normalized_bits_le _).trans (by simpa [coordinateBits] using bits j)

def vectorFromList (values : List ℚ) (n : ℕ) : Option (Vector ℚ n) :=
  if length : values.length=n then
    some (Vector.ofFn fun j => values[j.val]'(by omega))
  else none

theorem vectorFromList_correct (values : List ℚ) (x : Fin n → ℚ)
    (related : List.Forall₂ (fun i value => x i=value) (List.finRange n) values) :
    vectorFromList values n = some (Vector.ofFn x) := by
  have length : values.length=n := by simpa using related.length_eq.symm
  unfold vectorFromList
  rw [dif_pos length]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  have rel := related.get (by simpa using hi) (by omega : i < values.length)
  simpa using rel.symm

def optimize (input : Stored (n := n) (m := m)) : Option (Vector ℚ n) :=
  let root := (integerize input).boxed
  if decideBoxed root then
    (recoverValue root (coordinateBits input)).bind fun value =>
      (coordinateLoop (coordinateBits input) (List.finRange n)
        (root.fix root.objective value)).bind fun values => vectorFromList values n
  else none

theorem optimize_success (input : Stored (n := n) (m := m))
    (nonempty : ∃ x, input.problem.Feasible x ∧ ∀ j, 0≤x j ∧ x j≤1) :
    ∃ point, optimize input=some point ∧
      input.problem.Feasible (fun j => point[j.val]) ∧
      (∀ j : Fin n, 0≤point[j.val] ∧ point[j.val]≤1) ∧
      ∀ y, input.problem.Feasible y → (∀ j, 0≤y j ∧ y j≤1) →
        input.problem.objective (fun j => point[j.val]) ≤ input.problem.objective y := by
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
  refine ⟨Vector.ofFn x,?_,by simpa using original.1,by simpa using original.2,?_⟩
  · unfold optimize
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
  · intro y hy box
    have comparison := minimal y ((root_feasible y).mpr ⟨hy,box⟩)
    have equality := previous.2
    change root.problem.objective x = value at equality
    rw [← equality] at comparison
    simpa [root,Stored.boxed,Stored.extend,integerize,Stored.problem] using comparison

theorem optimize_none_iff (input : Stored (n := n) (m := m)) :
    optimize input=none ↔ ¬∃ x, input.problem.Feasible x ∧ ∀ j, 0≤x j ∧ x j≤1 := by
  constructor
  · intro absent inhabited
    obtain ⟨point,computed,_⟩ := optimize_success input inhabited
    rw [absent] at computed
    cases computed
  · intro impossible
    have decision : decideBoxed (integerize input).boxed=false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨x,hx,box⟩ := (decideBoxed_correct _).mp yes
      apply impossible
      rw [Stored.boxed_feasible,integerize_feasible] at hx
      exact ⟨x,hx⟩
    simp only [optimize,decision,Bool.false_eq_true,ite_false]

theorem optimize_correct (input : Stored (n := n) (m := m)) (point : Vector ℚ n)
    (computed : optimize input=some point) :
    input.problem.Feasible (fun j => point[j.val]) ∧
      (∀ j : Fin n, 0≤point[j.val] ∧ point[j.val]≤1) ∧
      ∀ y, input.problem.Feasible y → (∀ j, 0≤y j ∧ y j≤1) →
        input.problem.objective (fun j => point[j.val]) ≤ input.problem.objective y := by
  have inhabited : ∃ x, input.problem.Feasible x ∧ ∀ j, 0≤x j ∧ x j≤1 := by
    by_contra absent
    have no := (optimize_none_iff input).mpr absent
    rw [no] at computed
    cases computed
  obtain ⟨answer,returned,correct⟩ := optimize_success input inhabited
  have same : answer=point := Option.some.inj (returned.symm.trans computed)
  simpa only [same] using correct

end BuyAtBulk.PolynomialLP
