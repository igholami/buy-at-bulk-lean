import BuyAtBulk.Computation.Runtime.FlowSearchWords
import BuyAtBulk.Computation.Runtime.Weights
import BuyAtBulk.Computation.FlowDecomposition.Trace

namespace BuyAtBulk.Computation.Runtime.FlowUpdate
open Rational
variable {n : ℕ} {G : SimpleGraph (Fin n)}

def minimum (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) {s t : Fin n} :
    G.Walk s t → Traced ℚ
  | .nil => emit .write [(Code.ofRat mass).bits] mass
  | @SimpleGraph.Walk.cons _ _ u v t edge tail => do
      let _ ← emit .scan [u.val.size,v.val.size] ()
      let row ← emit .read [u.val.size,n.size] matrix[u.val]
      let q ← readRat row v
      let rest ← minimum matrix mass tail
      let less ← ratLe q rest
      let less ← branch less
      let chosen := if less then q else rest
      emit .write [(Code.ofRat chosen).bits] chosen

@[simp] theorem minimum_nil (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) (s : Fin n) :
    (minimum matrix mass (.nil : G.Walk s s)).value=mass := rfl

@[simp] theorem minimum_cons (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ)
    {s u t : Fin n} (edge : G.Adj s u) (tail : G.Walk u t) :
    (minimum matrix mass (.cons edge tail)).value=min matrix[s.val][u.val] (minimum matrix mass tail).value := by
  by_cases less : matrix[s.val][u.val]≤(minimum matrix mass tail).value <;>
    simp [minimum,Traced.bind_value,readRat,ratLe,branch,min_def,less]

theorem minimum_lower (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ)
    {s t : Fin n} (walk : G.Walk s t) (q : ℚ) :
    q≤(minimum matrix mass walk).value ↔ q≤mass ∧
      ∀ dart ∈ walk.darts, q≤matrix[dart.fst.val][dart.snd.val] := by
  induction walk with
  | nil => simp
  | cons edge tail ih =>
    rw [minimum_cons,le_min_iff,ih]
    simp only [SimpleGraph.Walk.darts_cons,List.mem_cons,forall_eq_or_imp]
    tauto

theorem minimum_bottleneck (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ)
    {s t : Fin n} (path : G.Path s t) :
    (minimum matrix mass path.val).value=FlowDecomposition.bottleneck G (FlowDecomposition.matrixFlow matrix) mass path := by
  classical
  let S := insert mass (path.val.darts.map fun dart => matrix[dart.fst.val][dart.snd.val]).toFinset
  change _=S.min' _
  apply le_antisymm
  · have lower := (minimum_lower matrix mass path.val (minimum matrix mass path.val).value).mp le_rfl
    have member := Finset.min'_mem S ⟨mass,Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.mp member with equal | member
    · rw [equal]; exact lower.1
    · obtain ⟨dart,member,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      rw [← equal]
      exact lower.2 dart member
  · apply (minimum_lower matrix mass path.val _).mpr
    constructor
    · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    · intro dart member
      exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨dart,member,rfl⟩)))

theorem minimum_count (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ)
    {s t : Fin n} (walk : G.Walk s t) :
    (minimum matrix mass walk).events.length=6*walk.length+1 := by
  induction walk with
  | nil => rfl
  | cons edge tail ih =>
    simp only [minimum,Traced.bind_events,Traced.bind_value,emit_length,emit_value,readRat,
      ratLe,branch,List.length_append,SimpleGraph.Walk.length_cons,ih]
    omega

def occurs (u v : Fin n) {s t : Fin n} : G.Walk s t → Traced Bool
  | .nil => ⟨false,[⟨.branch,[1]⟩]⟩
  | @SimpleGraph.Walk.cons _ _ s w t edge tail =>
      let events : List Event := [⟨.scan,[s.val.size,w.val.size]⟩,
        ⟨.natCompare,[s.val.size,u.val.size]⟩,⟨.natCompare,[w.val.size,v.val.size]⟩,⟨.branch,[1]⟩]
      if s=u ∧ w=v then ⟨true,events⟩ else
        let result := occurs u v tail
        ⟨result.value,events++result.events⟩

@[simp] theorem occurs_value (u v : Fin n) {s t : Fin n} (walk : G.Walk s t) :
    (occurs u v walk).value=walk.darts.any (fun dart => decide (dart.fst=u ∧ dart.snd=v)) := by
  induction walk with
  | nil => rfl
  | @cons s w t edge tail ih =>
    by_cases same : s=u ∧ w=v <;> simp [occurs,SimpleGraph.Walk.darts_cons,same,ih]

theorem occurs_count (u v : Fin n) {s t : Fin n} (walk : G.Walk s t) :
    (occurs u v walk).events.length≤4*walk.length+1 := by
  induction walk with
  | nil => rfl
  | cons edge tail ih =>
    simp only [occurs]
    split <;> simp only [List.length_append,List.length_cons,List.length_nil,SimpleGraph.Walk.length_cons] <;> omega

def subtractCell (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) (u v : Fin n) : Traced ℚ := do
  let row ← emit .read [u.val.size,n.size] matrix[u.val]
  let q ← readRat row v
  let used ← occurs u v path.val
  let chosen := if used then amount else 0
  let chosen ← emit .branch [1,(Code.ofRat chosen).bits] chosen
  let negative ← emit .ratNeg [(Code.ofRat chosen).bits,(Code.ofRat (-chosen)).bits] (-chosen)
  ratAdd q negative

@[simp] theorem subtractCell_value (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) (u v : Fin n) :
    (subtractCell matrix amount path u v).value=matrix[u.val][v.val]-
      if FlowDecomposition.usesArc G path u v then amount else 0 := by
  simp [subtractCell,Traced.bind_value,readRat,FlowDecomposition.usesArc,sub_eq_add_neg]

theorem subtractCell_count (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) (u v : Fin n) :
    (subtractCell matrix amount path u v).events.length≤4*path.val.length+7 := by
  have used := occurs_count u v path.val
  simp only [subtractCell,Traced.bind_events,Traced.bind_value,List.length_append,emit_length,emit_value,readRat,ratAdd_length]
  omega

def subtract (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) : Traced (FlowDecomposition.FlowMatrix n) :=
  Weights.materialize (fun u => Weights.materialize (subtractCell matrix amount path u)
    (fun q => (Code.ofRat q).bits)) (fun _ => n.size)

@[simp] theorem subtract_value (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) :
    (subtract matrix amount path).value=FlowDecomposition.subtract G (Equiv.refl _) matrix amount path := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [subtract,Weights.materialize,FlowDecomposition.subtract,FlowDecomposition.matrixFlow,subtractCell_value] <;> rfl

theorem subtract_count (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) :
    (subtract matrix amount path).events.length≤(4*path.val.length+9)*n^2+3*n+1 := by
  have row (u : Fin n) := Weights.materialize_count (subtractCell matrix amount path u)
    (fun q => (Code.ofRat q).bits) (4*path.val.length+7) (fun v => subtractCell_count matrix amount path u v)
  have all := Weights.materialize_count (fun u : Fin n => Weights.materialize (subtractCell matrix amount path u)
    (fun q => (Code.ofRat q).bits)) (fun _ => n.size) (n*(4*path.val.length+9)+1) row
  dsimp only [subtract]
  nlinarith

end BuyAtBulk.Computation.Runtime.FlowUpdate
