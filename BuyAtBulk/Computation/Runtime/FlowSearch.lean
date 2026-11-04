import BuyAtBulk.Computation.Runtime.Paths
import BuyAtBulk.Computation.ShortestPath.Encoding
import BuyAtBulk.Computation.FlowDecomposition.SearchComplexity
import BuyAtBulk.Computation.FlowDecomposition.Bottleneck

/-! Directed positive-flow search on actual stored matrices. Walk extension
copies and every table/adjacency/flow scan are part of the operation trace. -/
namespace BuyAtBulk.Computation.Runtime.FlowSearch
open Rational
variable {n : ℕ} (input : Computation.ShortestPath.GraphEncoding n)

 def concat {s u v : Fin n} : input.graph.Walk s u → input.graph.Adj u v → Traced (input.graph.Walk s v)
  | .nil, edge => ⟨.cons edge .nil,[⟨.branch,[1]⟩,⟨.cons,[u.val.size,v.val.size]⟩]⟩
  | .cons edge tail, last =>
      let result := concat tail last
      ⟨.cons edge result.value,[⟨.branch,[1]⟩]++result.events++[⟨.cons,[s.val.size]⟩]⟩

@[simp] theorem concat_value {s u v : Fin n} (walk : input.graph.Walk s u) (edge : input.graph.Adj u v) :
    (concat input walk edge).value=walk.concat edge := by
  induction walk with
  | nil => rfl
  | cons first tail ih => simp [concat,ih,SimpleGraph.Walk.concat]

@[simp] theorem concat_count {s u v : Fin n} (walk : input.graph.Walk s u) (edge : input.graph.Adj u v) :
    (concat input walk edge).events.length=2*walk.length+2 := by
  induction walk with
  | nil => rfl
  | cons first tail ih => simp [concat,ih]; omega

def lookup {source : Fin n} : FlowDecomposition.Table input.graph source →
    (target : Fin n) → Traced (Option (input.graph.Walk source target))
  | [], _ => ⟨none,[⟨.branch,[1]⟩]⟩
  | ⟨v,path⟩::rest,target =>
      let eventsBefore : List Event := [⟨.scan,[v.val.size]⟩,⟨.read,[v.val.size]⟩,
        ⟨.natCompare,[v.val.size,target.val.size]⟩,⟨.branch,[1]⟩]
      if equal : v=target then
        ⟨some (path.copy rfl equal),eventsBefore++[⟨.write,[1]⟩]⟩
      else
        let result := lookup rest target
        ⟨result.value,eventsBefore++result.events⟩

@[simp] theorem lookup_value {source target : Fin n} (table : FlowDecomposition.Table input.graph source) :
    (lookup input table target).value=FlowDecomposition.lookup input.graph table target := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨v,path⟩
    simp only [lookup,FlowDecomposition.lookup]
    split <;> simp_all

theorem lookup_count {source target : Fin n} (table : FlowDecomposition.Table input.graph source) :
    (lookup input table target).events.length≤4*table.length+1 := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨v,path⟩
    simp only [lookup]
    split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega

def extend (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n} :
    FlowDecomposition.Table input.graph source → (target : Fin n) → Traced (Option (input.graph.Walk source target))
  | [], _ => ⟨none,[⟨.branch,[1]⟩]⟩
  | ⟨v,path⟩::rest,target =>
      let eventsBefore : List Event := [⟨.scan,[v.val.size]⟩,⟨.read,[v.val.size,n.size]⟩,
        ⟨.read,[target.val.size,1]⟩,⟨.branch,[1]⟩]
      if edge : input.graph.Adj v target then
        let q := matrix[v.val][target.val]
        let checked : List Event := [⟨.read,[v.val.size,n.size]⟩,
          ⟨.read,[target.val.size,(Code.ofRat q).bits]⟩,
          ⟨.ratCompare,[(Code.ofRat (0:ℚ)).bits,(Code.ofRat q).bits]⟩,⟨.branch,[1]⟩]
        if 0<q then
          let result := concat input path edge
          ⟨some result.value,eventsBefore++checked++result.events++[⟨.write,[1]⟩]⟩
        else
          let result := extend matrix rest target
          ⟨result.value,eventsBefore++checked++result.events⟩
      else
        let result := extend matrix rest target
        ⟨result.value,eventsBefore++result.events⟩

@[simp] theorem extend_value (matrix : FlowDecomposition.FlowMatrix n) {source target : Fin n}
    (table : FlowDecomposition.Table input.graph source) :
    (extend input matrix table target).value=
      FlowDecomposition.extend input.graph (FlowDecomposition.matrixFlow matrix) table target := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨v,path⟩
    by_cases edge : input.graph.Adj v target
    · by_cases positive : 0<matrix[v.val][target.val] <;>
        simp [extend,FlowDecomposition.extend,FlowDecomposition.matrixFlow,edge,positive,ih]
    · simp [extend,FlowDecomposition.extend,edge,ih]

theorem extend_count (matrix : FlowDecomposition.FlowMatrix n) {source target : Fin n}
    (table : FlowDecomposition.Table input.graph source) (R : ℕ)
    (depth : FlowDecomposition.Depth input.graph table R) :
    (extend input matrix table target).events.length≤(2*R+12)*table.length+1 := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨v,path⟩
    have head := depth ⟨v,path⟩ (by simp)
    have tail := ih (fun e member => depth e (by simp [member]))
    simp only [extend]
    split
    · split
      · simp only [List.length_append,List.length_cons,List.length_nil,concat_count]
        nlinarith
      · simp only [List.length_append,List.length_cons,List.length_nil]
        nlinarith
    · simp only [List.length_append,List.length_cons,List.length_nil]
      nlinarith

def next (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) (target : Fin n) : Traced (Option (input.graph.Walk source target)) :=
  let found := lookup input table target
  match found.value with
  | some path => ⟨some path,found.events++[⟨.branch,[1]⟩]⟩
  | none =>
      let result := extend input matrix table target
      ⟨result.value,found.events++[⟨.branch,[1]⟩]++result.events⟩

@[simp] theorem next_value (matrix : FlowDecomposition.FlowMatrix n) {source target : Fin n}
    (table : FlowDecomposition.Table input.graph source) :
    (next input matrix table target).value=
      FlowDecomposition.next input.graph (FlowDecomposition.matrixFlow matrix) table target := by
  simp only [next,FlowDecomposition.next,lookup_value]
  split <;> simp_all [extend_value]

theorem next_count (matrix : FlowDecomposition.FlowMatrix n) {source target : Fin n}
    (table : FlowDecomposition.Table input.graph source) (R : ℕ)
    (depth : FlowDecomposition.Depth input.graph table R) :
    (next input matrix table target).events.length≤(2*R+16)*table.length+3 := by
  have found := lookup_count input (target:=target) table
  have extended := extend_count input matrix (target:=target) table R depth
  simp only [next]
  split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> nlinarith

def collect (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) : List (Fin n) → Traced (FlowDecomposition.Table input.graph source)
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | target::rest =>
      let found := next input matrix table target
      let tail := collect matrix table rest
      match found.value with
      | none => ⟨tail.value,[⟨.scan,[target.val.size]⟩]++found.events++[⟨.branch,[1]⟩]++tail.events⟩
      | some path => ⟨⟨target,path⟩::tail.value,
          [⟨.scan,[target.val.size]⟩]++found.events++[⟨.branch,[1]⟩]++tail.events++
            [⟨.write,[target.val.size]⟩,⟨.cons,[target.val.size]⟩]⟩

@[simp] theorem collect_value (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) (targets : List (Fin n)) :
    (collect input matrix table targets).value=
      targets.filterMap (fun target => (FlowDecomposition.next input.graph
        (FlowDecomposition.matrixFlow matrix) table target).map fun path => ⟨target,path⟩) := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
    simp only [collect,next_value,List.filterMap_cons]
    split <;> simp_all

theorem collect_count (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) (targets : List (Fin n)) (R : ℕ)
    (depth : FlowDecomposition.Depth input.graph table R) :
    (collect input matrix table targets).events.length≤targets.length*((2*R+16)*table.length+7)+1 := by
  induction targets with
  | nil => simp [collect]
  | cons target rest ih =>
    have found := next_count input matrix (target:=target) table R depth
    simp only [collect]
    split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> nlinarith

def step (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) : Traced (FlowDecomposition.Table input.graph source) := do
  let indices ← indexList n
  collect input matrix table indices

@[simp] theorem step_value (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) :
    (step input matrix table).value=FlowDecomposition.step input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) table := by
  simp [step,Traced.bind_value,FlowDecomposition.step,FlowDecomposition.vertices]

theorem step_count (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) (R : ℕ)
    (depth : FlowDecomposition.Depth input.graph table R) :
    (step input matrix table).events.length≤n*((2*R+16)*table.length+10)+1 := by
  have collected := collect_count input matrix table (List.finRange n) R depth
  simp only [step,Traced.bind_events,Traced.bind_value,List.length_append,indexList_count,indexList_value]
  simp only [List.length_finRange] at collected
  nlinarith

def iterate (matrix : FlowDecomposition.FlowMatrix n) (source : Fin n) : ℕ → Traced (FlowDecomposition.Table input.graph source)
  | 0 => ⟨[⟨source,.nil⟩],[⟨.write,[1]⟩,⟨.write,[source.val.size]⟩,⟨.cons,[source.val.size]⟩]⟩
  | rounds+1 => do
      let _ ← emit .recurse [rounds.size] ()
      let previous ← iterate matrix source rounds
      step input matrix previous

@[simp] theorem iterate_value (matrix : FlowDecomposition.FlowMatrix n) (source : Fin n) (rounds : ℕ) :
    (iterate input matrix source rounds).value=FlowDecomposition.iterate input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp [iterate,Traced.bind_value,ih,FlowDecomposition.iterate]

theorem iterate_count (matrix : FlowDecomposition.FlowMatrix n) (source : Fin n) (rounds F : ℕ)
    (bounded : rounds≤F) :
    (iterate input matrix source rounds).events.length≤rounds*(n*((2*F+16)*n+10)+2)+3 := by
  induction rounds with
  | zero => simp [iterate]
  | succ rounds ih =>
    have previous := ih (by omega)
    have depth := FlowDecomposition.iterate_depth input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source rounds
    have length := FlowDecomposition.iterate_length input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source rounds
    have stepped := step_count input matrix (FlowDecomposition.iterate input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source rounds) rounds depth
    have enlarged : (2*rounds+16)*(FlowDecomposition.iterate input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source rounds).length≤(2*F+16)*n :=
      Nat.mul_le_mul (by omega) length
    simp only [iterate,Traced.bind_events,Traced.bind_value,emit_length,emit_value,iterate_value,List.length_append]
    nlinarith [Nat.mul_le_mul_left n enlarged]

def positivePath (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) : Traced (Option (input.graph.Path source target)) :=
  let table := iterate input matrix source n
  let found := lookup input table.value target
  match found.value with
  | none => ⟨none,table.events++found.events++[⟨.branch,[1]⟩]⟩
  | some walk =>
      let result := Paths.toPath walk
      ⟨some result.value,table.events++found.events++[⟨.branch,[1]⟩]++result.events++[⟨.write,[1]⟩]⟩

@[simp] theorem positivePath_value (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) :
    (positivePath input matrix source target).value=FlowDecomposition.positivePath input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source target := by
  simp only [positivePath,iterate_value,lookup_value,FlowDecomposition.positivePath]
  split <;> simp_all [Paths.toPath_value]

def searchBudget (n : ℕ) : ℕ := n*(n*((2*n+16)*n+10)+2)+4*n+6*(n+1)^2+6

theorem positivePath_count (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) :
    (positivePath input matrix source target).events.length≤searchBudget n := by
  have table := iterate_count input matrix source n n (by omega)
  have found := lookup_count input (target:=target) (iterate input matrix source n).value
  have length := FlowDecomposition.iterate_length input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source n
  have depth := FlowDecomposition.iterate_depth input.graph (Equiv.refl _)
      (FlowDecomposition.matrixFlow matrix) source n
  rw [iterate_value] at found
  simp only [positivePath]
  split
  · simp only [List.length_append,List.length_cons,List.length_nil,iterate_value]
    dsimp [searchBudget]
    omega
  · rename_i walk returned
    have lookup_return : FlowDecomposition.lookup input.graph
        (FlowDecomposition.iterate input.graph (Equiv.refl _) (FlowDecomposition.matrixFlow matrix) source n) target=some walk := by
      simpa only [lookup_value,iterate_value] using returned
    have walklen := FlowDecomposition.lookup_depth input.graph _ n depth lookup_return
    have erased := Paths.toPath_count walk
    have square : (walk.length+1)^2≤(n+1)^2 := Nat.pow_le_pow_left (by omega) 2
    simp only [List.length_append,List.length_cons,List.length_nil,iterate_value]
    dsimp [searchBudget]
    omega

end BuyAtBulk.Computation.Runtime.FlowSearch
