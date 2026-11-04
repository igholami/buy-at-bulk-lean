import BuyAtBulk.Computation.PolynomialLP.RecoveryMonotonicity

/-! Native coordinate-face optimization. Each basis objective is materialized;
all appended faces, real feasibility queries and returned list cells are traced. -/
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Rational ObjectiveRuntime
variable {n m : ℕ}

def coordinateObjectiveTrace (i : Fin n) : Traced (Vector ℚ n) :=
  Weights.materialize (fun j =>
    ⟨if j=i then 1 else 0,[⟨.natCompare,[j.val.size,i.val.size]⟩,⟨.branch,[1]⟩]⟩)
    (fun q => (Code.ofRat q).bits)

@[simp] theorem coordinateObjectiveTrace_value (i : Fin n) :
    (coordinateObjectiveTrace i).value=coordinateObjective i := by
  apply Vector.ext
  intro j hj
  simp [coordinateObjectiveTrace,coordinateObjective,Weights.materialize]

theorem coordinateObjectiveTrace_count (i : Fin n) :
    (coordinateObjectiveTrace i).events.length≤4*n+1 := by
  simpa [coordinateObjectiveTrace,Nat.mul_comm] using Weights.materialize_count
    (fun j : Fin n => (⟨if j=i then (1:ℚ) else 0,[⟨.natCompare,[j.val.size,i.val.size]⟩,⟨.branch,[1]⟩]⟩ : Traced ℚ))
    (fun q => (Code.ofRat q).bits) 2 (by intro j; simp)

theorem coordinateObjectiveTrace_words (i : Fin n) (W : ℕ) (indices : n+4≤W) :
    WordsWithin W (coordinateObjectiveTrace i).events := by
  have bound (j : Fin n) : j.val.size≤W :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := j.isLt; omega)
  apply Weights.materialize_words _ _ _ (by omega)
  · intro j
    simp only [wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,and_true]
    exact ⟨⟨bound j,bound i⟩,by omega⟩
  · intro j
    change (Code.ofRat (if j=i then (1:ℚ) else 0)).bits≤W
    split_ifs <;> norm_num [Code.ofRat,Code.bits] <;> omega

def coordinateLoopTrace (K : ℕ) (indices : List (Fin n)) {m : ℕ}
    (input : Stored (n:=n) (m:=m)) : Traced (Option (List ℚ)) :=
  match indices with
  | [] => ⟨some [],[⟨.branch,[1]⟩]⟩
  | i::rest =>
    let objective := coordinateObjectiveTrace i
    let current := withObjectiveTrace input objective.value
    let recovered := recoverActual current.value K
    match recovered.value with
    | none => ⟨none,[⟨.scan,[1]⟩]++objective.events++current.events++recovered.events++[⟨.branch,[1]⟩]⟩
    | some value =>
      let fixed := fixTrace current.value current.value.objective value
      let tail := coordinateLoopTrace K rest fixed.value
      ⟨tail.value.map (value::·),[⟨.scan,[1]⟩]++objective.events++current.events++recovered.events++
        [⟨.branch,[1]⟩]++fixed.events++tail.events++[⟨.branch,[1]⟩,⟨.write,[(Code.ofRat value).bits]⟩]⟩
termination_by indices.length

@[simp] theorem coordinateLoopTrace_value (K : ℕ) (indices : List (Fin n))
    (input : Stored (n:=n) (m:=m)) :
    (coordinateLoopTrace K indices input).value=coordinateLoop K indices input := by
  induction indices generalizing m with
  | nil => simp [coordinateLoopTrace,coordinateLoop]
  | cons i rest ih =>
    simp only [coordinateLoopTrace,coordinateObjectiveTrace_value,withObjectiveTrace_value,
      recoverActual_value,coordinateLoop]
    split <;> simp_all only [Traced.value,fixTrace_value,Option.bind_none,Option.bind_some]

def coordinateStepCount (n M L K : ℕ) :=
  4*n+1+(3*n+2)+recoverCount n M L K+(2*M+1)*(3*n+13)+4*n+12+4

def coordinateLoopCount (n M L K steps : ℕ) := steps*coordinateStepCount n M L K+1

def coordinateLoopWords (n M L K : ℕ) := recoverWordBudget n M L K+n+M+L+K+20

@[gcongr] theorem coordinateStepCount_mono {n n' M M' L L' K K' : ℕ}
    (dim : n≤n') (rows : M≤M') (cells : L≤L') (vertices : K≤K') :
    coordinateStepCount n M L K≤coordinateStepCount n' M' L' K' := by
  dsimp only [coordinateStepCount]
  gcongr

/-- Encoding and complexity invariants are derived from the original feasible
polytope, whose vertices survive every attained coordinate face. -/
theorem coordinateLoopTrace_runtime {m₀ : ℕ}
    (original : Stored (n:=n) (m:=m₀)) (K L M : ℕ)
    (cube : original.problem.InUnitCube)
    (word_bound : ∀ x, original.problem.Feasible x → original.problem.Vertex x →
      ∀ j, (Code.ofRat (x j)).bits≤K)
    (constant : 4≤L) (coordinate : K≤L)
    (indices : List (Fin n)) (input : Stored (n:=n) (m:=m))
    (room : m+2*indices.length≤M) (cells : CellBits input L)
    (subset : ∀ x, input.problem.Feasible x → original.problem.Feasible x)
    (vertices : ∀ x, input.problem.Feasible x → input.problem.Vertex x → original.problem.Vertex x)
    (nonempty : ∃ x, input.problem.Feasible x) :
    (coordinateLoopTrace K indices input).events.length≤coordinateLoopCount n M L K indices.length ∧
      WordsWithin (coordinateLoopWords n M L K) (coordinateLoopTrace K indices input).events := by
  induction indices generalizing m with
  | nil =>
    simp only [coordinateLoopTrace,List.length_nil,coordinateLoopCount,Nat.zero_mul,Nat.zero_add,
      List.length_cons,le_refl,true_and,wordsWithin_cons,wordsWithin_nil]
    constructor
    · intro word member
      simp only [List.mem_singleton] at member
      subst word
      dsimp only [coordinateLoopWords]
      omega
    · trivial
  | cons i rest ih =>
    let current := input.withObjective (coordinateObjective i)
    have current_cells : CellBits current L := cells.withObjective _
      (fun j => (coordinateObjective_bits i j).trans constant)
    have current_cube : current.problem.InUnitCube := fun x hx => cube x (subset x hx)
    have current_words : ∀ x, current.problem.Feasible x → current.problem.Vertex x →
        ∀ j, (Code.ofRat (x j)).bits≤K :=
      fun x hx hv => word_bound x (subset x hx) (vertices x hx hv)
    obtain ⟨value,computed,v,vfeasible,vvertex,value_eq,minimal⟩ :=
      recoverValue_correct current K current_cube nonempty current_words
    have scalar := recover_coordinate_bound original K cube word_bound input subset vertices nonempty i value computed
    let next := current.fix current.objective value
    have next_subset : ∀ x, next.problem.Feasible x → original.problem.Feasible x :=
      fun x hx => subset x ((current.fix_feasible current.objective value x).mp hx).1
    have next_vertices : ∀ x, next.problem.Feasible x → next.problem.Vertex x → original.problem.Vertex x := by
      intro x hx hv
      have previous := (current.fix_feasible current.objective value x).mp hx
      have optimal : ∀ y, current.problem.Feasible y → current.problem.objective x≤current.problem.objective y := by
        intro y hy
        change rowForm current.objective x≤_
        rw [previous.2]
        exact minimal y hy
      exact vertices x previous.1 (current.fix_vertex value x hx optimal hv)
    have next_nonempty : ∃ x, next.problem.Feasible x :=
      ⟨v,(current.fix_feasible current.objective value v).mpr ⟨vfeasible,value_eq⟩⟩
    have next_cells : CellBits next L := current_cells.fix _ _ current_cells.objective (scalar.trans coordinate)
    have next_room : m+1+1+2*rest.length≤M := by simp only [List.length_cons] at room; omega
    have tail := ih next next_room next_cells next_subset next_vertices next_nonempty
    have rows : m≤M := by omega
    have objectiveCount := coordinateObjectiveTrace_count i
    have currentCount := withObjectiveTrace_count input (coordinateObjective i)
    have recoveredCount := (recoverActual_count current L K current_cells).trans
      (recoverCount_mono (le_refl n) rows (le_refl L) (le_refl K))
    have fixedCount := fixTrace_count current current.objective value
    have fixedUniform : (fixTrace current current.objective value).events.length≤
        (2*M+1)*(3*n+13)+4*n+12 := fixedCount.trans (by gcongr)
    let W := coordinateLoopWords n M L K
    have small : n+M+L+K+4≤W := by dsimp only [W,coordinateLoopWords]; omega
    have objectiveWords := coordinateObjectiveTrace_words i W (by omega)
    have currentWords := withObjectiveTrace_words input (coordinateObjective i) W (by omega)
      (fun j => (coordinateObjective_bits i j).trans (by omega))
    have recoveredWords : WordsWithin W (recoverActual current K).events :=
      (recoverActual_words current L K current_cells).mono
        ((recoverWordBudget_mono (le_refl n) rows (le_refl L) (le_refl K)).trans
          (by dsimp only [W,coordinateLoopWords]; omega))
    have fixedWords := fixTrace_words current current.objective value W (by omega)
      (fun a b => (current_cells.coefficients a b).trans (by omega))
      (fun a => (current_cells.bounds a).trans (by omega))
      (fun j => (current_cells.objective j).trans (by omega)) (scalar.trans (by omega))
    have computedTrace : (recoverActual current K).value=some value :=
      (recoverActual_value current K).trans computed
    simp only [coordinateLoopTrace,coordinateObjectiveTrace_value,withObjectiveTrace_value]
    rw [computedTrace]
    simp only [fixTrace_value]
    constructor
    · simp only [List.length_append,List.length_cons,List.length_nil]
      change 1+(coordinateObjectiveTrace i).events.length+
        (withObjectiveTrace input (coordinateObjective i)).events.length+
        (recoverActual current K).events.length+1+
        (fixTrace current current.objective value).events.length+
        (coordinateLoopTrace K rest next).events.length+2≤_
      have inductionCount := tail.1
      dsimp only [coordinateLoopCount,coordinateStepCount] at inductionCount ⊢
      nlinarith
    · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
        List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      exact ⟨⟨⟨⟨⟨⟨⟨by omega,objectiveWords⟩,currentWords⟩,recoveredWords⟩,by omega⟩,
        fixedWords⟩,tail.2⟩,by omega,scalar.trans (by omega)⟩

end BuyAtBulk.PolynomialLP
