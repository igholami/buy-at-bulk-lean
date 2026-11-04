import BuyAtBulk.Computation.PolynomialLP.CompactBounds
import BuyAtBulk.Computation.Runtime.Primitive

/-! Closed literal compact-LP cells. Equality uses only explicit fixed-arity
sum tags and Fin-value comparisons; stored adjacency/endpoint/price accesses
are recorded. No equality or coefficient callback is supplied. -/
namespace BuyAtBulk.PolynomialLP.CompactTrace
open Computation Computation.Runtime Computation.Rational
open CompactFlow
variable {n h : ℕ}

def literalVarTag : VariableIndex (Fin n) h → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def literalRowTag : ConstraintIndex (Fin n) h → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

def variableDispatch (c : VariableIndex (Fin n) h) : List Event :=
  [⟨.read,[(literalVarTag c).size]⟩,⟨.branch,[(literalVarTag c).size]⟩]
def rowDispatch (r : ConstraintIndex (Fin n) h) : List Event :=
  [⟨.read,[(literalRowTag r).size]⟩,⟨.branch,[(literalRowTag r).size]⟩]

def finEqualCell {m : ℕ} (a b : Fin m) : Traced Bool :=
  ⟨decide (a.val=b.val),[⟨.read,[a.val.size]⟩,⟨.read,[b.val.size]⟩,⟨.natCompare,[a.val.size,b.val.size]⟩]⟩

@[simp] theorem finEqualCell_value {m : ℕ} (a b : Fin m) : (finEqualCell a b).value=decide (a=b) := by
  by_cases same : a=b
  · subst b;simp[finEqualCell]
  · have ne : a.val≠b.val := fun equal => same (Fin.ext equal)
    simp[finEqualCell,same,ne]
@[simp] theorem finEqualCell_count {m : ℕ} (a b : Fin m) : (finEqualCell a b).events.length=3 := rfl

def variableEqualCell (a b : VariableIndex (Fin n) h) : Traced Bool :=
  let prefixEvents : List Event := [⟨.read,[(literalVarTag a).size]⟩,⟨.read,[(literalVarTag b).size]⟩,
    ⟨.natCompare,[(literalVarTag a).size,(literalVarTag b).size]⟩,⟨.branch,[1]⟩]
  let compared : Traced Bool := match a,b with
    | .inl v,.inl w => finEqualCell v w
    | .inr (.inl (i,v)),.inr (.inl (j,w)) => do
      let first ← finEqualCell i j
      let second ← finEqualCell v w
      emit .branch [1,1] (first&&second)
    | .inr (.inr (i,u,v)),.inr (.inr (j,x,y)) => do
      let first ← finEqualCell i j
      let second ← finEqualCell u x
      let third ← finEqualCell v y
      emit .branch [1,1,1] (first&&second&&third)
    | _,_ => emit .write [1] false
  ⟨compared.value,prefixEvents++compared.events⟩

@[simp] theorem variableEqualCell_value (a b : VariableIndex (Fin n) h) :
    (variableEqualCell a b).value=decide (a=b) := by
  rcases a with v|⟨i,v⟩|⟨i,u,v⟩ <;>rcases b with w|⟨j,w⟩|⟨j,x,y⟩ <;>
    simp[variableEqualCell,Traced.bind_value,Bool.and_assoc]


def indicatorCell (b : Bool) : Traced ℚ := emit .branch [1] (if b then 1 else 0)
def literalCell (q : ℚ) : Traced ℚ := emit .write [(Code.ofRat q).bits] q

def negativeCell (q : ℚ) : Traced ℚ := emit .ratNeg [(Code.ofRat q).bits,(Code.ofRat (-q)).bits] (-q)
def subtractCell (a b : ℚ) : Traced ℚ := do
  let negative ← negativeCell b
  ratAdd a negative

def signCell (positive : Bool) (q : ℚ) : Traced ℚ := do
  let sign ← emit .branch [1] (if positive then (1 : ℚ) else -1)
  ratMul sign q

@[simp] theorem indicatorCell_value (b : Bool) : (indicatorCell b).value=(if b then 1 else 0) := rfl
@[simp] theorem literalCell_value (q : ℚ) : (literalCell q).value=q := rfl
@[simp] theorem negativeCell_value (q : ℚ) : (negativeCell q).value= -q := rfl
@[simp] theorem subtractCell_value (a b : ℚ) : (subtractCell a b).value=a-b := by simp[subtractCell,sub_eq_add_neg]
@[simp] theorem signCell_value (positive : Bool) (q : ℚ) : (signCell positive q).value=(if positive then 1 else -1)*q := rfl


def nodeCell (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) : Traced ℚ :=
  let result : Traced ℚ := match c with
    | .inr (.inl (j,w)) => do
      let first ← finEqualCell i j
      let second ← finEqualCell v w
      indicatorCell (first&&second)
    | _ => literalCell 0
  ⟨result.value,variableDispatch c++result.events⟩

def openingCell (v : Fin n) (c : VariableIndex (Fin n) h) : Traced ℚ :=
  let result : Traced ℚ := match c with
    | .inl w => do
      let equal ← finEqualCell v w
      indicatorCell equal
    | _ => literalCell 0
  ⟨result.value,variableDispatch c++result.events⟩

def transportCell (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) : Traced ℚ :=
  let result : Traced ℚ := match c with
    | .inr (.inr (j,u,w)) => do
      let first ← finEqualCell i j
      let endpoint ← emit .branch [1,u.val.size,w.val.size] (if incoming then w else u)
      let second ← finEqualCell v endpoint
      indicatorCell (first&&second)
    | _ => literalCell 0
  ⟨result.value,variableDispatch c++result.events⟩

def balanceCell (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) : Traced ℚ :=
  let node := nodeCell i v c
  let transport := transportCell incoming i v c
  let result := if incoming then subtractCell node.value transport.value else subtractCell transport.value node.value
  ⟨result.value,node.events++transport.events++[⟨.branch,[1]⟩]++result.events⟩

@[simp] theorem nodeCell_value (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (nodeCell i v c).value=CompactEncoding.nodeCoefficient i v c := by
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[nodeCell,indicatorCell,CompactEncoding.nodeCoefficient]

@[simp] theorem openingCell_value (v : Fin n) (c : VariableIndex (Fin n) h) :
    (openingCell v c).value=CompactEncoding.openingCoefficient v c := by
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[openingCell,indicatorCell,CompactEncoding.openingCoefficient]

@[simp] theorem transportCell_value (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (transportCell incoming i v c).value=(match c with
      | .inr (.inr (j,u,w)) => if i=j ∧ (if incoming then v=w else v=u) then (1 : ℚ) else 0
      | _ => 0) := by
  cases incoming <;>rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[transportCell,indicatorCell]

@[simp] theorem balanceCell_value (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (balanceCell incoming i v c).value=CompactEncoding.balanceCoefficient incoming i v c := by
  simp only[balanceCell,nodeCell_value,transportCell_value,CompactEncoding.balanceCoefficient]
  cases incoming <;>rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[CompactEncoding.nodeCoefficient]


def literalCoefficient (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) (c : VariableIndex (Fin n) h) : Traced ℚ :=
  let result : Traced ℚ := match r with
    | .inl (upper,d) => do
      let equal ← variableEqualCell d c
      let amount ← indicatorCell equal
      signCell upper amount
    | .inr (.inl (i,v)) => do
      let node ← nodeCell i v c
      let opening ← openingCell v c
      subtractCell node opening
    | .inr (.inr (.inl ((positive,incoming),(i,v)))) => do
      let balance ← balanceCell incoming i v c
      signCell positive balance
    | .inr (.inr (.inr (i,u,v))) => do
      let edge ← emit .read [u.val.size,v.val.size,1] data.adjacency[u.val][v.val]
      let edge ← branch edge
      if edge then literalCell 0 else do
        let equal ← variableEqualCell c (.inr (.inr (i,u,v)))
        indicatorCell equal
  ⟨result.value,rowDispatch r++result.events⟩


def literalBound (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) : Traced ℚ :=
  let result : Traced ℚ := match r with
    | .inl (upper,_) => indicatorCell upper
    | .inr (.inl _) => literalCell 0
    | .inr (.inr (.inl ((positive,incoming),(i,v)))) =>
      let endpoint := if incoming then emit .read [i.val.size,data.source[i.val].val.size] data.source[i.val]
        else emit .read [i.val.size,data.target[i.val].val.size] data.target[i.val]
      let matched := finEqualCell endpoint.value v
      let amount := indicatorCell matched.value
      let signed := if incoming then Traced.pure amount.value else negativeCell amount.value
      let output := signCell positive signed.value
      ⟨output.value,[⟨.branch,[1]⟩]++endpoint.events++matched.events++amount.events++[⟨.branch,[1]⟩]++signed.events++output.events⟩
    | .inr (.inr (.inr _)) => literalCell 0
  ⟨result.value,rowDispatch r++result.events⟩


def literalObjective (data : CompactEncoding.Data n h) (c : VariableIndex (Fin n) h) : Traced ℚ :=
  let result : Traced ℚ := match c with
    | .inl v => readRat data.buying v
    | .inr (.inl (i,v)) => do
      let demand ← readRat data.demand i
      let physical ← readRat data.physical v
      ratMul demand physical
    | .inr (.inr _) => literalCell 0
  ⟨result.value,variableDispatch c++result.events⟩


theorem literalCoefficient_value (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) (c : VariableIndex (Fin n) h) :
    (literalCoefficient data r c).value=CompactEncoding.coefficient data r c := by
  rcases r with ⟨upper,d⟩|⟨i,v⟩|⟨⟨positive,incoming⟩,i,v⟩|⟨i,u,v⟩
  · simp[literalCoefficient,CompactEncoding.coefficient,indicatorCell]
  · simp[literalCoefficient,CompactEncoding.coefficient]
  · simp[literalCoefficient,CompactEncoding.coefficient]
  · cases edge : data.adjacency[u.val][v.val] <;>simp[literalCoefficient,CompactEncoding.coefficient,indicatorCell,branch,edge]



theorem literalBound_value (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) :
    (literalBound data r).value=CompactEncoding.bound data r := by
  rcases r with ⟨upper,d⟩|⟨i,v⟩|⟨⟨positive,incoming⟩,i,v⟩|⟨i,u,v⟩
  · rfl
  · rfl
  · cases positive <;>cases incoming <;>simp[literalBound,CompactEncoding.bound,indicatorCell]
  · rfl


theorem literalObjective_value (data : CompactEncoding.Data n h) (c : VariableIndex (Fin n) h) :
    (literalObjective data c).value=CompactEncoding.objective data c := by
  rcases c with v|⟨i,v⟩|⟨i,u,v⟩ <;>rfl



@[simp] theorem variableDispatch_count (c : VariableIndex (Fin n) h) : (variableDispatch c).length=2 := rfl
@[simp] theorem rowDispatch_count (r : ConstraintIndex (Fin n) h) : (rowDispatch r).length=2 := rfl
@[simp] theorem indicatorCell_count (b : Bool) : (indicatorCell b).events.length=1 := rfl
@[simp] theorem literalCell_count (q : ℚ) : (literalCell q).events.length=1 := rfl
@[simp] theorem negativeCell_count (q : ℚ) : (negativeCell q).events.length=1 := rfl
@[simp] theorem subtractCell_count (a b : ℚ) : (subtractCell a b).events.length=3 := rfl
@[simp] theorem signCell_count (positive : Bool) (q : ℚ) : (signCell positive q).events.length=3 := rfl


theorem variableEqualCell_count (a b : VariableIndex (Fin n) h) : (variableEqualCell a b).events.length≤14 := by
  rcases a with v|⟨i,v⟩|⟨i,u,v⟩ <;>rcases b with w|⟨j,w⟩|⟨j,x,y⟩ <;>
    simp[variableEqualCell,Traced.bind_events,List.length_append,finEqualCell_count]


theorem nodeCell_count (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) : (nodeCell i v c).events.length≤9 := by
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[nodeCell,Traced.bind_events,List.length_append]


theorem openingCell_count (v : Fin n) (c : VariableIndex (Fin n) h) : (openingCell v c).events.length≤6 := by
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[openingCell,Traced.bind_events,List.length_append]


theorem transportCell_count (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (transportCell incoming i v c).events.length≤10 := by
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp[transportCell,Traced.bind_events,List.length_append]


theorem balanceCell_count (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (balanceCell incoming i v c).events.length≤23 := by
  have node := nodeCell_count i v c
  have transport := transportCell_count incoming i v c
  cases incoming <;>simp only[balanceCell,List.length_append,List.length_cons,List.length_nil,subtractCell_count,Bool.false_eq_true,ite_false,ite_true] <;>omega


theorem literalCoefficient_count (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) (c : VariableIndex (Fin n) h) :
    (literalCoefficient data r c).events.length≤64 := by
  rcases r with ⟨upper,d⟩|⟨i,v⟩|⟨⟨positive,incoming⟩,i,v⟩|⟨i,u,v⟩
  · have equal := variableEqualCell_count d c
    simp only[literalCoefficient,Traced.bind_events,Traced.bind_value,List.length_append,rowDispatch_count,indicatorCell_count,signCell_count]
    omega
  · have node := nodeCell_count i v c
    have opening := openingCell_count v c
    simp only[literalCoefficient,Traced.bind_events,Traced.bind_value,List.length_append,rowDispatch_count,subtractCell_count]
    omega
  · have balance := balanceCell_count incoming i v c
    simp only[literalCoefficient,Traced.bind_events,Traced.bind_value,List.length_append,rowDispatch_count,signCell_count]
    omega
  · have equal := variableEqualCell_count c (.inr (.inr (i,u,v)))
    cases edge : data.adjacency[u.val][v.val] <;>
      simp only[literalCoefficient,Traced.bind_events,Traced.bind_value,emit_value,branch,edge,Bool.false_eq_true,ite_false,ite_true,
        List.length_append,rowDispatch_count,emit_length,literalCell_count,indicatorCell_count] <;>omega


theorem literalBound_count (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) :
    (literalBound data r).events.length≤32 := by
  rcases r with ⟨upper,d⟩|⟨i,v⟩|⟨⟨positive,incoming⟩,i,v⟩|⟨i,u,v⟩
  · simp[literalBound]
  · simp[literalBound]
  · cases incoming <;>simp[literalBound,List.length_append,Traced.pure]
  · simp[literalBound]


theorem literalObjective_count (data : CompactEncoding.Data n h) (c : VariableIndex (Fin n) h) :
    (literalObjective data c).events.length≤8 := by
  rcases c with v|⟨i,v⟩|⟨i,u,v⟩ <;>simp[literalObjective,Traced.bind_events,List.length_append,readRat]


@[simp] theorem literalCoefficient_bits (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) (c : VariableIndex (Fin n) h) :
    (Code.ofRat (literalCoefficient data r c).value).bits≤4 := by
  rw[literalCoefficient_value]
  exact CompactEncoding.coefficient_bits data r c

@[simp] theorem literalBound_bits (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) :
    (Code.ofRat (literalBound data r).value).bits≤4 := by
  rw[literalBound_value]
  exact CompactEncoding.bound_bits data r


theorem literalObjective_bits (data : CompactEncoding.Data n h) (c : VariableIndex (Fin n) h) (L : ℕ)
    (buying : ∀ v : Fin n, (Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n, (Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h, (Code.ofRat data.demand[i.val]).bits≤L) :
    (Code.ofRat (literalObjective data c).value).bits≤4*L+8 := by
  rw[literalObjective_value]
  rcases c with v|⟨i,v⟩|⟨i,u,v⟩
  · exact (buying v).trans (by omega)
  · have product := ratMul_result_bits data.demand[i.val] data.physical[v.val]
    have d := demand i
    have p := physical v
    exact product.trans (by omega)
  · have zero : (Code.ofRat (0 : ℚ)).bits=3 := by decide
    simpa only[CompactEncoding.objective,zero] using (by omega : 3≤4*L+8)


def scalarWords (n h L : ℕ) := n+h+16*L+128

private theorem finWord {m : ℕ} (v : Fin m) : v.val.size≤m :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt)

private theorem varTag_word (c : VariableIndex (Fin n) h) : (literalVarTag c).size≤2 := by
  rcases c with v|⟨i,v⟩|⟨i,u,v⟩ <;>simp only[literalVarTag] <;>decide
private theorem rowTag_word (r : ConstraintIndex (Fin n) h) : (literalRowTag r).size≤2 := by
  rcases r with box|node|balance|arc <;>simp only[literalRowTag] <;>decide


theorem finEqualCell_words {m : ℕ} (a b : Fin m) (K : ℕ) (capacity : m≤K) :
    WordsWithin K (finEqualCell a b).events := by
  have aWord := (finWord a).trans capacity
  have bWord := (finWord b).trans capacity
  simp only[finEqualCell,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  exact ⟨aWord,bWord,aWord,bWord⟩


theorem variableDispatch_words (c : VariableIndex (Fin n) h) (K : ℕ) (capacity : 2≤K) :
    WordsWithin K (variableDispatch c) := by
  have word := (varTag_word c).trans capacity
  simpa only[variableDispatch,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using And.intro word word

theorem rowDispatch_words (r : ConstraintIndex (Fin n) h) (K : ℕ) (capacity : 2≤K) :
    WordsWithin K (rowDispatch r) := by
  have word := (rowTag_word r).trans capacity
  simpa only[rowDispatch,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using And.intro word word


theorem variableEqualCell_words (a b : VariableIndex (Fin n) h) (K : ℕ) (capacity : n+h+4≤K) :
    WordsWithin K (variableEqualCell a b).events := by
  have nodes (u v : Fin n) := finEqualCell_words u v K (by omega)
  have commodities (i j : Fin h) := finEqualCell_words i j K (by omega)
  have one : 1≤K := by omega
  have two : 2≤K := by omega
  have aTag := (varTag_word a).trans two
  have bTag := (varTag_word b).trans two
  rcases a with v|⟨i,v⟩|⟨i,u,v⟩ <;>rcases b with w|⟨j,w⟩|⟨j,x,y⟩ <;>
    simp only[variableEqualCell,Traced.bind_events,Traced.bind_value,emit_value,List.append_assoc,wordsWithin_append,
      emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals aesop


private theorem negCode_bits (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp[Code.ofRat,Code.bits]


theorem indicatorCell_bits (b : Bool) : (Code.ofRat (indicatorCell b).value).bits≤4 := by cases b <;>decide

theorem indicatorCell_words (b : Bool) (K : ℕ) (one : 1≤K) : WordsWithin K (indicatorCell b).events := by
  simpa[indicatorCell,emit,wordsWithin_cons] using one


theorem literalCell_words (q : ℚ) (K : ℕ) (input : (Code.ofRat q).bits≤K) : WordsWithin K (literalCell q).events := by
  simpa[literalCell,emit,wordsWithin_cons] using input


theorem negativeCell_bits (q : ℚ) : (Code.ofRat (negativeCell q).value).bits=(Code.ofRat q).bits := negCode_bits q

theorem negativeCell_words (q : ℚ) (K : ℕ) (input : (Code.ofRat q).bits≤K) : WordsWithin K (negativeCell q).events := by
  simp only[negativeCell,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,negCode_bits]
  exact ⟨input,input⟩


theorem subtractCell_bits (a b : ℚ) (aBits : (Code.ofRat a).bits≤4) (bBits : (Code.ofRat b).bits≤4) :
    (Code.ofRat (subtractCell a b).value).bits≤24 := by
  have result := ratAdd_result_bits a (-b)
  rw[negCode_bits] at result
  simpa only[subtractCell,Traced.bind_value,negativeCell_value,ratAdd_value] using result.trans (by omega)


theorem subtractCell_words (a b : ℚ) (K : ℕ) (capacity : 24≤K)
    (aBits : (Code.ofRat a).bits≤4) (bBits : (Code.ofRat b).bits≤4) :
    WordsWithin K (subtractCell a b).events := by
  have neg := negativeCell_words b K (by omega)
  have add : WordsWithin K (ratAdd a (-b)).events := by
    intro event member word present
    have result := ratAdd_words a (-b) event member word present
    rw[negCode_bits] at result
    omega
  simpa only[subtractCell,Traced.bind_events,Traced.bind_value,negativeCell_value,wordsWithin_append] using And.intro neg add


theorem signCell_words (positive : Bool) (q : ℚ) (K : ℕ) (capacity : 24≤K) (input : (Code.ofRat q).bits≤4) :
    WordsWithin K (signCell positive q).events := by
  have one : 1≤K := by omega
  have sign : (Code.ofRat (if positive then (1 : ℚ) else -1)).bits≤4 := by cases positive <;>decide
  have multiplied : WordsWithin K (ratMul (if positive then 1 else -1) q).events := by
    intro event member word present
    have actual := ratMul_words (if positive then 1 else -1) q event member word present
    omega
  simpa only[signCell,Traced.bind_events,Traced.bind_value,emit_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_singleton,forall_eq,and_true] using And.intro one multiplied


theorem nodeCell_bits (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) : (Code.ofRat (nodeCell i v c).value).bits≤4 := by
  rw[nodeCell_value]
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp only[CompactEncoding.nodeCoefficient]
  all_goals (try split_ifs) <;>norm_num[Code.ofRat,Code.bits]


theorem openingCell_bits (v : Fin n) (c : VariableIndex (Fin n) h) : (Code.ofRat (openingCell v c).value).bits≤4 := by
  rw[openingCell_value]
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp only[CompactEncoding.openingCoefficient]
  all_goals (try split_ifs) <;>norm_num[Code.ofRat,Code.bits]


theorem transportCell_bits (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (Code.ofRat (transportCell incoming i v c).value).bits≤4 := by
  rw[transportCell_value]
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>simp only
  all_goals (try split_ifs) <;>norm_num[Code.ofRat,Code.bits]


theorem balanceCell_bits (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) :
    (Code.ofRat (balanceCell incoming i v c).value).bits≤4 := by
  rw[balanceCell_value]
  cases incoming <;>rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>
    simp only[CompactEncoding.balanceCoefficient,CompactEncoding.nodeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  all_goals (try split_ifs) <;>norm_num[Code.ofRat,Code.bits]


theorem nodeCell_words (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) (K : ℕ) (capacity : n+h+4≤K) :
    WordsWithin K (nodeCell i v c).events := by
  have dispatch := variableDispatch_words c K (by omega)
  have nodes (u w : Fin n) := finEqualCell_words u w K (by omega)
  have commodities (j k : Fin h) := finEqualCell_words j k K (by omega)
  have one : 1≤K := by omega
  have zero : (Code.ofRat (0 : ℚ)).bits=3 := by decide
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>
    simp only[nodeCell,Traced.bind_events,Traced.bind_value,emit_value,wordsWithin_append,literalCell,indicatorCell,emit,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,zero]
  all_goals aesop <;>omega


theorem openingCell_words (v : Fin n) (c : VariableIndex (Fin n) h) (K : ℕ) (capacity : n+h+4≤K) :
    WordsWithin K (openingCell v c).events := by
  have dispatch := variableDispatch_words c K (by omega)
  have nodes (u w : Fin n) := finEqualCell_words u w K (by omega)
  have one : 1≤K := by omega
  have zero : (Code.ofRat (0 : ℚ)).bits=3 := by decide
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>
    simp only[openingCell,Traced.bind_events,Traced.bind_value,emit_value,wordsWithin_append,literalCell,indicatorCell,emit,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,zero]
  all_goals aesop <;>omega


theorem transportCell_words (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) (K : ℕ) (capacity : n+h+4≤K) :
    WordsWithin K (transportCell incoming i v c).events := by
  have dispatch := variableDispatch_words c K (by omega)
  have nodes (u w : Fin n) := finEqualCell_words u w K (by omega)
  have commodities (j k : Fin h) := finEqualCell_words j k K (by omega)
  have index (u : Fin n) := (finWord u).trans (show n≤K by omega)
  have one : 1≤K := by omega
  have zero : (Code.ofRat (0 : ℚ)).bits=3 := by decide
  rcases c with w|⟨j,w⟩|⟨j,u,w⟩ <;>
    simp only[transportCell,Traced.bind_events,Traced.bind_value,emit_value,wordsWithin_append,literalCell,indicatorCell,emit,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,zero]
  all_goals aesop <;>omega


theorem balanceCell_words (incoming : Bool) (i : Fin h) (v : Fin n) (c : VariableIndex (Fin n) h) (K : ℕ)
    (capacity : n+h+24≤K) : WordsWithin K (balanceCell incoming i v c).events := by
  have node := nodeCell_words i v c K (by omega)
  have transport := transportCell_words incoming i v c K (by omega)
  have first := subtractCell_words (nodeCell i v c).value (transportCell incoming i v c).value K (by omega)
    (nodeCell_bits i v c) (transportCell_bits incoming i v c)
  have second := subtractCell_words (transportCell incoming i v c).value (nodeCell i v c).value K (by omega)
    (transportCell_bits incoming i v c) (nodeCell_bits i v c)
  have one : 1≤K := by omega
  cases incoming <;>simp only[balanceCell,Bool.false_eq_true,ite_false,ite_true,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_singleton,forall_eq,and_true] <;>aesop


theorem literalCoefficient_words (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h)
    (c : VariableIndex (Fin n) h) (L : ℕ) :
    WordsWithin (scalarWords n h L) (literalCoefficient data r c).events := by
  let K := scalarWords n h L
  have capacity : n+h+24≤K := by dsimp[K,scalarWords];omega
  have one : 1≤K := by omega
  have dispatch := rowDispatch_words r K (by omega)
  rcases r with ⟨upper,d⟩|⟨i,v⟩|⟨⟨positive,incoming⟩,i,v⟩|⟨i,u,v⟩
  · have equal := variableEqualCell_words d c K (by omega)
    have amount := indicatorCell_words (variableEqualCell d c).value K one
    have signed := signCell_words upper (indicatorCell (variableEqualCell d c).value).value K (by omega) (indicatorCell_bits _)
    simpa only[literalCoefficient,Traced.bind_events,Traced.bind_value,List.append_assoc,wordsWithin_append] using
      And.intro dispatch (And.intro equal (And.intro amount signed))
  · have node := nodeCell_words i v c K (by omega)
    have opening := openingCell_words v c K (by omega)
    have subtracted := subtractCell_words (nodeCell i v c).value (openingCell v c).value K (by omega)
      (nodeCell_bits i v c) (openingCell_bits v c)
    simpa only[literalCoefficient,Traced.bind_events,Traced.bind_value,List.append_assoc,wordsWithin_append] using
      And.intro dispatch (And.intro node (And.intro opening subtracted))
  · have balance := balanceCell_words incoming i v c K capacity
    have signed := signCell_words positive (balanceCell incoming i v c).value K (by omega) (balanceCell_bits incoming i v c)
    simpa only[literalCoefficient,Traced.bind_events,Traced.bind_value,List.append_assoc,wordsWithin_append] using
      And.intro dispatch (And.intro balance signed)
  · have ui := (finWord u).trans (show n≤K by omega)
    have vi := (finWord v).trans (show n≤K by omega)
    have equal := variableEqualCell_words c (.inr (.inr (i,u,v))) K (by omega)
    have amount := indicatorCell_words (variableEqualCell c (.inr (.inr (i,u,v)))).value K one
    have zero := literalCell_words 0 K (by
      have bits : (Code.ofRat (0 : ℚ)).bits=3 := by decide
      rw[bits]
      omega)
    cases edge : data.adjacency[u.val][v.val] <;>
      simp only[literalCoefficient,Traced.bind_events,Traced.bind_value,emit_value,branch,edge,Bool.false_eq_true,ite_false,ite_true,
        wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals aesop


theorem literalBound_words (data : CompactEncoding.Data n h) (r : ConstraintIndex (Fin n) h) (L : ℕ) :
    WordsWithin (scalarWords n h L) (literalBound data r).events := by
  let K := scalarWords n h L
  have capacity : n+h+24≤K := by dsimp[K,scalarWords];omega
  have one : 1≤K := by omega
  have dispatch := rowDispatch_words r K (by omega)
  have zero := literalCell_words 0 K (by
    have bits : (Code.ofRat (0 : ℚ)).bits=3 := by decide
    rw[bits]
    omega)
  rcases r with ⟨upper,d⟩|⟨i,v⟩|⟨⟨positive,incoming⟩,i,v⟩|⟨i,u,v⟩
  · simpa only[literalBound,wordsWithin_append] using And.intro dispatch (indicatorCell_words upper K one)
  · simpa only[literalBound,wordsWithin_append] using And.intro dispatch zero
  · let endpoint := if incoming then emit .read [i.val.size,data.source[i.val].val.size] data.source[i.val]
      else emit .read [i.val.size,data.target[i.val].val.size] data.target[i.val]
    let amount := indicatorCell (finEqualCell endpoint.value v).value
    let signed := if incoming then Traced.pure amount.value else negativeCell amount.value
    have ii := (finWord i).trans (show h≤K by omega)
    have sourceWord := (finWord data.source[i.val]).trans (show n≤K by omega)
    have targetWord := (finWord data.target[i.val]).trans (show n≤K by omega)
    have endpoint_words : WordsWithin K endpoint.events := by
      cases incoming <;>simp only[endpoint,Bool.false_eq_true,ite_false,ite_true,emit,wordsWithin_cons,wordsWithin_nil,
        List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] <;>aesop
    have equal := finEqualCell_words endpoint.value v K (by omega)
    have amount_words := indicatorCell_words (finEqualCell endpoint.value v).value K one
    have amount_bits : (Code.ofRat amount.value).bits≤4 := indicatorCell_bits _
    have signed_words : WordsWithin K signed.events := by
      cases incoming
      · exact negativeCell_words amount.value K (by omega)
      · simp[signed,Traced.pure,WordsWithin]
    have signed_bits : (Code.ofRat signed.value).bits≤4 := by
      cases incoming
      · simpa only[signed,Bool.false_eq_true,ite_false,negativeCell_bits] using amount_bits
      · exact amount_bits
    have multiplied := signCell_words positive signed.value K (by omega) signed_bits
    simp only[literalBound,List.append_assoc,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
    exact ⟨dispatch,one,endpoint_words,equal,amount_words,one,signed_words,multiplied⟩
  · simpa only[literalBound,wordsWithin_append] using And.intro dispatch zero


theorem literalObjective_words (data : CompactEncoding.Data n h) (c : VariableIndex (Fin n) h) (L : ℕ)
    (buying : ∀ v : Fin n, (Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n, (Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h, (Code.ofRat data.demand[i.val]).bits≤L) :
    WordsWithin (scalarWords n h L) (literalObjective data c).events := by
  let K := scalarWords n h L
  have capacity : n+h+24≤K := by dsimp[K,scalarWords];omega
  have dispatch := variableDispatch_words c K (by omega)
  rcases c with v|⟨i,v⟩|⟨i,u,v⟩
  · have vi := (finWord v).trans (show n≤K by omega)
    have price := (buying v).trans (show L≤K by dsimp[K,scalarWords];omega)
    simpa only[literalObjective,readRat,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true] using And.intro dispatch (And.intro vi price)
  · have vi := (finWord v).trans (show n≤K by omega)
    have ii := (finWord i).trans (show h≤K by omega)
    have price := (physical v).trans (show L≤K by dsimp[K,scalarWords];omega)
    have dem := (demand i).trans (show L≤K by dsimp[K,scalarWords];omega)
    have multiplied : WordsWithin K (ratMul data.demand[i.val] data.physical[v.val]).events := by
      intro event member word present
      have actual := ratMul_words data.demand[i.val] data.physical[v.val] event member word present
      have d := demand i
      have p := physical v
      dsimp[K,scalarWords]
      omega
    simpa only[literalObjective,Traced.bind_events,Traced.bind_value,readRat,emit_value,emit,List.append_assoc,wordsWithin_append,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
      And.intro dispatch (And.intro (And.intro ii dem) (And.intro (And.intro vi price) multiplied))
  · have zero := literalCell_words 0 K (by
      have bits : (Code.ofRat (0 : ℚ)).bits=3 := by decide
      rw[bits]
      omega)
    simpa only[literalObjective,wordsWithin_append] using And.intro dispatch zero

end BuyAtBulk.PolynomialLP.CompactTrace
