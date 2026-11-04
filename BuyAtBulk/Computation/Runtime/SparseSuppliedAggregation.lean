import BuyAtBulk.Computation.Runtime.OriginalNumeric
import BuyAtBulk.Computation.Runtime.Weights
import BuyAtBulk.Computation.FlowDecomposition.Encoding

/-! Actual weighted-path aggregation into directed transport matrices. Every
walk edge is scanned and tested; rational additions use the instrumented sum. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational Original
variable {n : ℕ} {G : SimpleGraph (Fin n)}

def arcTerms (weight : ℚ) (u v : Fin n) {s t : Fin n} : G.Walk s t → Traced (List ℚ)
  | .nil => ⟨[], [⟨.branch,[1]⟩]⟩
  | @SimpleGraph.Walk.cons _ _ a b _ _ tail =>
    let rest := arcTerms weight u v tail
    let q := if a=u ∧ b=v then weight else 0
    ⟨q::rest.value, [⟨.branch,[1]⟩,⟨.scan,[a.val.size,b.val.size]⟩,
      ⟨.natCompare,[a.val.size,u.val.size]⟩,⟨.natCompare,[b.val.size,v.val.size]⟩,
      ⟨.branch,[1]⟩,⟨.read,[(Code.ofRat weight).bits]⟩] ++ rest.events ++
      [⟨.cons,[(Code.ofRat q).bits]⟩]⟩

@[simp] theorem arcTerms_length (weight : ℚ) (u v : Fin n) {s t : Fin n} (p : G.Walk s t) :
    (arcTerms weight u v p).value.length = p.length := by
  induction p <;> simp_all [arcTerms]

@[simp] theorem arcTerms_sum (weight : ℚ) (u v : Fin n) {s t : Fin n} (p : G.Walk s t) :
    (arcTerms weight u v p).value.sum = weight * CompactFlow.transportVisits p u v := by
  induction p with
  | nil => simp [arcTerms,CompactFlow.transportVisits]
  | cons edge tail ih =>
    simp only [arcTerms,List.sum_cons,CompactFlow.transportVisits,mul_add,ih]
    split_ifs <;> simp

theorem arcTerms_count (weight : ℚ) (u v : Fin n) {s t : Fin n} (p : G.Walk s t) :
    (arcTerms weight u v p).events.length = 7*p.length+1 := by
  induction p <;> simp_all [arcTerms] <;> omega

theorem arcTerms_bits (weight : ℚ) (u v : Fin n) {s t : Fin n} (p : G.Walk s t)
    (L : ℕ) (constant : 3 ≤ L) (bits : (Code.ofRat weight).bits ≤ L) :
    ∀ q ∈ (arcTerms weight u v p).value, (Code.ofRat q).bits ≤ L := by
  induction p with
  | nil => simp [arcTerms]
  | cons edge tail ih =>
    simp only [arcTerms,List.mem_cons,forall_eq_or_imp]
    constructor
    · split_ifs
      · exact bits
      · exact constant
    · exact ih

theorem arcTerms_words (weight : ℚ) (u v : Fin n) {s t : Fin n} (p : G.Walk s t)
    (L : ℕ) (constant : 3 ≤ L) (bits : (Code.ofRat weight).bits ≤ L) :
    WordsWithin (n+L) (arcTerms weight u v p).events := by
  have index (a : Fin n) : a.val.size ≤ n+L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have one : 1 ≤ n+L := by omega
  induction p with
  | nil => simp [arcTerms,WordsWithin,one]
  | @cons a b t edge tail ih =>
    have qb : (Code.ofRat (if a=u ∧ b=v then weight else 0)).bits ≤ n+L := by
      split_ifs
      · omega
      · change 3 ≤ n+L;omega
    simp [arcTerms,wordsWithin_append,wordsWithin_cons,index,one,ih,qb,bits.trans (Nat.le_add_left L n)]

def listTerms {s t : Fin n} (u v : Fin n) : FlowDecomposition.WeightedPaths G s t → Traced (List ℚ)
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | e::rest =>
    let head := arcTerms e.1 u v e.2.val
    let tail := listTerms u v rest
    ⟨head.value++tail.value,[⟨.branch,[1]⟩,⟨.scan,[1]⟩]++head.events++tail.events++
      head.value.map (fun q=>⟨.cons,[(Code.ofRat q).bits]⟩)⟩

@[simp] theorem listTerms_sum {s t : Fin n} (u v : Fin n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (listTerms u v entries).value.sum =
      (entries.map fun e=>e.1*CompactFlow.transportVisits e.2.val u v).sum := by
  induction entries <;> simp_all [listTerms]

theorem listTerms_length {s t : Fin n} (u v : Fin n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (listTerms u v entries).value.length ≤ entries.length*n := by
  induction entries with
  | nil => simp [listTerms]
  | cons e rest ih =>
    have bound := e.2.property.length_lt
    simp only [listTerms,List.length_append,arcTerms_length,List.length_cons]
    have : Fintype.card (Fin n)=n := Fintype.card_fin n
    nlinarith

theorem listTerms_count {s t : Fin n} (u v : Fin n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (listTerms u v entries).events.length ≤ entries.length*(8*n+3)+1 := by
  induction entries with
  | nil => simp [listTerms]
  | cons e rest ih =>
    have bound := e.2.property.length_lt
    simp only [listTerms,List.length_append,List.length_cons,List.length_nil,List.length_map,arcTerms_count,arcTerms_length]
    have : Fintype.card (Fin n)=n := Fintype.card_fin n
    nlinarith

theorem listTerms_bits {s t : Fin n} (u v : Fin n) (entries : FlowDecomposition.WeightedPaths G s t)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    ∀ q∈(listTerms u v entries).value,(Code.ofRat q).bits ≤ L := by
  induction entries with
  | nil => simp [listTerms]
  | cons e rest ih =>
    intro q mem
    simp only [listTerms,List.mem_append] at mem
    exact mem.elim (arcTerms_bits e.1 u v e.2.val L constant (bits e (by simp)) q)
      (ih (fun e mem=>bits e (by simp[mem])) q)

theorem listTerms_words {s t : Fin n} (u v : Fin n) (entries : FlowDecomposition.WeightedPaths G s t)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    WordsWithin (n+L) (listTerms u v entries).events := by
  have one : 1 ≤ n+L := by omega
  induction entries with
  | nil => simp [listTerms,WordsWithin,one]
  | cons e rest ih =>
    have head := arcTerms_words e.1 u v e.2.val L constant (bits e (by simp))
    have tail := ih (fun e mem=>bits e (by simp[mem]))
    have copied : WordsWithin (n+L) ((arcTerms e.1 u v e.2.val).value.map (fun q=>⟨Operation.cons,[(Code.ofRat q).bits]⟩)) := by
      intro event member word present
      obtain ⟨q,mem,rfl⟩ := List.mem_map.mp member
      simp only [List.mem_singleton] at present
      subst word
      exact (arcTerms_bits e.1 u v e.2.val L constant (bits e (by simp)) q mem).trans (by omega)
    simp [listTerms,wordsWithin_append,wordsWithin_cons,one,head,tail,copied]

def cell {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) (u v : Fin n) : Traced ℚ :=
  let terms := listTerms u v entries
  let result := ratSum terms.value
  ⟨result.value,terms.events++result.events⟩

@[simp] theorem cell_value {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) (u v : Fin n) :
    (cell entries u v).value=(entries.map fun e=>e.1*CompactFlow.transportVisits e.2.val u v).sum := by
  simp [cell]

theorem cell_count {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) (u v : Fin n) :
    (cell entries u v).events.length ≤ entries.length*(14*n+3)+3 := by
  have := listTerms_count u v entries
  have := listTerms_length u v entries
  simp only [cell,List.length_append,ratSum_count]
  nlinarith

def cellBits (n k L : ℕ) := 2*(2*k*n+1)*(L+6)+2
 def cellWords (n k L : ℕ) := n+L+(8*k*n+6)*(L+6)+12

 theorem cell_bits {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) (u v : Fin n)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    (Code.ofRat (cell entries u v).value).bits ≤ cellBits n entries.length L := by
  have bounds := listTerms_bits u v entries L constant bits
  have result := HelperExpressions.sum_rat_bits (listTerms u v entries).value (L+6)
    (by omega) (fun q mem=>by have := bounds q mem;omega)
  have length := listTerms_length u v entries
  simp only [cell,ratSum_value]
  dsimp [cellBits]
  nlinarith

 theorem cell_words {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) (u v : Fin n)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    WordsWithin (cellWords n entries.length L) (cell entries u v).events := by
  have first := (listTerms_words u v entries L constant bits).mono
    (show n+L ≤ cellWords n entries.length L by dsimp[cellWords];omega)
  have bounds := listTerms_bits u v entries L constant bits
  have last := ratSum_general_words (listTerms u v entries).value (L+6)
    (by omega) (fun q mem=>by have := bounds q mem;omega)
  have length := listTerms_length u v entries
  apply (wordsWithin_append _ _ _).mpr
  exact ⟨first,last.mono (by dsimp[cellWords];nlinarith)⟩

 def aggregate {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) :
    Traced (FlowDecomposition.FlowMatrix n) :=
  Weights.materialize (fun u=>Weights.materialize (cell entries u) (fun q=>(Code.ofRat q).bits))
    (fun _=>n.size)

 @[simp] theorem aggregate_value {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) (u v : Fin n) :
    (aggregate entries).value[u.val][v.val] =
      (entries.map fun e=>e.1*CompactFlow.transportVisits e.2.val u v).sum := by
  simp [aggregate]

 theorem aggregate_count {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t) :
    (aggregate entries).events.length ≤ n*(n*(entries.length*(14*n+3)+5)+3)+1 := by
  apply Weights.materialize_count
  intro u
  exact Weights.materialize_count _ _ _ (cell_count entries u)

 def aggregateWords (n k L : ℕ) := cellWords n k L+cellBits n k L+n

 theorem aggregate_words {s t : Fin n} (entries : FlowDecomposition.WeightedPaths G s t)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    WordsWithin (aggregateWords n entries.length L) (aggregate entries).events := by
  apply Weights.materialize_words
  · dsimp[aggregateWords];omega
  · intro u
    apply Weights.materialize_words
    · dsimp[aggregateWords];omega
    · intro v;exact (cell_words entries u v L constant bits).mono (by dsimp[aggregateWords];omega)
    · intro v;exact (cell_bits entries u v L constant bits).trans (by dsimp[aggregateWords];omega)
  · intro u
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[aggregateWords];omega)

end BuyAtBulk.Computation.Runtime.SparseSupplied
