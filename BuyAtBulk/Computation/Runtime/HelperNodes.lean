import BuyAtBulk.Computation.Runtime.MaterializedHelper
import BuyAtBulk.Computation.Runtime.RawBridge

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio m : ℕ}

theorem cachedChoose_length (stored : HelperConstruction.StoredTables n m) (selected remaining : List (Fin n)) :
    (CachedHelper.choose stored selected remaining).value.length≤selected.length+remaining.length := by
  induction remaining generalizing selected with
  | nil => simp [CachedHelper.choose]
  | cons v rest ih =>
    simp only [CachedHelper.choose]
    split
    · exact (ih selected).trans (by simp only [List.length_cons] <;> omega)
    · split
      · exact (ih selected).trans (by simp only [List.length_cons] <;> omega)
      · exact (ih (v::selected)).trans (by simp only [List.length_cons] <;> omega)

def appendNodes : List (Fin n) → List (Fin n) → Traced (List (Fin n))
  | [],right => emit .branch [1] right
  | v::rest,right => do
      let _ ← emit .scan [v.val.size] ()
      let tail ← appendNodes rest right
      emit .cons [v.val.size] (v::tail)

@[simp] theorem appendNodes_value (left right : List (Fin n)) :
    (appendNodes left right).value=left++right := by
  induction left <;> simp_all [appendNodes,Traced.bind_value]

@[simp] theorem appendNodes_count (left right : List (Fin n)) :
    (appendNodes left right).events.length=2*left.length+1 := by
  induction left <;> simp_all [appendNodes,Traced.bind_events,List.length_append] <;> omega

theorem appendNodes_words (left right : List (Fin n)) (K : ℕ) (indices : n≤K) (one : 1≤K) :
    WordsWithin K (appendNodes left right).events := by
  induction left with
  | nil => simp [appendNodes,emit,WordsWithin,one]
  | cons v rest ih =>
    have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;omega)
    simpa only [appendNodes,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
      forall_eq,and_true] using And.intro vi (And.intro ih vi)

def nodes (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) : Traced (List (Fin n)) := do
  let stored ← tables buying opening budget database rows
  let order ← indexList n
  let heavy ← CoefficientPipeline.heavyScan opening h order
  let chosen ← RawBridge.trace (CachedHelper.choose stored [] order)
  appendNodes heavy chosen

@[simp] theorem nodes_value (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    (nodes buying opening budget database rows).value=
      (Core.heavyVertices (Equiv.refl _) (fun v => opening[v.val]) h)++
      (HelperEvaluation.original (SourceCoefficients.tables buying opening budget database rows).tables [] (List.finRange n)).1 := by
  simp [nodes,Traced.bind_value,tables_value,CachedHelper.choose_value,CoefficientPipeline.heavyScan_value,
    Core.heavyVertices,Core.vertexOrder]

theorem nodes_length (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    (nodes buying opening budget database rows).value.length≤2*n := by
  have chosen := cachedChoose_length (SourceCoefficients.tables buying opening budget database rows) [] (List.finRange n)
  have heavy := SourceCoefficients.heavy_length (h:=h) opening
  rw [nodes_value,List.length_append]
  rw [CachedHelper.choose_value] at chosen
  simpa only [List.length_nil,List.length_finRange,Nat.zero_add,two_mul] using Nat.add_le_add heavy chosen

end BuyAtBulk.Computation.Runtime.MaterializedHelper
