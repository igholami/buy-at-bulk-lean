import BuyAtBulk.Computation.Runtime.ZeroProjectionRuntime
import BuyAtBulk.Computation.Runtime.CoreOutputBound

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def appendEntries (source target : Vector (Fin n) h) :
    List (StoredBatch.Entry input source target) → List (StoredBatch.Entry input source target) → Traced (List (StoredBatch.Entry input source target))
  | [],right => emit .branch [1] right
  | entry::rest,right =>
    let next := appendEntries source target rest right
    ⟨entry::next.value,[⟨.scan,[entry.1.val.size]⟩]++next.events++[⟨.cons,[entry.1.val.size]⟩]⟩

@[simp] theorem appendEntries_value (source target : Vector (Fin n) h)
    (left right : List (StoredBatch.Entry input source target)) :
    (appendEntries input source target left right).value=left++right := by
  induction left with
  | nil => rfl
  | cons entry rest ih => simp[appendEntries,ih]

@[simp] theorem appendEntries_count (source target : Vector (Fin n) h)
    (left right : List (StoredBatch.Entry input source target)) :
    (appendEntries input source target left right).events.length=2*left.length+1 := by
  induction left with
  | nil => rfl
  | cons entry rest ih => simp[appendEntries,ih,Nat.mul_add]

theorem appendEntries_words (source target : Vector (Fin n) h)
    (left right : List (StoredBatch.Entry input source target)) :
    WordsWithin (h+1) (appendEntries input source target left right).events := by
  induction left with
  | nil => simp[appendEntries,emit,WordsWithin]
  | cons entry rest ih =>
    have ii : entry.1.val.size ≤ h+1 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := entry.1.isLt;omega)
    simpa only[appendEntries,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using And.intro (And.intro ii ih) ii


theorem projectEntries_length (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (ZeroEntry input physical source target lengths)) :
    (projectEntries input physical source target lengths entries).value.length ≤ entries.length := by
  rw[projectEntries_value]
  exact List.length_filterMap_le _ _

end BuyAtBulk.Computation.Runtime.StoredRounding
