import BuyAtBulk.Computation.Runtime.OriginalLabels

/-! Explicit stored original-input payload size: Boolean adjacency cells,
record tags, endpoint/resource labels and normalized rational word encodings. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.Computation.StoredOriginal Rational
open scoped BigOperators
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def locationBits : Fin n ⊕ Sym2 (Fin n)→ℕ
  | .inl v=>v.val.size+1
  | .inr edge=>(edgePair edge).1.val.size+(edgePair edge).2.val.size+1

def inputSize : ℕ :=
  n*n+5*resources+3*requests+1+
    (∑ i : Fin requests,(tables.source[i.val].val.size+tables.target[i.val].val.size))+
    (∑ a : Fin resources,locationBits tables.location[a.val])+
    (∑ a : Fin resources,((Code.ofRat tables.buying[a.val]).bits+(Code.ofRat tables.length[a.val]).bits))+
    (∑ i : Fin requests,(Code.ofRat tables.demand[i.val]).bits)

theorem inputSize_pos : 0 < inputSize tables := by dsimp only [inputSize];omega

theorem inputSize_square : n*n ≤ inputSize tables := by dsimp only [inputSize];omega

theorem inputSize_vertices : n ≤ inputSize tables := by
  have bound := inputSize_square tables
  cases n with
  | zero=>omega
  | succ n=>nlinarith

theorem inputSize_resources : resources ≤ inputSize tables := by dsimp only [inputSize];omega

theorem inputSize_requests : requests ≤ inputSize tables := by dsimp only [inputSize];omega

theorem inputSize_buying (a : Fin resources) : (Code.ofRat tables.buying[a.val]).bits ≤ inputSize tables := by
  have sum := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun b : Fin resources=>(Code.ofRat tables.buying[b.val]).bits+(Code.ofRat tables.length[b.val]).bits)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)
  dsimp only [inputSize]
  omega

theorem inputSize_length (a : Fin resources) : (Code.ofRat tables.length[a.val]).bits ≤ inputSize tables := by
  have sum := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun b : Fin resources=>(Code.ofRat tables.buying[b.val]).bits+(Code.ofRat tables.length[b.val]).bits)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)
  dsimp only [inputSize]
  omega

theorem inputSize_demand (i : Fin requests) : (Code.ofRat tables.demand[i.val]).bits ≤ inputSize tables := by
  have sum := Finset.single_le_sum (s:=Finset.univ) (f:=fun j : Fin requests=>(Code.ofRat tables.demand[j.val]).bits)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  dsimp only [inputSize]
  omega

end BuyAtBulk.Computation.Runtime.Original
