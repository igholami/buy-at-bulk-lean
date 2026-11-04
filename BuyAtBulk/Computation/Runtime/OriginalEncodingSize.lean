import BuyAtBulk.Computation.Runtime.OriginalLabels
import BuyAtBulk.Computation.Runtime.PolynomialBudget

/-! An explicit original-table integer-array encoding and its binary size.
Each signed integer uses a unary magnitude-length prefix, magnitude bits and
a sign bit, for exactly `2*natAbs.size+2` bits. Dimension headers determine
all fixed table lengths. Resource edges use the canonical min/max codec. -/
set_option autoImplicit false
namespace BuyAtBulk.Computation.Runtime.OriginalEncoding
open Rational BuyAtBulk.Computation.StoredOriginal
variable {n resources requests m : ℕ}

def wordBits (z : ℤ) : ℕ := 2*z.natAbs.size+2

def arrayBits (words : List ℤ) : ℕ := (words.map wordBits).sum

@[simp] theorem arrayBits_append (left right : List ℤ) : arrayBits (left++right)=arrayBits left+arrayBits right := by
  simp[arrayBits]

def rationalWords (q : ℚ) : List ℤ := [q.num,(q.den : ℤ)]

def rationalVectorWords (values : Vector ℚ m) : List ℤ :=
  (List.finRange m).flatMap fun i => rationalWords values[i.val]

def rationalVectorBits (values : Vector ℚ m) : ℕ :=
  ((List.finRange m).map fun i => (Code.ofRat values[i.val]).bits).sum

def locationWords : Fin n ⊕ Sym2 (Fin n) → List ℤ
  | .inl v => [0,(v.val : ℤ),0]
  | .inr edge => [1,((Original.edgePair edge).1.val : ℤ),((Original.edgePair edge).2.val : ℤ)]

def adjacencyWords (tables : Tables n resources requests) : List ℤ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => if tables.adjacency[u.val][v.val] then 1 else 0

def endpointWords (tables : Tables n resources requests) : List ℤ :=
  (List.finRange requests).flatMap fun i => [(tables.source[i.val].val : ℤ),(tables.target[i.val].val : ℤ)]

def resourceWords (tables : Tables n resources requests) : List ℤ :=
  (List.finRange resources).flatMap fun a => locationWords tables.location[a.val]

def words (tables : Tables n resources requests) : List ℤ :=
  [(n : ℤ),(resources : ℤ),(requests : ℤ)]++adjacencyWords tables++endpointWords tables++resourceWords tables++
    rationalVectorWords tables.buying++rationalVectorWords tables.length++rationalVectorWords tables.demand

def inputSize (tables : Tables n resources requests) : ℕ := arrayBits (words tables)

@[simp] theorem rationalWords_bits (q : ℚ) : arrayBits (rationalWords q)=2*(Code.ofRat q).bits := by
  simp only[rationalWords,arrayBits,wordBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Code.ofRat,Code.bits,Int.natAbs_natCast]
  omega

theorem rationalVectorWords_bits (values : Vector ℚ m) : arrayBits (rationalVectorWords values)=2*rationalVectorBits values := by
  have scan (indices : List (Fin m)) :
      arrayBits (indices.flatMap fun i => rationalWords values[i.val])=2*(indices.map fun i => (Code.ofRat values[i.val]).bits).sum := by
    induction indices with
    | nil => simp[arrayBits]
    | cons i rest ih =>
      simp only[List.flatMap_cons,arrayBits_append,rationalWords_bits,List.map_cons,List.sum_cons,ih]
      omega
  exact scan _

@[simp] theorem rationalVectorWords_length (values : Vector ℚ m) : (rationalVectorWords values).length=2*m := by
  simp[rationalVectorWords,rationalWords,List.length_flatMap,List.map_const',Nat.mul_comm]

@[simp] theorem locationWords_length (location : Fin n ⊕ Sym2 (Fin n)) : (locationWords location).length=3 := by
  cases location <;>rfl

@[simp] theorem words_length (tables : Tables n resources requests) :
    (words tables).length=3+n*n+7*resources+4*requests := by
  simp[words,adjacencyWords,endpointWords,resourceWords,List.length_flatMap,List.map_const',Nat.mul_comm]
  omega

theorem length_le_arrayBits (values : List ℤ) : values.length≤arrayBits values := by
  induction values with
  | nil => simp[arrayBits]
  | cons z rest ih =>
    simp only[arrayBits,List.map_cons,List.sum_cons,List.length_cons] at *
    have lower : 1≤wordBits z := by unfold wordBits;omega
    omega

theorem dimensions (tables : Tables n resources requests) : n+resources+requests≤ inputSize tables := by
  have lower := length_le_arrayBits (words tables)
  rw[words_length] at lower
  have square := Nat.le_mul_self n
  exact (show n+resources+requests≤3+n*n+7*resources+4*requests by omega).trans lower

theorem logical_cells (tables : Tables n resources requests) : tables.cells≤ inputSize tables := by
  have lower := length_le_arrayBits (words tables)
  rw[words_length] at lower
  unfold Tables.cells inputSize
  omega

private theorem member_le_sum (a : ℕ) (values : List ℕ) (member : a∈values) : a≤values.sum := by
  induction values with
  | nil => simp at member
  | cons b rest ih =>
    simp only[List.mem_cons] at member
    rcases member with rfl|member
    · simp only[List.sum_cons];omega
    · have bound := ih member
      simp only[List.sum_cons]
      omega

theorem rationalVectorBits_member (values : Vector ℚ m) (i : Fin m) :
    (Code.ofRat values[i.val]).bits≤rationalVectorBits values :=
  member_le_sum _ _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

theorem buying_bits (tables : Tables n resources requests) (a : Fin resources) :
    (Code.ofRat tables.buying[a.val]).bits≤ inputSize tables := by
  have leaf := rationalVectorBits_member tables.buying a
  have component : arrayBits (rationalVectorWords tables.buying)≤ inputSize tables := by
    simp only[inputSize,words,arrayBits_append]
    omega
  rw[rationalVectorWords_bits] at component
  omega

theorem length_bits (tables : Tables n resources requests) (a : Fin resources) :
    (Code.ofRat tables.length[a.val]).bits≤ inputSize tables := by
  have leaf := rationalVectorBits_member tables.length a
  have component : arrayBits (rationalVectorWords tables.length)≤ inputSize tables := by
    simp only[inputSize,words,arrayBits_append]
    omega
  rw[rationalVectorWords_bits] at component
  omega

theorem demand_bits (tables : Tables n resources requests) (i : Fin requests) :
    (Code.ofRat tables.demand[i.val]).bits≤ inputSize tables := by
  have leaf := rationalVectorBits_member tables.demand i
  have component : arrayBits (rationalVectorWords tables.demand)≤ inputSize tables := by
    simp only[inputSize,words,arrayBits_append]
    omega
  rw[rationalVectorWords_bits] at component
  omega

def parameterizedWords (tables : Tables n resources requests) (ratio girth : ℕ) : List ℤ :=
  words tables++[(ratio : ℤ),(girth : ℤ)]

def parameterizedSize (tables : Tables n resources requests) (ratio girth : ℕ) : ℕ :=
  arrayBits (parameterizedWords tables ratio girth)

theorem input_le_parameterized (tables : Tables n resources requests) (ratio girth : ℕ) :
    inputSize tables≤parameterizedSize tables ratio girth := by
  simp only[parameterizedSize,parameterizedWords,arrayBits_append,inputSize]
  omega

theorem ratio_bits (tables : Tables n resources requests) (ratio girth : ℕ) : ratio.size≤parameterizedSize tables ratio girth := by
  simp only[parameterizedSize,parameterizedWords,arrayBits_append]
  simp only[arrayBits,wordBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.natAbs_natCast]
  omega

theorem girth_bits (tables : Tables n resources requests) (ratio girth : ℕ) : girth.size≤parameterizedSize tables ratio girth := by
  simp only[parameterizedSize,parameterizedWords,arrayBits_append]
  simp only[arrayBits,wordBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.natAbs_natCast]
  omega

def withRationalsSize (tables : Tables n resources requests) (values : Vector ℚ m) : ℕ :=
  arrayBits (words tables++rationalVectorWords values)

theorem input_le_withRationals (tables : Tables n resources requests) (values : Vector ℚ m) :
    inputSize tables≤withRationalsSize tables values := by simp[withRationalsSize,inputSize]

theorem extra_rational_bits (tables : Tables n resources requests) (values : Vector ℚ m) (i : Fin m) :
    (Code.ofRat values[i.val]).bits≤withRationalsSize tables values := by
  have leaf := rationalVectorBits_member values i
  simp only[withRationalsSize,arrayBits_append,rationalVectorWords_bits]
  omega

end BuyAtBulk.Computation.Runtime.OriginalEncoding
