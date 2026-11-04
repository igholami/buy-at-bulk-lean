import BuyAtBulk.Computation.Runtime.OriginalSizedEndpoints

/-! A closed original-input decoder whose actual stored count drives every
reduced dense loop. No enumeration is recovered from an erased type index. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
open Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)

structure CachedBuffers where
  count : ℕ
  vertices : List (Vertex tables.graphData)
  size : count=vertices.length
  complete : vertices=modelVertices tables
  graphInput : ShortestPath.GraphEncoding count
  buying : Vector ℚ count
  physical : Vector ℚ count
  demand : Vector ℚ requests
  source : Vector (Fin count) requests
  target : Vector (Fin count) requests

def cachedBuffers : Traced (CachedBuffers tables) :=
  let vertices := enumeration tables
  let count := listLength vertices.value
  let size := listLength_value vertices.value
  let complete := enumeration_value tables
  let graphInput := sizedGraph tables vertices.value count.value size
  let buying := sizedPrices tables vertices.value count.value size tables.buying 0
  let physical := sizedPrices tables vertices.value count.value size tables.length 0
  let demand := Weights.materialize (readRat tables.demand) (fun q=>(Code.ofRat q).bits)
  let source := sizedEndpoints tables vertices.value complete count.value size false
  let target := sizedEndpoints tables vertices.value complete count.value size true
  ⟨⟨count.value,vertices.value,size,complete,graphInput.value,buying.value,physical.value,demand.value,source.value,target.value⟩,
    vertices.events++count.events++graphInput.events++buying.events++physical.events++demand.events++source.events++target.events++
      [⟨.cons,[count.value.size,n.size,resources.size,requests.size]⟩]⟩

@[simp] theorem cachedBuffers_count_value : (cachedBuffers tables).value.count=reducedCount tables := by
  simp only [cachedBuffers,listLength_value,enumeration_value]
@[simp] theorem cachedBuffers_vertices : (cachedBuffers tables).value.vertices=modelVertices tables := enumeration_value tables

/-- The source graph is isomorphic to the actual cached Boolean graph. -/
def cachedIso : (graph tables.graphData) ≃g (cachedBuffers tables).value.graphInput.graph :=
  sizedIso tables (enumeration tables).value (enumeration_value tables)
    (listLength (enumeration tables).value).value (listLength_value _)

theorem cachedBuffers_buying (v : Fin (cachedBuffers tables).value.count) :
    (cachedBuffers tables).value.buying[v.val]=OriginalPipeline.resourceCost tables.graphData tables.graphData.buying
      ((cachedIso tables).symm v) :=
  sizedPrices_cost tables _ (enumeration_value tables) _ (listLength_value _) tables.buying v

theorem cachedBuffers_physical (v : Fin (cachedBuffers tables).value.count) :
    (cachedBuffers tables).value.physical[v.val]=OriginalPipeline.resourceCost tables.graphData tables.graphData.length
      ((cachedIso tables).symm v) :=
  sizedPrices_cost tables _ (enumeration_value tables) _ (listLength_value _) tables.length v

theorem cachedBuffers_source (i : Fin requests) :
    (cachedBuffers tables).value.source[i.val]=cachedIso tables (.leaf i false) :=
  sizedEndpoints_value tables _ (enumeration_value tables) _ (listLength_value _) false i

theorem cachedBuffers_target (i : Fin requests) :
    (cachedBuffers tables).value.target[i.val]=cachedIso tables (.leaf i true) :=
  sizedEndpoints_value tables _ (enumeration_value tables) _ (listLength_value _) true i

theorem cachedBuffers_demand (i : Fin requests) : (cachedBuffers tables).value.demand[i.val]=tables.demand[i.val] := by
  change (Weights.materialize (readRat tables.demand) (fun q=>(Code.ofRat q).bits)).value[i.val]=_
  rw [Weights.materialize_get]
  rfl

def cachedCount (n r h m : ℕ) :=
  50*(n+n*n+2*h+1)^2+(2*m+1)+(50*(m+1)*m^2+5*m)+
    2*(m*(50*(m+r+1)+2)+1)+(3*h+1)+2*(h*(27*m+5)+1)+1

theorem cachedBuffers_count : (cachedBuffers tables).events.length ≤ cachedCount n resources requests (reducedCount tables) := by
  have vertices := enumeration_count tables
  have length := listLength_count (enumeration tables).value
  have graphInput := sizedGraph_count tables (enumeration tables).value _ (listLength_value _)
  have buying := sizedPrices_count tables (enumeration tables).value _ (listLength_value _) tables.buying 0
  have physical := sizedPrices_count tables (enumeration tables).value _ (listLength_value _) tables.length 0
  have demand := Weights.materialize_count (readRat tables.demand) (fun q=>(Code.ofRat q).bits) 1 (by intro i;rfl)
  have source := sizedEndpoints_count tables (enumeration tables).value (enumeration_value tables) _ (listLength_value _) false
  have target := sizedEndpoints_count tables (enumeration tables).value (enumeration_value tables) _ (listLength_value _) true
  let m := (listLength (enumeration tables).value).value
  have mvalue : m=reducedCount tables := by simp only [m,listLength_value,enumeration_value]
  have lengthValue := listLength_value (enumeration tables).value
  have combined : (cachedBuffers tables).events.length ≤ cachedCount n resources requests m := by
    dsimp only [cachedBuffers,cachedCount,m]
    simp only [List.length_append,List.length_cons,List.length_nil]
    nlinarith
  exact combined.trans_eq (congrArg (cachedCount n resources requests) mvalue)

theorem cachedBuffers_words (K : ℕ) (dimension : n+resources+requests+reducedCount tables+5 ≤ K)
    (buyingBits : ∀ a : Fin resources,(Code.ofRat tables.buying[a.val]).bits ≤ K)
    (lengthBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ K)
    (demandBits : ∀ i : Fin requests,(Code.ofRat tables.demand[i.val]).bits ≤ K) :
    WordsWithin K (cachedBuffers tables).events := by
  dsimp only [reducedCount,modelVertices] at dimension
  have vertices := enumeration_words tables K (by omega)
  have length := listLength_words (enumeration tables).value K (by simpa only [enumeration_value] using (show reducedCount tables+2 ≤ K by dsimp only [reducedCount,modelVertices];omega))
  have zero : (Code.ofRat (0:ℚ)).bits ≤ K := by norm_num [Code.bits,Code.ofRat];omega
  have graphInput := sizedGraph_words tables (enumeration tables).value _ (listLength_value _) K (by
    simp only [listLength_value,enumeration_value];omega)
  have buying := sizedPrices_words tables (enumeration tables).value _ (listLength_value _) tables.buying 0 K (by
    simp only [listLength_value,enumeration_value];omega) buyingBits zero
  have physical := sizedPrices_words tables (enumeration tables).value _ (listLength_value _) tables.length 0 K (by
    simp only [listLength_value,enumeration_value];omega) lengthBits zero
  have source := sizedEndpoints_words tables (enumeration tables).value (enumeration_value tables) _ (listLength_value _) false K (by
    simp only [listLength_value,enumeration_value];omega)
  have target := sizedEndpoints_words tables (enumeration tables).value (enumeration_value tables) _ (listLength_value _) true K (by
    simp only [listLength_value,enumeration_value];omega)
  have demand : WordsWithin K (Weights.materialize (readRat tables.demand) (fun q=>(Code.ofRat q).bits)).events := by
    apply Weights.materialize_words
    · omega
    · intro i
      have ii : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
      simp only [readRat,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true]
      exact ⟨ii,demandBits i⟩
    · intro i
      simpa only [readRat,emit_value] using demandBits i
  have size (a : ℕ) (bound : a ≤ K) : a.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans bound
  have actualSize : (listLength (enumeration tables).value).value.size ≤ K := by
    simp only [listLength_value,enumeration_value]
    exact size _ (by omega)
  simp only [cachedBuffers,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨vertices,length⟩,graphInput⟩,buying⟩,physical⟩,demand⟩,source⟩,target⟩,
    actualSize,size n (by omega),size resources (by omega),size requests (by omega)⟩

theorem cachedBuffers_dimension : (cachedBuffers tables).value.count ≤ n+n*n+2*requests := by
  rw [cachedBuffers_count_value]
  exact BuyAtBulk.Computation.NodeReduction.numbering_size tables.graphData (Equiv.refl _)

theorem cachedBuffers_count_polynomial : (cachedBuffers tables).events.length ≤
    cachedCount n resources requests (n+n*n+2*requests) := by
  apply (cachedBuffers_count tables).trans
  have bound : reducedCount tables ≤ n+n*n+2*requests :=
    BuyAtBulk.Computation.NodeReduction.numbering_size tables.graphData (Equiv.refl _)
  dsimp only [cachedCount]
  gcongr

def cachedWordBudget (n r h L : ℕ) := n+r+h+(n+n*n+2*h)+L+10

theorem cachedBuffers_words_polynomial (L : ℕ)
    (buyingBits : ∀ a : Fin resources,(Code.ofRat tables.buying[a.val]).bits ≤ L)
    (lengthBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (demandBits : ∀ i : Fin requests,(Code.ofRat tables.demand[i.val]).bits ≤ L) :
    WordsWithin (cachedWordBudget n resources requests L) (cachedBuffers tables).events := by
  have bound : reducedCount tables ≤ n+n*n+2*requests :=
    BuyAtBulk.Computation.NodeReduction.numbering_size tables.graphData (Equiv.refl _)
  apply cachedBuffers_words
  · dsimp only [cachedWordBudget];omega
  · intro a;exact (buyingBits a).trans (by dsimp[cachedWordBudget];omega)
  · intro a;exact (lengthBits a).trans (by dsimp[cachedWordBudget];omega)
  · intro i;exact (demandBits i).trans (by dsimp[cachedWordBudget];omega)

end BuyAtBulk.Computation.Runtime.Original
