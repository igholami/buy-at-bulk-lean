import BuyAtBulk.Computation.Runtime.SuppliedPaths

/-! Exact supplied-list length metadata, with bounds in the actual list size
and the binary widths of its weights and original resource prices. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Supplied
open Rational BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal Original
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources h : ℕ} (tables : Tables n resources h)

abbrev InputEntry := Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target

def terms (i : Fin h) : List (InputEntry tables) → Traced (List ℚ)
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | entry::rest =>
    let length := pathCost tables entry.1 entry.2.2
    let product := ratMul entry.2.1 length.value
    let same := natEqual entry.1.val i.val
    let value := if same.value then product.value else 0
    let tail := terms i rest
    ⟨value::tail.value,
      [⟨.branch,[1]⟩,⟨.scan,[1]⟩,⟨.read,[(Code.ofRat entry.2.1).bits]⟩]++
      length.events++product.events++same.events++[⟨.branch,[1]⟩]++tail.events++[⟨.cons,[(Code.ofRat value).bits]⟩]⟩

 theorem terms_value (i : Fin h) (entries : List (InputEntry tables)) :
    (terms tables i entries).value = entries.map (fun e => if e.1=i then e.2.1*OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length e.1 e.2.2 else 0) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [terms,pathCost_value,ratMul_value,natEqual,emit_value,decide_eq_true_eq,List.map_cons,ih]
    simp only [Fin.ext_iff]

 def commodity (i : Fin h) (entries : List (InputEntry tables)) : Traced ℚ :=
  let values := terms tables i entries
  let result := ratSum values.value
  ⟨result.value,values.events++result.events⟩

 theorem commodity_value (i : Fin h) (fractional : Fractional tables) :
    (commodity tables i fractional.entries).value = OriginalPipeline.fractionalLength tables.graphData fractional.decode i := by
  simp only [commodity,ratSum_value,terms_value,OriginalPipeline.fractionalLength,Fractional.decode]
  generalize fractional.entries = entries
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨j,weight,path⟩
    simp only [selectPaths,List.filterMap_cons,List.map_cons,List.sum_cons]
    by_cases same : j=i
    · subst j
      simp only [dif_pos rfl,ite_true,List.map_cons,List.sum_cons]
      exact congrArg (fun q=>weight*OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length i path+q) ih
    · simp only [dif_neg same,if_neg same,zero_add]
      exact ih

 def termCount (n resources : ℕ) := resources*(50*(n+1)+11)+11
 def termBudget (resources L : ℕ) := 2*(L+pathOutputBudget resources L)+8
 def metadataWords (n resources h k L : ℕ) := pathWordBudget n resources h L+n+h+L+termBudget resources L+
   (8*k+6)*(termBudget resources L+6)+20
 def metadataBits (resources k L : ℕ) := 2*(2*k+1)*(termBudget resources L+6)+2

 theorem terms_count (i : Fin h) (entries : List (InputEntry tables)) :
    (terms tables i entries).events.length ≤ termCount n resources*entries.length+1 := by
  induction entries with
  | nil => simp [terms]
  | cons entry rest ih =>
    have cost := pathCost_count tables entry.1 entry.2.2
    simp only [terms,List.length_append,List.length_cons,List.length_nil,ratMul_length,natEqual,emit_length]
    dsimp only [termCount] at *
    nlinarith

 theorem commodity_count (i : Fin h) (entries : List (InputEntry tables)) :
    (commodity tables i entries).events.length ≤ (termCount n resources+6)*entries.length+3 := by
  have bound := terms_count tables i entries
  simp only [commodity,List.length_append,ratSum_count,terms_value,List.length_map]
  nlinarith

 theorem terms_bits (i : Fin h) (entries : List (InputEntry tables)) (L : ℕ) (constant : 5 ≤ L)
    (priceBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    ∀ q∈(terms tables i entries).value,(Code.ofRat q).bits ≤ termBudget resources L := by
  intro q mem
  rw [terms_value] at mem
  obtain ⟨e,member,rfl⟩ := List.mem_map.mp mem
  split
  · have weight := weightBits e member
    have length := pathCost_bits tables e.1 e.2.2 L constant priceBits
    have result := ratMul_result_bits e.2.1 (pathCost tables e.1 e.2.2).value
    rw [pathCost_value] at result length
    dsimp only [Tables.graphData] at result length ⊢
    dsimp [termBudget]
    omega
  · have zero : (Code.ofRat 0).bits=3 := by decide
    rw [zero];dsimp[termBudget];omega

 theorem terms_words (i : Fin h) (entries : List (InputEntry tables)) (L K : ℕ) (constant : 5 ≤ L)
    (priceBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L)
    (budget : pathWordBudget n resources h L+n+h+L+termBudget resources L+5 ≤ K) :
    WordsWithin K (terms tables i entries).events := by
  have one : 1 ≤ K := by omega
  induction entries with
  | nil => simp[terms,WordsWithin,one]
  | cons e rest ih =>
    have weight := weightBits e (by simp)
    have length := pathCost_bits tables e.1 e.2.2 L constant priceBits
    have cost := (pathCost_words tables e.1 e.2.2 L constant priceBits).mono (by omega : pathWordBudget n resources h L ≤ K)
    have product : WordsWithin K (ratMul e.2.1 (pathCost tables e.1 e.2.2).value).events := by
      intro event mem word present
      exact (ratMul_words _ _ event mem word present).trans (by dsimp[termBudget] at budget;omega)
    have productBits := ratMul_result_bits e.2.1 (pathCost tables e.1 e.2.2).value
    have ii : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
    have ei : e.1.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have : e.1.val < h := e.1.isLt;omega)
    have valueBits : (Code.ofRat (if (natEqual e.1.val i.val).value then (ratMul e.2.1 (pathCost tables e.1 e.2.2).value).value else 0)).bits ≤ K := by
      split
      · simp only [ratMul_value];dsimp[termBudget] at budget;omega
      · have zero : (Code.ofRat 0).bits=3 := by decide
        rw[zero];omega
    have tail := ih (fun e mem=>weightBits e (by simp[mem]))
    simp only [terms,wordsWithin_append,wordsWithin_cons,wordsWithin_nil]
    simp only [List.mem_singleton,forall_eq,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,and_true]
    exact ⟨⟨⟨⟨⟨⟨⟨one,one,by omega⟩,cost⟩,product⟩,by simp[natEqual,emit,WordsWithin,ei,ii]⟩,one⟩,tail⟩,valueBits⟩

 theorem commodity_words (i : Fin h) (entries : List (InputEntry tables)) (L : ℕ) (constant : 5 ≤ L)
    (priceBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    WordsWithin (metadataWords n resources h entries.length L) (commodity tables i entries).events := by
  let K := metadataWords n resources h entries.length L
  have values := terms_words tables i entries L K constant priceBits weightBits (by dsimp[K,metadataWords];omega)
  have bits := terms_bits tables i entries L constant priceBits weightBits
  have sum := (ratSum_general_words (terms tables i entries).value (termBudget resources L+6)
    (by omega) (by intro q mem;have := bits q mem;omega)).mono
    (show _ ≤ K by simp only [terms_value,List.length_map];dsimp[K,metadataWords];omega)
  exact (wordsWithin_append _ _ _).mpr ⟨values,sum⟩

 theorem commodity_bits (i : Fin h) (entries : List (InputEntry tables)) (L : ℕ) (constant : 5 ≤ L)
    (priceBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    (Code.ofRat (commodity tables i entries).value).bits ≤ metadataBits resources entries.length L := by
  have bits := terms_bits tables i entries L constant priceBits weightBits
  have sum := HelperExpressions.sum_rat_bits (terms tables i entries).value (termBudget resources L+6)
    (by omega) (by intro q mem;have := bits q mem;omega)
  simpa only [commodity,ratSum_value,terms_value,List.length_map,metadataBits] using sum

 def metadata (entries : List (InputEntry tables)) : Traced (Vector ℚ h) :=
   Weights.materialize (fun i=>commodity tables i entries) (fun q=>(Code.ofRat q).bits)

 theorem metadata_value (fractional : Fractional tables) (i : Fin h) :
    (metadata tables fractional.entries).value[i.val]=OriginalPipeline.fractionalLength tables.graphData fractional.decode i := by
   rw [metadata,Weights.materialize_get,commodity_value]

 theorem metadata_count (entries : List (InputEntry tables)) :
    (metadata tables entries).events.length ≤ h*((termCount n resources+6)*entries.length+5)+1 :=
   Weights.materialize_count _ _ _ (fun i=>commodity_count tables i entries)

 theorem metadata_words (entries : List (InputEntry tables)) (L : ℕ) (constant : 5 ≤ L)
    (priceBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    WordsWithin (metadataWords n resources h entries.length L+metadataBits resources entries.length L+h)
      (metadata tables entries).events := by
   apply Weights.materialize_words
   · omega
   · intro i;exact (commodity_words tables i entries L constant priceBits weightBits).mono (by omega)
   · intro i;exact (commodity_bits tables i entries L constant priceBits weightBits).trans (by omega)

end BuyAtBulk.Computation.Runtime.Supplied
