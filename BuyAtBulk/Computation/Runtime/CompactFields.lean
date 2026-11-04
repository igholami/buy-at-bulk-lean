import BuyAtBulk.Computation.Runtime.CompactMetadataWords
import BuyAtBulk.Computation.Runtime.ArrayDot

/-! The compact optimizer's actual vector is converted once into the stored
opening, buying budget and per-request allowance consumed by the rounder. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.CompactLift
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ}

structure Fields (n h : ℕ) where
  opening : Vector ℚ n
  budget : ℚ
  allowance : Vector ℚ h

def prepare (input : ShortestPath.GraphEncoding n) (buying physical : Vector ℚ n)
    (source target : Vector (Fin n) h) (point : Vector ℚ (variableCount n h)) :
    Traced (Option (Fields n h)) :=
  let opening := CompactDecode.opening point
  let budget := ArrayDot.run buying opening.value
  let allowance := lengths input physical source target point
  match allowance.value with
  | none=>⟨none,opening.events++budget.events++allowance.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | some values=>⟨some ⟨opening.value,budget.value,values⟩,
    opening.events++budget.events++allowance.events++[⟨.branch,[1]⟩,⟨.cons,[n.size,h.size,(Code.ofRat budget.value).bits]⟩,⟨.write,[1]⟩]⟩

theorem opening_eq (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (CompactDecode.opening point).value=Vector.ofFn f.opening := by
  apply Vector.ext
  intro v bound
  have coord := congrFun coordinates (Sum.inl (⟨v,bound⟩ : Fin n))
  change f.opening ⟨v,bound⟩=point[(variableEquiv n h (.inl ⟨v,bound⟩)).val] at coord
  simpa only [Vector.getElem_ofFn] using (CompactDecode.opening_value point ⟨v,bound⟩).trans coord.symm

theorem budget_eq (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (ArrayDot.run (Vector.ofFn f.buying) (CompactDecode.opening point).value).value=f.buyingBudget := by
  rw [opening_eq input f point coordinates,ArrayDot.run_value]
  simp only [Vector.getElem_ofFn,Fin.eta,CompactFlow.Solution.buyingBudget]

theorem prepare_value (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (prepare input (Vector.ofFn f.buying) (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).value=
      some ⟨Vector.ofFn f.opening,f.buyingBudget,Vector.ofFn (FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f)⟩ := by
  simp only [prepare,lengths_value input f point coordinates]
  rw [budget_eq input f point coordinates,opening_eq input f point coordinates]

def prepareCount (n h : ℕ) := lengthsCount n h+13*n+4

theorem prepare_count (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (prepare input (Vector.ofFn f.buying) (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).events.length ≤ prepareCount n h := by
  have opening := CompactDecode.opening_count point
  have budget := ArrayDot.run_count (Vector.ofFn f.buying) (CompactDecode.opening point).value
  have allowance := lengths_count input f point coordinates
  simp only [prepare,lengths_value input f point coordinates,List.length_append,List.length_cons,List.length_nil]
  dsimp only [prepareCount]
  omega

def budgetBits (n L : ℕ) := 2*(4*n+1)*L+2

def prepareWords (n h L : ℕ) := CompactDecode.indexWordBudget n h L+ArrayDot.wordBudget n L+
  lengthsWords n h L+budgetBits n L+n+h+20

theorem prepare_words (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val]))
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (buyingBits : ∀ v : Fin n,(Code.ofRat (f.buying v)).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat (f.physical v)).bits+1 ≤ L) :
    WordsWithin (prepareWords n h L)
      (prepare input (Vector.ofFn f.buying) (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).events := by
  let K := prepareWords n h L
  have opening := (CompactDecode.opening_words point L (by intro j;have bound:=pointBits j;omega)).mono
    (show _ ≤ K by dsimp[K,prepareWords];omega)
  have buying : ∀ v : Fin n,(Code.ofRat (Vector.ofFn f.buying)[v.val]).bits+1 ≤ L := by
    simpa only [Vector.getElem_ofFn] using buyingBits
  have obits : ∀ v : Fin n,(Code.ofRat (CompactDecode.opening point).value[v.val]).bits+1 ≤ L := by
    intro v
    rw [CompactDecode.opening_value]
    exact pointBits _
  have budget := (ArrayDot.run_words (Vector.ofFn f.buying) (CompactDecode.opening point).value L constant buying obits).mono
    (show _ ≤ K by dsimp[K,prepareWords];omega)
  have budgetBits := ArrayDot.run_bits (Vector.ofFn f.buying) (CompactDecode.opening point).value L constant buying obits
  have storedBudget : (Code.ofRat (ArrayDot.run (Vector.ofFn f.buying) (CompactDecode.opening point).value).value).bits ≤ K :=
    budgetBits.trans (by dsimp[K,prepareWords,CompactLift.budgetBits];omega)
  have allowance := (lengths_words input f point coordinates L constant pointBits physicalBits).mono
    (show _ ≤ K by dsimp[K,prepareWords];omega)
  have one : 1 ≤ K := by dsimp[K,prepareWords];omega
  have ni : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,prepareWords];omega)
  have hi : h.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,prepareWords];omega)
  unfold prepare
  dsimp only
  rw [lengths_value input f point coordinates]
  simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  aesop

theorem prepare_field_bits (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val]))
    (fields : Fields n h)
    (returned : (prepare input (Vector.ofFn f.buying) (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).value=some fields)
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (buyingBits : ∀ v : Fin n,(Code.ofRat (f.buying v)).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat (f.physical v)).bits+1 ≤ L) :
    (∀ v : Fin n,(Code.ofRat fields.opening[v.val]).bits+1 ≤ L) ∧
      (Code.ofRat fields.budget).bits ≤ budgetBits n L ∧
      ∀ i : Fin h,(Code.ofRat fields.allowance[i.val]).bits ≤ allowanceBits n L := by
  rw [prepare_value input f point coordinates] at returned
  have fieldsEq := Option.some.inj returned
  rw [←fieldsEq]
  constructor
  · intro v
    simp only [Vector.getElem_ofFn,Fin.eta]
    have coord := congrFun coordinates (Sum.inl v)
    change f.opening v=point[(variableEquiv n h (.inl v)).val] at coord
    rw [coord]
    exact pointBits _
  constructor
  · have buying : ∀ v : Fin n,(Code.ofRat (Vector.ofFn f.buying)[v.val]).bits+1 ≤ L := by
      simpa only [Vector.getElem_ofFn] using buyingBits
    have obits : ∀ v : Fin n,(Code.ofRat (CompactDecode.opening point).value[v.val]).bits+1 ≤ L := by
      intro v;rw [CompactDecode.opening_value];exact pointBits _
    have bound := ArrayDot.run_bits (Vector.ofFn f.buying) (CompactDecode.opening point).value L constant buying obits
    rw [budget_eq input f point coordinates] at bound
    exact bound
  · intro i
    simpa only [Vector.getElem_ofFn,Fin.eta] using fractionalLength_bits input f point coordinates i L constant pointBits physicalBits

end BuyAtBulk.Computation.Runtime.CompactLift
