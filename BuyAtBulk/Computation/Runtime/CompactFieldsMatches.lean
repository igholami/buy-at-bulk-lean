import BuyAtBulk.Computation.Runtime.CompactFields

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.CompactLift
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

structure FieldsCorrect (f : CompactFlow.Solution input.graph h) (fields : Fields n h) : Prop where
  opening : ∀ v : Fin n,fields.opening[v.val]=f.opening v
  budget : fields.budget=f.buyingBudget
  allowance : ∀ i : Fin h,fields.allowance[i.val]=(FlowDecomposition.toNodeLP input.graph (Equiv.refl _) f).fractionalLength i

theorem arrays_of_matches (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f) :
    data.buying=Vector.ofFn f.buying ∧ data.physical=Vector.ofFn f.physical ∧
      data.source=Vector.ofFn f.source ∧ data.target=Vector.ofFn f.target := by
  constructor
  · apply Vector.ext;intro i bound
    simpa only [Vector.getElem_ofFn] using same.buying ⟨i,bound⟩
  constructor
  · apply Vector.ext;intro i bound
    simpa only [Vector.getElem_ofFn] using same.physical ⟨i,bound⟩
  constructor
  · apply Vector.ext;intro i bound
    simpa only [Vector.getElem_ofFn] using same.source ⟨i,bound⟩
  · apply Vector.ext;intro i bound
    simpa only [Vector.getElem_ofFn] using same.target ⟨i,bound⟩

theorem prepare_correct (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    ∃ fields,(prepare input data.buying data.physical data.source data.target point).value=some fields ∧
      FieldsCorrect input f fields := by
  obtain ⟨buying,physical,source,target⟩ := arrays_of_matches input data f same
  rw [buying,physical,source,target,prepare_value input f point coordinates]
  refine ⟨_,rfl,?_⟩
  constructor
  · intro v;simp only [Vector.getElem_ofFn,Fin.eta]
  · rfl
  · intro i
    simpa only [Vector.getElem_ofFn,Fin.eta] using FlowDecomposition.fractionalLength_eq input.graph (Equiv.refl _) f i

theorem prepare_matches_count (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (prepare input data.buying data.physical data.source data.target point).events.length ≤ prepareCount n h := by
  obtain ⟨buying,physical,source,target⟩ := arrays_of_matches input data f same
  rw [buying,physical,source,target]
  exact prepare_count input f point coordinates

theorem prepare_matches_words (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val]))
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (buyingBits : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits+1 ≤ L) :
    WordsWithin (prepareWords n h L) (prepare input data.buying data.physical data.source data.target point).events := by
  obtain ⟨buying,physical,source,target⟩ := arrays_of_matches input data f same
  rw [buying,physical,source,target]
  apply prepare_words input f point coordinates L constant pointBits
  · intro v;simpa only [same.buying] using buyingBits v
  · intro v;simpa only [same.physical] using physicalBits v

theorem prepare_matches_field_bits (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val]))
    (fields : Fields n h) (returned : (prepare input data.buying data.physical data.source data.target point).value=some fields)
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (buyingBits : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits+1 ≤ L) :
    (∀ v : Fin n,(Code.ofRat fields.opening[v.val]).bits+1 ≤ L) ∧
      (Code.ofRat fields.budget).bits ≤ budgetBits n L ∧
      ∀ i : Fin h,(Code.ofRat fields.allowance[i.val]).bits ≤ allowanceBits n L := by
  obtain ⟨buying,physical,source,target⟩ := arrays_of_matches input data f same
  rw [buying,physical,source,target] at returned
  apply prepare_field_bits input f point coordinates fields returned L constant pointBits
  · intro v;simpa only [same.buying] using buyingBits v
  · intro v;simpa only [same.physical] using physicalBits v

end BuyAtBulk.Computation.Runtime.CompactLift
