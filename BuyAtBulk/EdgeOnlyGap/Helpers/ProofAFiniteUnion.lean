import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAFiniteProbability

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

 theorem probability_union {Ω ι : Type} [Fintype Ω] [DecidableEq ι]
    (S : Finset ι) (E : ι → Ω → Prop) :
    finiteProbability (fun ω => ∃ i ∈ S, E i ω) ≤
      ∑ i ∈ S, finiteProbability (E i) := by
  classical
  have he : (Finset.univ.filter fun ω => ∃ i ∈ S, E i ω) =
      S.biUnion (fun i => Finset.univ.filter (E i)) := by
    ext ω
    simp
  have hc := Finset.card_biUnion_le (s := S) (t := fun i => Finset.univ.filter (E i))
  unfold finiteProbability
  simp only [Fintype.card_subtype]
  rw [he, ← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hc

 theorem probability_exists {Ω ι : Type} [Fintype Ω] [Fintype ι]
    (E : ι → Ω → Prop) :
    finiteProbability (fun ω => ∃ i, E i ω) ≤ ∑ i, finiteProbability (E i) := by
  simpa using probability_union Finset.univ E

/-- Every list of length at most L is represented by its L optional entries. -/
 theorem boundedLists_finite (α : Type) [Finite α] (L : ℕ) :
    Finite {s : List α // s.length ≤ L} := by
  let f : {s : List α // s.length ≤ L} → (Fin L → Option α) := fun s i => s.val[i.val]?
  apply Finite.of_injective f
  intro s t heq
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L
  · exact congrFun heq ⟨i,hi⟩
  · rw [List.getElem?_eq_none (le_trans s.prop (Nat.le_of_not_lt hi)),
        List.getElem?_eq_none (le_trans t.prop (Nat.le_of_not_lt hi))]

end BuyAtBulk.EdgeOnlyGap.ProofA
