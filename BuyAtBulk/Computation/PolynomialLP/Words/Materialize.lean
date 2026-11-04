import BuyAtBulk.Computation.Runtime.Weights

/-! Project actual stored-output word bounds from complete materialization
traces. These lemmas inspect the real cell events rather than assuming an
output-size certificate. -/
namespace BuyAtBulk.Computation.Runtime.Weights
variable {n : ℕ} {α : Type}

theorem materialize_child_words (f : Fin n → Traced α) (width : α → ℕ) (K : ℕ)
    (valid : WordsWithin K (materialize f width).events) (i : Fin n) :
    WordsWithin K (f i).events := by
  intro event member word present
  apply valid event _ word present
  simp only [materialize, List.mem_cons, List.mem_flatMap, Vector.getElem_ofFn]
  right
  refine ⟨i, List.mem_finRange i, ?_⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inl (Or.inr member)

theorem materialize_output_width (f : Fin n → Traced α) (width : α → ℕ) (K : ℕ)
    (valid : WordsWithin K (materialize f width).events) (i : Fin n) :
    width (materialize f width).value[i.val] ≤ K := by
  rw [materialize_get]
  let event : Event := ⟨.write, [i.val.size, width (f i).value]⟩
  have member : event ∈ (materialize f width).events := by
    simp only [materialize, List.mem_cons, List.mem_flatMap, Vector.getElem_ofFn]
    right
    refine ⟨i, List.mem_finRange i, ?_⟩
    simp [event]
  exact valid event member _ (by simp [event])

end BuyAtBulk.Computation.Runtime.Weights
