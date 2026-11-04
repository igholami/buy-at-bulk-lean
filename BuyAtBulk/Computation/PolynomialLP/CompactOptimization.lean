import BuyAtBulk.Computation.PolynomialLP.CompactRefinement

/-! The actual optimizer applied to the source compact flow table. The flow
witness in the correctness theorem establishes nonemptiness and never enters
the program's data. -/
namespace BuyAtBulk.PolynomialLP.CompactEncoding
open CompactFlow
variable {n h : ℕ} {G : SimpleGraph (Fin n)}

def encode (x : Coordinate (Fin n) h) : Fin (variableCount n h) → ℚ :=
  fun j => x ((variableEquiv n h).symm j)

@[simp] theorem decode_encode (x : Coordinate (Fin n) h) : decode (encode x) = x := by
  funext c
  simp [encode,decode]

def solve (data : Data n h) : Option (Vector ℚ (variableCount n h)) := optimize (stored data)

theorem solve_correct (data : Data n h) (f : Solution G h) (same : Matches data f) :
    ∃ point, solve data=some point ∧
      ∃ optimal : Solution G h,
        f.SameData optimal ∧
        optimal.coordinates=decode (fun j => point[j.val]) ∧
        ∀ other : Solution G h, f.SameData other →
          optimal.buyingBudget+optimal.rentalBudget ≤ other.buyingBudget+other.rentalBudget := by
  have feasible : (stored data).problem.Feasible (encode f.coordinates) :=
    (feasible_correct data f same _).mpr (by simpa using f.coordinates_feasible)
  have box : ∀ j, 0≤encode f.coordinates j ∧ encode f.coordinates j≤1 :=
    fun j => f.coordinate_bounds ((variableEquiv n h).symm j)
  obtain ⟨point,computed,valid,bounded,minimal⟩ := optimize_success (stored data)
    ⟨encode f.coordinates,feasible,box⟩
  have source_valid := (feasible_correct data f same _).mp valid
  let optimal := f.ofCoordinates (decode (fun j => point[j.val])) source_valid
  refine ⟨point,computed,optimal,f.ofCoordinates_sameData _ _,?_,?_⟩
  · funext c
    rcases c with v | ⟨i,v⟩ | ⟨i,u,v⟩ <;> rfl
  · intro other sameData
    have other_feasible : f.linearProblem.Feasible other.coordinates := by
      rw [← f.linearProblem_eq_of_sameData other sameData]
      exact other.coordinates_feasible
    have stored_feasible : (stored data).problem.Feasible (encode other.coordinates) :=
      (feasible_correct data f same _).mpr (by simpa using other_feasible)
    have other_box : ∀ j, 0≤encode other.coordinates j ∧ encode other.coordinates j≤1 :=
      fun j => other.coordinate_bounds ((variableEquiv n h).symm j)
    have inequality := minimal (encode other.coordinates) stored_feasible other_box
    rw [objective_value data f same,objective_value data f same,decode_encode] at inequality
    change optimal.buyingBudget+optimal.rentalBudget ≤ _
    rw [f.ofCoordinates_objective]
    convert inequality using 1
    rw [← f.linearProblem_eq_of_sameData other sameData,other.objective_coordinates]

end BuyAtBulk.PolynomialLP.CompactEncoding
