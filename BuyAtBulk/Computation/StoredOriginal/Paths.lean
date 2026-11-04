import BuyAtBulk.Computation.FlowDecomposition.Algorithm

/-! Actual indexed typed-path filtering and exact candidate inspections. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
variable {n resources requests : ℕ}

section Select
variable {V : Type} {G : SimpleGraph V} {h : ℕ} (source target : Fin h → V)

abbrev Entry := Σ i : Fin h, ℚ × G.Path (source i) (target i)

def selectPaths (entries : List (Entry (G := G) source target)) (i : Fin h) :
    FlowDecomposition.WeightedPaths G (source i) (target i) :=
  entries.filterMap fun entry => if same : entry.1 = i then some (same ▸ entry.2) else none

theorem selectPaths_nonneg (entries : List (Entry (G := G) source target))
    (nonneg : ∀ entry ∈ entries, 0 ≤ entry.2.1) (i : Fin h) :
    ∀ entry ∈ selectPaths source target entries i, 0 ≤ entry.1 := by
  intro entry member
  obtain ⟨⟨j, weight, path⟩, old_mem, selected⟩ := List.mem_filterMap.mp member
  dsimp only at selected
  split_ifs at selected with same
  · subst j
    simp only [Option.some.injEq] at selected
    subst entry
    exact nonneg _ old_mem

theorem selectPaths_length (entries : List (Entry (G := G) source target)) (i : Fin h) :
    (selectPaths source target entries i).length ≤ entries.length :=
  List.length_filterMap_le _ _

/-- Count the actual entries inspected by a complete request-filter scan. -/
def selectScheduled : List (Entry (G := G) source target) → (i : Fin h) →
    FlowDecomposition.WeightedPaths G (source i) (target i) × ℕ
  | [], _ => ([], 0)
  | entry :: rest, i =>
    let next := selectScheduled rest i
    if same : entry.1 = i then ((same ▸ entry.2) :: next.1, next.2 + 1)
    else (next.1, next.2 + 1)

theorem selectScheduled_value (entries : List (Entry (G := G) source target)) (i : Fin h) :
    (selectScheduled source target entries i).1 = selectPaths source target entries i := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [selectScheduled, selectPaths, List.filterMap_cons]
    split_ifs <;> simp_all [selectPaths]

theorem selectScheduled_visits (entries : List (Entry (G := G) source target)) (i : Fin h) :
    (selectScheduled source target entries i).2 = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [selectScheduled, List.length_cons]
    split_ifs <;> simpa using ih

theorem totalSelected_length (entries : List (Entry (G := G) source target)) :
    (∑ i, (selectPaths source target entries i).length) ≤ h * entries.length := by
  calc
    (∑ i, (selectPaths source target entries i).length) ≤ ∑ _i : Fin h, entries.length :=
      Finset.sum_le_sum fun i _ => selectPaths_length source target entries i
    _ = _ := by simp

end Select


end BuyAtBulk.Computation.StoredOriginal
