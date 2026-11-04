import BuyAtBulk.Computation.Runtime.AttachmentWords
import BuyAtBulk.Computation.Runtime.Logarithm
import BuyAtBulk.Computation.Runtime.SourceCoefficients
import BuyAtBulk.Computation.Serve.GridSearch

/-! Exact integer grid evaluation and stored distance eligibility. Neither
powers nor logarithms are treated as unit-cost oracle operations. -/
namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def gridScale (budget : ℚ) (ratio depth : ℕ) : Traced ℚ := do
  let integer ← power ratio depth
  let denominator ← ratCast integer
  let numerator ← ratMul 2 budget
  ratDiv numerator denominator

@[simp] theorem gridScale_value (budget : ℚ) (ratio depth : ℕ) :
    (gridScale budget ratio depth).value = UpperBound.gridScale budget ratio depth := by
  simp [gridScale, Traced.bind_value, power_value, ratCast, emit_value, ratMul_value,
    ratDiv_value, UpperBound.gridScale, Nat.cast_pow]

theorem gridScale_count (budget : ℚ) (ratio depth : ℕ) :
    (gridScale budget ratio depth).events.length = 2 * depth + 6 := by
  simp [gridScale, Traced.bind_events, Traced.bind_value, List.length_append,
    power_count, ratCast, emit_length]

def eligibleAt (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (depth : ℕ) : Traced Bool :=
  let scale := gridScale budget ratio depth
  let weights := Weights.mixed buying physical state allowance scale.value
  let encoded := ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _)
  let distances := Runtime.ShortestPath.iterate encoded weights.value t n
  let label := Runtime.ShortestPath.read distances.value s
  let compared := emit .ratCompare [Runtime.ShortestPath.width (scale.value : WithTop ℚ), Runtime.ShortestPath.width label.value]
    (decide ((scale.value : WithTop ℚ) ≤ label.value))
  ⟨compared.value, scale.events ++ weights.events ++ Queries.encodingEvents n ++ distances.events ++ label.events ++ compared.events⟩

theorem eligibleAt_value (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (depth : ℕ) :
    (eligibleAt input buying physical state budget allowance ratio s t depth).value =
      Serve.eligibleAt input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode input.graph state) budget allowance ratio s t depth := by
  have weights : (fun v => (Weights.mixed buying physical state allowance (UpperBound.gridScale budget ratio depth)).value[v.val]) =
      Attachment.mixedWeight input.graph (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode input.graph state) allowance (UpperBound.gridScale budget ratio depth) :=
    funext (Weights.mixed_get buying physical state allowance _)
  simp only [eligibleAt, gridScale_value, Runtime.ShortestPath.iterate_value, Runtime.ShortestPath.read, emit_value]
  unfold Serve.eligibleAt ShortestPath.indexedDistances
  simp only [Equiv.refl_apply, Equiv.refl_symm, weights, ShortestPath.shortestDistances]
  rfl

def eligibleBudget (n depth : ℕ) : ℕ :=
  (2 * depth + 6) + (14 * n + 1) + (3 * n * n + n + 1) +
    (n * (n * (10 * n + 4) + 2) + 4 * n + 2) + 2

theorem eligibleAt_count (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (depth : ℕ) :
    (eligibleAt input buying physical state budget allowance ratio s t depth).events.length ≤ eligibleBudget n depth := by
  have weights := Weights.mixed_count buying physical state allowance (gridScale budget ratio depth).value
  have distances := Runtime.ShortestPath.iterate_count (ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _))
    (Weights.mixed buying physical state allowance (gridScale budget ratio depth).value).value t n
  simp only [eligibleAt, List.length_append, gridScale_count, Queries.encodingEvents_count,
    Runtime.ShortestPath.read, emit_length]
  unfold eligibleBudget
  omega

/-- Enumerate increasing indices without allocating an unused list tail.
The result agrees with the minimum selected by the source finite-set scan. -/
def findScale (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) : ℕ → ℕ → Traced (Option ℕ)
  | 0, index => ⟨none, [⟨.recurse, [index.size]⟩]⟩
  | fuel + 1, index =>
      let eligible := eligibleAt input buying physical state budget allowance ratio s t index
      let control := [⟨Operation.recurse, [fuel.size, index.size]⟩] ++ eligible.events ++ [⟨.branch, [1]⟩]
      if eligible.value then ⟨some index, control ++ [⟨.cons, [index.size]⟩]⟩ else
        let next := emit .natAdd [index.size, 1, (index + 1).size] (index + 1)
        let recursive := findScale buying physical state budget allowance ratio s t fuel next.value
        ⟨recursive.value, control ++ next.events ++ recursive.events⟩

def FirstEligible (predicate : ℕ → Bool) (fuel index : ℕ) : Option ℕ → Prop
  | none => ∀ j, index ≤ j → j < index + fuel → predicate j = false
  | some selected => index ≤ selected ∧ selected < index + fuel ∧ predicate selected = true ∧
      ∀ j, index ≤ j → j < selected → predicate j = false

theorem findScale_spec (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (fuel index : ℕ) :
    FirstEligible (fun d => Serve.eligibleAt input.graph (Equiv.refl _)
      (fun v => buying[v.val]) (fun v => physical[v.val]) (StoredState.decode input.graph state)
      budget allowance ratio s t d) fuel index
      (findScale input buying physical state budget allowance ratio s t fuel index).value := by
  let predicate := fun d => Serve.eligibleAt input.graph (Equiv.refl _)
    (fun v => buying[v.val]) (fun v => physical[v.val]) (StoredState.decode input.graph state)
    budget allowance ratio s t d
  change FirstEligible predicate fuel index _
  induction fuel generalizing index with
  | zero => simp [findScale, FirstEligible]; omega
  | succ k ih =>
      have recursive := ih (index + 1)
      simp only [findScale]
      split
      · rename_i accepted
        have high : predicate index = true := by simpa only [predicate, eligibleAt_value] using accepted
        simp only [FirstEligible]
        exact ⟨le_rfl, by omega, high, by intro j lower upper; omega⟩
      · rename_i rejected
        have low : predicate index = false := by
          simp only [eligibleAt_value] at rejected
          cases value : predicate index <;> simp_all [predicate]
        simp only [emit_value]
        cases returned : (findScale input buying physical state budget allowance ratio s t k (index + 1)).value with
        | none =>
            simp only [returned, FirstEligible] at recursive ⊢
            intro j lower upper
            by_cases same : j = index
            · simpa only [same] using low
            · exact recursive j (by omega) (by omega)
        | some selected =>
            simp only [returned, FirstEligible] at recursive ⊢
            obtain ⟨lower, upper, high, earlier⟩ := recursive
            refine ⟨by omega, by omega, high, ?_⟩
            intro j low_index high_index
            by_cases same : j = index
            · simpa only [same] using low
            · exact earlier j (by omega) high_index

def gridDepth (h ratio : ℕ) : Traced ℕ := do
  let twiceRatio ← natMul 2 ratio
  let target ← natMul twiceRatio h
  let doubled ← natMul 2 h
  let fuel ← emit .natAdd [doubled.size, 1, (doubled + 1).size] (doubled + 1)
  ceilingLog ratio target fuel

@[simp] theorem gridDepth_value (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    (gridDepth h ratio).value = UpperBound.gridDepth h ratio := by
  simpa only [gridDepth, Traced.bind_value, natMul, emit_value] using (gridLog_runtime h ratio ratio_ge).1

theorem gridDepth_count (h ratio : ℕ) : (gridDepth h ratio).events.length ≤ 10 * h + 12 := by
  have count := logarithmLoop_count ratio (2 * ratio * h) (2 * h + 1) 0 1
  simp only [gridDepth, Traced.bind_events, Traced.bind_value, natMul, emit_value, emit_length,
    List.length_append]
  change 1 + (1 + (1 + (1 + (ceilingLog ratio (2 * ratio * h) (2 * h + 1)).events.length))) ≤ _
  simp only [ceilingLog]
  omega

def selectScale (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : Fin n) : Traced (Option ℕ) :=
  let depth := gridDepth h ratio
  let fuel := emit .natAdd [depth.value.size, 1, (depth.value + 1).size] (depth.value + 1)
  let selected := findScale input buying physical state budget allowance ratio s t fuel.value 0
  ⟨selected.value, depth.events ++ fuel.events ++ selected.events⟩

theorem selectScale_value (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : Fin n) (ratio_ge : 2 ≤ ratio) :
    (selectScale input buying physical state budget allowance h ratio s t).value =
      Serve.selectScale input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode input.graph state) budget allowance h ratio s t := by
  have selected := findScale_spec input buying physical state budget allowance ratio s t (UpperBound.gridDepth h ratio + 1) 0
  simp only [selectScale, gridDepth_value h ratio ratio_ge, emit_value]
  let candidates := Serve.eligibleGrid input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
    (StoredState.decode input.graph state) budget allowance h ratio s t
  have member (j : ℕ) : j ∈ candidates ↔ j < UpperBound.gridDepth h ratio + 1 ∧
      Serve.eligibleAt input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode input.graph state) budget allowance ratio s t j = true := by
    simp [candidates, Serve.eligibleGrid]
  cases returned : (findScale input buying physical state budget allowance ratio s t
      (UpperBound.gridDepth h ratio + 1) 0).value with
  | none =>
      simp only [returned, FirstEligible, Nat.zero_add] at selected
      have empty : ¬ candidates.Nonempty := by
        rintro ⟨j, present⟩
        obtain ⟨range, high⟩ := (member j).mp present
        have low := selected j (Nat.zero_le _) range
        rw [low] at high
        contradiction
      simpa only [Serve.selectScale, candidates, returned, dite_eq_right empty]
  | some chosen =>
      simp only [returned, FirstEligible, Nat.zero_add] at selected
      obtain ⟨_, range, high, earlier⟩ := selected
      have present := (member chosen).mpr ⟨range, high⟩
      have nonempty : candidates.Nonempty := ⟨chosen, present⟩
      have minimum : candidates.min' nonempty = chosen := by
        apply Nat.le_antisymm (Finset.min'_le _ _ present)
        by_contra small
        have used := Finset.min'_mem candidates nonempty
        obtain ⟨_, high⟩ := (member _).mp used
        have low := earlier (candidates.min' nonempty) (Nat.zero_le _) (by omega)
        rw [low] at high
        contradiction
      simpa only [Serve.selectScale, candidates, returned, dite_eq_left nonempty, minimum]

theorem findScale_count (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (D fuel index : ℕ) (schedule : index + fuel ≤ D + 1) :
    (findScale input buying physical state budget allowance ratio s t fuel index).events.length ≤
      fuel * (eligibleBudget n D + 3) + 1 := by
  induction fuel generalizing index with
  | zero => simp [findScale]
  | succ k ih =>
      have eligible := eligibleAt_count input buying physical state budget allowance ratio s t index
      have cap : eligibleBudget n index ≤ eligibleBudget n D := by unfold eligibleBudget; omega
      have actual := eligible.trans cap
      have recursive := ih (index + 1) (by omega)
      simp only [findScale, emit_value]
      split <;> simp only [List.length_append, List.length_cons, List.length_nil, emit_length,
        Nat.add_mul, Nat.one_mul] <;> omega

theorem selectScale_count (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : Fin n) (ratio_ge : 2 ≤ ratio) :
    (selectScale input buying physical state budget allowance h ratio s t).events.length ≤
      (UpperBound.gridDepth h ratio + 1) * (eligibleBudget n (UpperBound.gridDepth h ratio) + 3) + 10 * h + 14 := by
  have depth := gridDepth_count h ratio
  have selected := findScale_count input buying physical state budget allowance ratio s t
    (UpperBound.gridDepth h ratio) (UpperBound.gridDepth h ratio + 1) 0 (by omega)
  simp only [selectScale, List.length_append, emit_length, emit_value, gridDepth_value h ratio ratio_ge]
  omega

theorem selectScale_some_range (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : Fin n) (d : ℕ) (ratio_ge : 2 ≤ ratio)
    (returned : (selectScale input buying physical state budget allowance h ratio s t).value = some d) :
    d ≤ UpperBound.gridDepth h ratio := by
  have spec := findScale_spec input buying physical state budget allowance ratio s t (UpperBound.gridDepth h ratio + 1) 0
  simp only [selectScale, gridDepth_value h ratio ratio_ge, emit_value] at returned
  rw [returned] at spec
  simp only [FirstEligible, Nat.zero_add] at spec
  omega

def selectionBudget (n h : ℕ) : ℕ :=
  (2 * h + 2) * (eligibleBudget n (2 * h + 1) + 3) + 10 * h + 14

theorem selectScale_count_uniform (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : Fin n) (ratio_ge : 2 ≤ ratio) :
    (selectScale input buying physical state budget allowance h ratio s t).events.length ≤ selectionBudget n h := by
  have actual := selectScale_count input buying physical state budget allowance h ratio s t ratio_ge
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  have eligibility : eligibleBudget n (UpperBound.gridDepth h ratio) ≤ eligibleBudget n (2 * h + 1) := by
    unfold eligibleBudget
    omega
  have product := Nat.mul_le_mul (show UpperBound.gridDepth h ratio + 1 ≤ 2 * h + 2 by omega)
    (Nat.add_le_add_right eligibility 3)
  unfold selectionBudget
  omega

end BuyAtBulk.Computation.Runtime.StoredServe
