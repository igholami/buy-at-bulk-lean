import BuyAtBulk.Computation.Runtime.OriginalLabels

/-! Materialized resource values use a verified first-match optimization.
Injectivity of resource locations proves equivalence to the LP's finite sums;
no large unreduced arithmetic expression is evaluated by this implementation. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
open Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def resourceValue (values : Vector ℚ resources) (defaultValue : ℚ)
    (vertex : Vertex tables.graphData) : Traced ℚ :=
  let indices := indexList resources
  let found := resourceLookup tables vertex indices.value
  let control := indices.events ++ found.events ++ [⟨Operation.branch, [1]⟩]
  match found.value with
  | none => ⟨defaultValue, control ++ [⟨.write, [(Code.ofRat defaultValue).bits]⟩]⟩
  | some a =>
    let price := readRat values a
    ⟨price.value, control ++ price.events⟩

theorem resourceLookup_some (vertex : Vertex tables.graphData) (a : Fin resources)
    (returned : (resourceLookup tables vertex (List.finRange resources)).value = some a) :
    resourceVertex tables.graphData a = vertex := by
  rw [resourceLookup_value] at returned
  have property := List.find?_some returned
  exact of_decide_eq_true property

theorem resourceLookup_none (vertex : Vertex tables.graphData)
    (returned : (resourceLookup tables vertex (List.finRange resources)).value = none) :
    ∀ a : Fin resources, resourceVertex tables.graphData a ≠ vertex := by
  rw [resourceLookup_value] at returned
  intro a same
  exact (List.find?_eq_none.mp returned a (List.mem_finRange a)) (by simpa only [same, decide_true])

theorem resourceCost_value (values : Vector ℚ resources) (vertex : Vertex tables.graphData) :
    (resourceValue tables values 0 vertex).value =
      OriginalPipeline.resourceCost tables.graphData (fun a => values[a.val]) vertex := by
  unfold resourceValue
  simp only [indexList_value]
  cases found : (resourceLookup tables vertex (List.finRange resources)).value with
  | none =>
    have free := resourceLookup_none tables vertex found
    simp [found, OriginalPipeline.resourceCost, free]
  | some a =>
    have paid := resourceLookup_some tables vertex a found
    simp only [found, readRat, emit_value]
    symm
    unfold OriginalPipeline.resourceCost
    calc
      (∑ b, if resourceVertex tables.graphData b = vertex then values[b.val] else 0) =
          if resourceVertex tables.graphData a = vertex then values[a.val] else 0 := by
        apply Finset.sum_eq_single a
        · intro b _ different
          have free : resourceVertex tables.graphData b ≠ vertex := by
            intro same
            exact different (resourceVertex_injective tables.graphData (same.trans paid.symm))
          simp [free]
        · intro absent; exact False.elim (absent (Finset.mem_univ a))
      _ = values[a.val] := by simp [paid]

theorem resourceOpening_value (values : Vector ℚ resources) (vertex : Vertex tables.graphData) :
    (resourceValue tables values 1 vertex).value =
      OriginalPipeline.resourceOpening tables.graphData (fun a => values[a.val]) vertex := by
  unfold resourceValue
  simp only [indexList_value]
  cases found : (resourceLookup tables vertex (List.finRange resources)).value with
  | none =>
    have free := resourceLookup_none tables vertex found
    simp only [found]
    exact (OriginalPipeline.resourceOpening_free tables.graphData _ vertex free).symm
  | some a =>
    have paid := resourceLookup_some tables vertex a found
    simp only [found, readRat, emit_value]
    rw [← paid, OriginalPipeline.resourceOpening_resource]

theorem resourceValue_count (values : Vector ℚ resources) (defaultValue : ℚ)
    (vertex : Vertex tables.graphData) :
    (resourceValue tables values defaultValue vertex).events.length ≤ 30 * resources + 3 := by
  have lookup := resourceLookup_count tables vertex (List.finRange resources)
  simp only [List.length_finRange] at lookup
  unfold resourceValue
  simp only [indexList_value]
  cases found : (resourceLookup tables vertex (List.finRange resources)).value <;>
    simp only [found, List.length_append, List.length_cons, List.length_nil, readRat, emit_length]
  all_goals have indices := indexList_count resources; omega

theorem resourceValue_words (values : Vector ℚ resources) (defaultValue : ℚ)
    (vertex : Vertex tables.graphData) (K : ℕ)
    (dimension : n + requests + resources + 3 ≤ K)
    (inputs : ∀ a : Fin resources, (Code.ofRat values[a.val]).bits ≤ K)
    (fallback : (Code.ofRat defaultValue).bits ≤ K) :
    WordsWithin K (resourceValue tables values defaultValue vertex).events := by
  have indices := indexList_words resources K (by omega)
  have lookup := resourceLookup_words tables vertex (List.finRange resources) K dimension
  have one : 1 ≤ K := by omega
  unfold resourceValue
  simp only [indexList_value]
  cases found : (resourceLookup tables vertex (List.finRange resources)).value with
  | none => simp_all [wordsWithin_append, wordsWithin_cons]
  | some a =>
    have index : a.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := a.isLt; omega)
    have price := inputs a
    simp_all [readRat, emit, wordsWithin_append, wordsWithin_cons]

end BuyAtBulk.Computation.Runtime.Original
