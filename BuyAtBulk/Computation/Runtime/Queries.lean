import BuyAtBulk.Computation.Runtime.ShortestPathComplete
import BuyAtBulk.Computation.Attachment.Queries

/-! Stored finite-input queries. The original indexed-path implementation
rebuilds the Boolean encoding and maps its returned walk back. Both loops are
charged explicitly here, in addition to the complete shortest-path trace. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Queries
open BuyAtBulk.Computation.ShortestPath
open Rational
variable {n : ℕ}

def encodingEvents (n : ℕ) : List Event :=
  ⟨.write, [n.size]⟩ :: (List.finRange n).flatMap fun u =>
    ⟨.scan, [u.val.size]⟩ :: (List.finRange n).flatMap fun v =>
      [⟨.scan, [v.val.size]⟩, ⟨.read, [u.val.size, v.val.size, 1]⟩,
        ⟨.write, [u.val.size, v.val.size, 1]⟩]

theorem encodingEvents_count : (encodingEvents n).length = 3 * n * n + n + 1 := by
  simp [encodingEvents, List.length_flatMap]
  ring

def mapWalk {G H : SimpleGraph (Fin n)} (hom : G →g H) {u v : Fin n} :
    (walk : G.Walk u v) → Traced (H.Walk (hom u) (hom v))
  | .nil => ⟨.nil, [⟨.branch, [1]⟩, ⟨.read, [u.val.size, (hom u).val.size]⟩]⟩
  | .cons edge tail =>
      let recursive := mapWalk hom tail
      ⟨.cons (hom.map_adj edge) recursive.value,
        [⟨.branch, [1]⟩, ⟨.read, [u.val.size, (hom u).val.size]⟩] ++
          recursive.events ++ [⟨.cons, [(hom u).val.size]⟩]⟩

@[simp] theorem mapWalk_value {G H : SimpleGraph (Fin n)} (hom : G →g H)
    {u v : Fin n} (walk : G.Walk u v) : (mapWalk hom walk).value = walk.map hom := by
  induction walk with
  | nil => rfl
  | cons edge tail ih => simp [mapWalk, ih]

theorem mapWalk_count {G H : SimpleGraph (Fin n)} (hom : G →g H)
    {u v : Fin n} (walk : G.Walk u v) : (mapWalk hom walk).events.length ≤ 3 * (walk.length + 1) := by
  induction walk with
  | nil => simp [mapWalk]
  | cons edge tail ih => simp only [mapWalk, List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons]; omega

/-- Only the fixed identity-on-labels encoding is used here. Thus `mapWalk`
reads/copies labels; it does not call an arbitrary external vertex map. -/
def indexedPath (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n) :
    Traced (Option (input.graph.Path source target)) :=
  let encoded := GraphEncoding.ofGraph input.graph (Equiv.refl _)
  let iso := GraphEncoding.ofGraphIso input.graph (Equiv.refl _)
  let result := Runtime.ShortestPath.path encoded weights source target
  match result.value with
  | none => ⟨none, encodingEvents n ++ result.events ++ [⟨.branch, [1]⟩]⟩
  | some path =>
      let mapped := mapWalk iso.symm.toHom path.val
      let original : input.graph.Path source target :=
        ⟨mapped.value.copy (iso.symm_apply_apply source) (iso.symm_apply_apply target), by
          rw [mapWalk_value]
          exact (copyPath (path.map iso.symm.toHom iso.symm.injective)
            (iso.symm_apply_apply source) (iso.symm_apply_apply target)).property⟩
      ⟨some original, encodingEvents n ++ result.events ++ [⟨.branch, [1]⟩] ++ mapped.events⟩

theorem indexedPath_value (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n) :
    (indexedPath input weights source target).value =
      BuyAtBulk.Computation.ShortestPath.indexedPath input.graph (fun v => weights[v.val])
        (Equiv.refl _) source target := by
  unfold indexedPath BuyAtBulk.Computation.ShortestPath.indexedPath
  have value := Runtime.ShortestPath.path_value (GraphEncoding.ofGraph input.graph (Equiv.refl _)) weights source target
  unfold GraphEncoding.path at value
  simp only [Equiv.refl_apply, Equiv.refl_symm] at *
  rw [← value]
  cases returned : (Runtime.ShortestPath.path (GraphEncoding.ofGraph input.graph (Equiv.refl _)) weights source target).value with
  | none => simp [returned]
  | some path =>
      simp only [returned, Option.map_some, Option.some.injEq]
      apply Subtype.ext
      simp only [mapWalk_value]
      rfl

theorem indexedPath_count (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n) :
    (indexedPath input weights source target).events.length ≤
      (n + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 36) + 3 * n ^ 2 + 4 * n + 6 := by
  have query := Runtime.ShortestPath.path_count (GraphEncoding.ofGraph input.graph (Equiv.refl _)) weights source target
  unfold indexedPath
  cases returned : (Runtime.ShortestPath.path (GraphEncoding.ofGraph input.graph (Equiv.refl _)) weights source target).value with
  | none =>
      simp only [returned, List.length_append, List.length_cons, List.length_nil, encodingEvents_count]
      nlinarith
  | some path =>
      have mapped := mapWalk_count (GraphEncoding.ofGraphIso input.graph (Equiv.refl _)).symm.toHom path.val
      have length : path.val.length < n := by simpa using path.property.length_lt
      simp only [returned, List.length_append, List.length_cons, List.length_nil, encodingEvents_count]
      nlinarith

private theorem index_width (v : Fin n) : v.val.size ≤ n :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt)

theorem encodingEvents_words (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (encodingEvents n) := by
  apply (wordsWithin_cons K _ _).mpr
  constructor
  · simpa only [List.mem_singleton, forall_eq] using (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  · intro event member word present
    obtain ⟨u, _, membership⟩ := List.mem_flatMap.mp member
    have ui := (index_width u).trans indices
    rcases List.mem_cons.mp membership with rfl | inside
    · simp only [List.mem_singleton] at present
      simpa only [present] using ui
    · obtain ⟨v, _, membership⟩ := List.mem_flatMap.mp inside
      have vi := (index_width v).trans indices
      have cell : WordsWithin K [⟨Operation.scan, [v.val.size]⟩,
          ⟨Operation.read, [u.val.size, v.val.size, 1]⟩,
          ⟨Operation.write, [u.val.size, v.val.size, 1]⟩] := by
        simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        exact ⟨vi, ⟨ui, vi, one⟩, ui, vi, one⟩
      exact cell event membership word present

theorem mapWalk_words {G H : SimpleGraph (Fin n)} (hom : G →g H)
    {u v : Fin n} (walk : G.Walk u v) (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (mapWalk hom walk).events := by
  induction walk with
  | nil =>
      simp [mapWalk, WordsWithin, one, (index_width _).trans indices]
  | @cons a b c edge tail ih =>
      have ai := (index_width a).trans indices
      have mapped := (index_width (hom a)).trans indices
      simp only [mapWalk, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop

theorem indexedPath_words (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n)
    (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L) :
    WordsWithin (2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n)
      (indexedPath input weights source target).events := by
  let K := 2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n
  have indices : n ≤ K := by dsimp [K]; omega
  have one : 1 ≤ K := by dsimp [K]; omega
  have encoded := encodingEvents_words K indices one
  have query := Runtime.ShortestPath.path_words (GraphEncoding.ofGraph input.graph (Equiv.refl _)) weights source target L constant inputs
  unfold indexedPath
  cases returned : (Runtime.ShortestPath.path (GraphEncoding.ofGraph input.graph (Equiv.refl _)) weights source target).value with
  | none =>
      simpa only [returned, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton,
        forall_eq, and_true] using And.intro (And.intro encoded query) one
  | some path =>
      have mapped := mapWalk_words (GraphEncoding.ofGraphIso input.graph (Equiv.refl _)).symm.toHom path.val K indices one
      simpa only [returned, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton,
        forall_eq, and_true] using And.intro (And.intro (And.intro encoded query) one) mapped

end BuyAtBulk.Computation.Runtime.Queries
