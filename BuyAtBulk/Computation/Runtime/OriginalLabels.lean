import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.StoredOriginal.Input

/-! Closed canonical integer labels for reduction vertices and a finite traced
resource-table scan. No equality or cost callback is accepted by this code. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def edgePair (edge : Sym2 (Fin n)) : Fin n × Fin n :=
  Quot.lift (fun pair : Fin n × Fin n => (min pair.1 pair.2, max pair.1 pair.2))
    (by intro a b related; cases related <;> simp [min_comm, max_comm]) edge

theorem edgePair_reconstruct (edge : Sym2 (Fin n)) :
    s((edgePair edge).1, (edgePair edge).2) = edge := by
  induction edge using Sym2.ind with
  | h u v =>
    by_cases order : u ≤ v
    · simp [edgePair, min_eq_left order, max_eq_right order]
    · have reverse : v ≤ u := le_of_not_ge order
      simp [edgePair, min_eq_right reverse, max_eq_left reverse, Sym2.eq_swap]

theorem edgePair_injective : Function.Injective (edgePair (n := n)) := by
  intro a b equal
  rw [← edgePair_reconstruct a, ← edgePair_reconstruct b, equal]

/-- Fixed tag and two actual index words. Unordered pair labels are canonical
(minimum, maximum), so the encoding is independent of quotient representatives. -/
def label (vertex : Vertex tables.graphData) : ℕ × ℕ × ℕ :=
  match vertex with
  | .original v => (0, v.val, 0)
  | .edge e => (1, (edgePair e).1.val, (edgePair e).2.val)
  | .leaf i side => (2, i.val, if side then 1 else 0)

theorem label_injective : Function.Injective (label tables) := by
  intro a b equal
  cases a <;> cases b <;> simp only [label, Prod.mk.injEq] at equal
  all_goals try { have tags := equal.1; omega }
  · rcases equal with ⟨_, equal, _⟩
    exact congrArg Vertex.original (Fin.ext equal)
  · rcases equal with ⟨_, first, second⟩
    apply congrArg Vertex.edge
    apply edgePair_injective
    exact Prod.ext (Fin.ext first) (Fin.ext second)
  · rename_i i side j other
    rcases equal with ⟨_, first, second⟩
    have same_i : i = j := Fin.ext first
    cases same_i
    cases side <;> cases other <;> simp_all

/-- The encoder charges tag dispatch, reading the label words, and allocation.
For unordered pairs it also charges both min/max comparisons. -/
def encode (vertex : Vertex tables.graphData) : Traced (ℕ × ℕ × ℕ) :=
  let code := label tables vertex
  let words := [code.1.size, code.2.1.size, code.2.2.size]
  let base := [⟨Operation.branch, [2]⟩,
    ⟨Operation.read, [code.1.size]⟩, ⟨Operation.read, [code.2.1.size]⟩, ⟨Operation.read, [code.2.2.size]⟩,
    ⟨Operation.write, [code.1.size]⟩, ⟨Operation.write, [code.2.1.size]⟩, ⟨Operation.write, [code.2.2.size]⟩]
  match vertex with
  | .edge _ => ⟨code, base ++ [⟨.natCompare, [code.2.1.size, code.2.2.size]⟩,
      ⟨.natCompare, [code.2.1.size, code.2.2.size]⟩]⟩
  | .leaf _ _ => ⟨code, base ++ [⟨.branch, [1]⟩]⟩
  | .original _ => ⟨code, base⟩

@[simp] theorem encode_value (vertex : Vertex tables.graphData) :
    (encode tables vertex).value = label tables vertex := by cases vertex <;> rfl

theorem encode_count (vertex : Vertex tables.graphData) : (encode tables vertex).events.length ≤ 9 := by
  cases vertex <;> simp [encode]

def natEqual (a b : ℕ) : Traced Bool := emit .natCompare [a.size, b.size] (decide (a = b))

def vertexEqual (u v : Vertex tables.graphData) : Traced Bool :=
  let first := encode tables u
  let second := encode tables v
  let a := natEqual first.value.1 second.value.1
  let b := natEqual first.value.2.1 second.value.2.1
  let c := natEqual first.value.2.2 second.value.2.2
  ⟨a.value && b.value && c.value,
    first.events ++ second.events ++ a.events ++ b.events ++ c.events ++
      [⟨.branch, [1, 1, 1]⟩, ⟨.branch, [1, 1]⟩]⟩

@[simp] theorem vertexEqual_value (u v : Vertex tables.graphData) :
    (vertexEqual tables u v).value = decide (u = v) := by
  simp only [vertexEqual, encode_value, natEqual, emit_value]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨tag, first⟩, second⟩
    apply label_injective tables
    exact Prod.ext tag (Prod.ext first second)
  · intro same; subst v; simp

theorem vertexEqual_count (u v : Vertex tables.graphData) :
    (vertexEqual tables u v).events.length ≤ 23 := by
  have first := encode_count tables u
  have second := encode_count tables v
  simp only [vertexEqual, List.length_append, natEqual, emit_length, List.length_cons, List.length_nil]
  omega

private theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

theorem label_bounds (vertex : Vertex tables.graphData) :
    (label tables vertex).1 ≤ 2 ∧ (label tables vertex).2.1 < n + requests + 1 ∧
      (label tables vertex).2.2 < n + requests + 1 := by
  cases vertex with
  | original v => simp only [label]; have := v.isLt; omega
  | edge e =>
    have first := (edgePair e).1.isLt
    have second := (edgePair e).2.isLt
    simp only [label]; omega
  | leaf i side =>
    have bound : i.val < requests := i.isLt
    cases side <;> simp [label] <;> omega

theorem label_widths (vertex : Vertex tables.graphData) (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    (label tables vertex).1.size ≤ K ∧ (label tables vertex).2.1.size ≤ K ∧
      (label tables vertex).2.2.size ≤ K := by
  obtain ⟨tag, first, second⟩ := label_bounds tables vertex
  exact ⟨(size_le_self _).trans (by omega), (size_le_self _).trans (by omega),
    (size_le_self _).trans (by omega)⟩

theorem encode_words (vertex : Vertex tables.graphData) (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    WordsWithin K (encode tables vertex).events := by
  have widths := label_widths tables vertex K dimension
  have one : 1 ≤ K := by omega
  have two : 2 ≤ K := by omega
  cases vertex <;>
    simp_all [encode, WordsWithin, List.mem_cons, List.mem_append]

theorem vertexEqual_words (u v : Vertex tables.graphData) (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    WordsWithin K (vertexEqual tables u v).events := by
  have first := encode_words tables u K dimension
  have second := encode_words tables v K dimension
  have wu := label_widths tables u K dimension
  have wv := label_widths tables v K dimension
  have one : 1 ≤ K := by omega
  simp_all [vertexEqual, natEqual, emit, wordsWithin_append, wordsWithin_cons]

def resourceLookup (vertex : Vertex tables.graphData) : List (Fin resources) → Traced (Option (Fin resources))
  | [] => ⟨none, [⟨.branch, [1]⟩]⟩
  | a :: rest =>
    let equal := vertexEqual tables (resourceVertex tables.graphData a) vertex
    let control :=  [⟨Operation.scan, [a.val.size]⟩, ⟨Operation.read, [a.val.size]⟩] ++ equal.events ++ [⟨.branch, [1]⟩]
    if equal.value then ⟨some a, control ++ [⟨.write, [a.val.size]⟩]⟩
    else
      let next := resourceLookup vertex rest
      ⟨next.value, control ++ next.events⟩

theorem resourceLookup_value (vertex : Vertex tables.graphData) (indices : List (Fin resources)) :
    (resourceLookup tables vertex indices).value =
      indices.find? (fun a => decide (resourceVertex tables.graphData a = vertex)) := by
  induction indices with
  | nil => rfl
  | cons a rest ih =>
    simp only [resourceLookup, vertexEqual_value, List.find?_cons]
    split <;> simp_all

theorem resourceLookup_count (vertex : Vertex tables.graphData) (indices : List (Fin resources)) :
    (resourceLookup tables vertex indices).events.length ≤ 27 * indices.length + 1 := by
  induction indices with
  | nil => simp [resourceLookup]
  | cons a rest ih =>
    have compared := vertexEqual_count tables (resourceVertex tables.graphData a) vertex
    simp only [resourceLookup, List.length_append, List.length_cons, List.length_nil]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

theorem resourceLookup_words (vertex : Vertex tables.graphData) (indices : List (Fin resources))
    (K : ℕ) (dimension : n + requests + resources + 3 ≤ K) :
    WordsWithin K (resourceLookup tables vertex indices).events := by
  induction indices with
  | nil => simp [resourceLookup, WordsWithin]; omega
  | cons a rest ih =>
    have compared := vertexEqual_words tables (resourceVertex tables.graphData a) vertex K (by omega)
    have index : a.val.size ≤ K := (size_le_self _).trans (by have := a.isLt; omega)
    have one : 1 ≤ K := by omega
    by_cases same : (vertexEqual tables (resourceVertex tables.graphData a) vertex).value = true
    · simp_all [resourceLookup, wordsWithin_append, wordsWithin_cons]
    · simp_all [resourceLookup, wordsWithin_append, wordsWithin_cons]

end BuyAtBulk.Computation.Runtime.Original
