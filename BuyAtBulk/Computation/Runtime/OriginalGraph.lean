import BuyAtBulk.Computation.Runtime.OriginalEnumeration
import BuyAtBulk.Computation.ShortestPath.Encoding

/-! Closed adjacency decoding for the actual subdivision graph. Original
adjacency and endpoint lookups are stored array reads, not graph callbacks. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def originalEdge (u : Fin n) (edge : Sym2 (Fin n)) : Traced Bool :=
  let encoded := encode tables (Vertex.edge edge)
  let a : Fin n := ⟨encoded.value.2.1, by simpa only [encoded, encode_value, label] using (edgePair edge).1.isLt⟩
  let b : Fin n := ⟨encoded.value.2.2, by simpa only [encoded, encode_value, label] using (edgePair edge).2.isLt⟩
  let first := natEqual u.val a.val
  let second := natEqual u.val b.val
  let adjacent := tables.adjacency[a.val][b.val]
  ⟨adjacent && (first.value || second.value),
    encoded.events ++ [⟨.read, [u.val.size]⟩, ⟨.read, [a.val.size, b.val.size, 1]⟩] ++
      first.events ++ second.events ++ [⟨.branch, [1, 1]⟩, ⟨.branch, [1, 1]⟩]⟩

theorem originalEdge_value (u : Fin n) (edge : Sym2 (Fin n)) :
    (originalEdge tables u edge).value =
      decide ((graph tables.graphData).Adj (.original u) (.edge edge)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [originalEdge, natEqual, emit_value, encode_value, label, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_iff]
  conv_rhs => rw [← edgePair_reconstruct edge]
  simp [graph, SimpleGraph.mem_edgeSet, matrixGraph, Tables.graphData, Sym2.mem_iff, Fin.ext_iff]

theorem originalEdge_count (u : Fin n) (edge : Sym2 (Fin n)) :
    (originalEdge tables u edge).events.length ≤ 15 := by
  have encoded := encode_count tables (Vertex.edge edge)
  simp only [originalEdge, List.length_append, List.length_cons, List.length_nil, natEqual, emit_length]
  omega

def endpointRead (i : Fin requests) (side : Bool) : Traced (Fin n) :=
  if side then ⟨tables.target[i.val], [⟨.branch, [1]⟩, ⟨.read, [i.val.size, tables.target[i.val].val.size]⟩]⟩
  else ⟨tables.source[i.val], [⟨.branch, [1]⟩, ⟨.read, [i.val.size, tables.source[i.val].val.size]⟩]⟩

@[simp] theorem endpointRead_value (i : Fin requests) (side : Bool) :
    (endpointRead tables i side).value = endpoint tables.graphData i side := by
  cases side <;> rfl

theorem endpointRead_count (i : Fin requests) (side : Bool) : (endpointRead tables i side).events.length = 2 := by
  cases side <;> rfl

def originalLeaf (u : Fin n) (i : Fin requests) (side : Bool) : Traced Bool :=
  let endpoint := endpointRead tables i side
  let equal := natEqual u.val endpoint.value.val
  ⟨equal.value, [⟨.read, [u.val.size]⟩] ++ endpoint.events ++ equal.events⟩

theorem originalLeaf_value (u : Fin n) (i : Fin requests) (side : Bool) :
    (originalLeaf tables u i side).value =
      decide ((graph tables.graphData).Adj (.original u) (.leaf i side)) := by
  simp [originalLeaf, natEqual, graph, Fin.ext_iff]

theorem originalLeaf_count (u : Fin n) (i : Fin requests) (side : Bool) :
    (originalLeaf tables u i side).events.length = 4 := by
  simp [originalLeaf, endpointRead_count, natEqual]

def adjacent (u v : Vertex tables.graphData) : Traced Bool :=
  let result := match u, v with
    | .original u, .edge edge => originalEdge tables u edge
    | .edge edge, .original u => originalEdge tables u edge
    | .original u, .leaf i side => originalLeaf tables u i side
    | .leaf i side, .original u => originalLeaf tables u i side
    | _, _ => emit .write [1] false
  ⟨result.value,
    [⟨Operation.read, [(label tables u).1.size]⟩, ⟨.branch, [(label tables u).1.size]⟩,
      ⟨.read, [(label tables v).1.size]⟩, ⟨.branch, [(label tables v).1.size]⟩] ++ result.events⟩

@[simp] theorem adjacent_value (u v : Vertex tables.graphData) :
    (adjacent tables u v).value = decide ((graph tables.graphData).Adj u v) := by
  cases u <;> cases v <;>
    first | exact originalEdge_value tables _ _ | exact originalLeaf_value tables _ _ _ | rfl

theorem adjacent_count (u v : Vertex tables.graphData) : (adjacent tables u v).events.length ≤ 19 := by
  have edge := originalEdge_count tables
  have leaf := originalLeaf_count tables
  cases u <;> cases v <;>
    simp only [adjacent, List.length_append, List.length_cons, List.length_nil, emit_length, originalLeaf_count] <;>
    first | omega | (apply Nat.add_le_add_left (edge _ _) 4)

private theorem fin_width {m : ℕ} (i : Fin m) (K : ℕ) (bound : m ≤ K) : i.val.size ≤ K :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt; omega)

theorem originalEdge_words (u : Fin n) (edge : Sym2 (Fin n)) (K : ℕ)
    (dimension : n + requests + 3 ≤ K) : WordsWithin K (originalEdge tables u edge).events := by
  have encoded := encode_words tables (Vertex.edge edge) K dimension
  have first := fin_width (edgePair edge).1 K (by omega)
  have second := fin_width (edgePair edge).2 K (by omega)
  have vertex := fin_width u K (by omega)
  have one : 1 ≤ K := by omega
  simp_all [originalEdge, natEqual, emit, wordsWithin_append, wordsWithin_cons, label]

theorem originalLeaf_words (u : Fin n) (i : Fin requests) (side : Bool) (K : ℕ)
    (dimension : n + requests + 3 ≤ K) : WordsWithin K (originalLeaf tables u i side).events := by
  have vertex := fin_width u K (by omega)
  have index := fin_width i K (by omega)
  have source := fin_width tables.source[i.val] K (by omega)
  have target := fin_width tables.target[i.val] K (by omega)
  have one : 1 ≤ K := by omega
  cases side <;> simp_all [originalLeaf, endpointRead, natEqual, emit, wordsWithin_append, wordsWithin_cons]

theorem adjacent_words (u v : Vertex tables.graphData) (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    WordsWithin K (adjacent tables u v).events := by
  have first := label_widths tables u K dimension
  have second := label_widths tables v K dimension
  have one : 1 ≤ K := by omega
  cases u <;> cases v <;>
    simp only [adjacent, wordsWithin_append, wordsWithin_cons, wordsWithin_nil] <;>
    simp_all [emit, originalEdge_words, originalLeaf_words]

end BuyAtBulk.Computation.Runtime.Original
