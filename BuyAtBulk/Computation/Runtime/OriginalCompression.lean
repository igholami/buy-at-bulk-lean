import BuyAtBulk.Computation.Runtime.OriginalLabels
import BuyAtBulk.Model.NodeReduction.EndpointProjection

/-! Actual structural compression. Only proof-erased impossible cases are
eliminated: every reachable constructor and recursive allocation is charged. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def compressFuel (fuel : ℕ) {u v : Fin n}
    (p : (graph tables.graphData).Walk (.original u) (.original v))
    (hp : p.IsPath) (hlen : p.length ≤ fuel) : Traced (tables.graphData.graph.Walk u v) := by
  classical
  cases fuel with
  | zero =>
    cases p with
    | nil => exact ⟨.nil, [⟨.natCompare, [0, 0]⟩, ⟨.branch, [1]⟩, ⟨.path, [u.val.size]⟩]⟩
    | cons hadj tail => simp at hlen
  | succ fuel =>
    cases p with
    | nil => exact ⟨.nil, [⟨.natCompare, [(fuel + 1).size, 0]⟩, ⟨.branch, [1]⟩, ⟨.path, [u.val.size]⟩]⟩
    | @cons _ next _ hadj tail =>
      cases next with
      | original w => simp [graph] at hadj
      | leaf i side =>
        cases tail with
        | @cons _ next _ hleaf rest =>
          have hnext : next = Vertex.original (endpoint tables.graphData i side) :=
            (leaf_neighbor_iff tables.graphData i side next).mp hleaf
          have hu : u = endpoint tables.graphData i side := hadj
          have heq : next = Vertex.original u := hnext.trans (congrArg Vertex.original hu.symm)
          cases heq
          have hs := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hs
          exact (hs.1 (by simp)).elim
      | edge e =>
        cases tail with
        | @cons _ next _ hnext rest =>
          cases next with
          | edge f => simp [graph] at hnext
          | leaf i side => simp [graph] at hnext
          | original w =>
            have hu : e ∈ tables.graphData.graph.edgeSet ∧ u ∈ e := hadj
            have hw : e ∈ tables.graphData.graph.edgeSet ∧ w ∈ e := hnext
            have hs := hp.support_nodup
            simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hs
            have hne : u ≠ w := by intro heq; subst w; exact hs.1 (by simp)
            have heqedge : e = s(u, w) := (Sym2.mem_and_mem_iff hne).mp ⟨hu.2, hw.2⟩
            have hold : tables.graphData.graph.Adj u w := by simpa [heqedge] using hu.1
            have hrest : rest.length ≤ fuel := by simp only [SimpleGraph.Walk.length_cons] at hlen; omega
            let result := compressFuel fuel rest hp.of_cons.of_cons hrest
            exact ⟨.cons hold result.value,
              [⟨Operation.natCompare, [(fuel + 1).size, 0]⟩, ⟨.branch, [1]⟩, ⟨.branch, [2]⟩,
                ⟨.branch, [1]⟩, ⟨.branch, [1]⟩, ⟨.read, [u.val.size]⟩,
                ⟨.read, [w.val.size]⟩, ⟨.recurse, [(fuel + 1).size, fuel.size]⟩] ++ result.events ++ [⟨.cons, [u.val.size]⟩]⟩
termination_by fuel

private theorem leaf_impossible {u v : Fin n} (i : Fin requests) (side : Bool)
    (hadj : (graph tables.graphData).Adj (.original u) (.leaf i side))
    {next : Vertex tables.graphData} (hleaf : (graph tables.graphData).Adj (.leaf i side) next)
    (rest : (graph tables.graphData).Walk next (.original v))
    (simple : (SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hleaf rest)).IsPath) : False := by
  have next_eq : next = Vertex.original u :=
    ((leaf_neighbor_iff tables.graphData i side next).mp hleaf).trans
      (congrArg Vertex.original (show u = endpoint tables.graphData i side from hadj).symm)
  cases next_eq
  have no_repeat := simple.support_nodup
  simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at no_repeat
  exact no_repeat.1 (by simp)

theorem compressFuel_value (fuel : ℕ) {u v : Fin n}
    (p : (graph tables.graphData).Walk (.original u) (.original v))
    (hp : p.IsPath) (hlen : p.length ≤ fuel) :
    (compressFuel tables fuel p hp hlen).value =
      (BuyAtBulk.NodeReduction.compressPathFuel tables.graphData fuel p hp hlen).val := by
  induction fuel generalizing u v with
  | zero =>
    cases p with
    | nil => simp [compressFuel, BuyAtBulk.NodeReduction.compressPathFuel]
    | cons edge tail => simp at hlen
  | succ fuel ih =>
    cases p with
    | nil => simp [compressFuel, BuyAtBulk.NodeReduction.compressPathFuel]
    | @cons _ next _ edge tail =>
      cases next with
      | original w => simp [graph] at edge
      | leaf i side =>
        cases tail with
        | @cons _ next _ hleaf rest => exact False.elim (leaf_impossible tables i side edge hleaf rest hp)
      | edge e =>
        cases tail with
        | @cons _ next _ hnext rest =>
          cases next with
          | edge f => simp [graph] at hnext
          | leaf i side => simp [graph] at hnext
          | original w =>
            have hrest : rest.length ≤ fuel := by simp only [SimpleGraph.Walk.length_cons] at hlen; omega
            rw [compressFuel, BuyAtBulk.NodeReduction.compressPathFuel]
            dsimp only
            change SimpleGraph.Walk.cons _ (compressFuel tables fuel rest hp.of_cons.of_cons hrest).value =
              SimpleGraph.Walk.cons _ (BuyAtBulk.NodeReduction.compressPathFuel tables.graphData fuel rest hp.of_cons.of_cons hrest).val
            rw [ih rest hp.of_cons.of_cons hrest]

theorem compressFuel_count (fuel : ℕ) {u v : Fin n}
    (p : (graph tables.graphData).Walk (.original u) (.original v))
    (hp : p.IsPath) (hlen : p.length ≤ fuel) :
    (compressFuel tables fuel p hp hlen).events.length ≤ 9 * p.length + 3 := by
  induction fuel generalizing u v with
  | zero =>
    cases p with
    | nil => simp [compressFuel]
    | cons edge tail => simp at hlen
  | succ fuel ih =>
    cases p with
    | nil => simp [compressFuel]
    | @cons _ next _ edge tail =>
      cases next with
      | original w => simp [graph] at edge
      | leaf i side =>
        cases tail with
        | @cons _ next _ hleaf rest => exact False.elim (leaf_impossible tables i side edge hleaf rest hp)
      | edge e =>
        cases tail with
        | @cons _ next _ hnext rest =>
          cases next with
          | edge f => simp [graph] at hnext
          | leaf i side => simp [graph] at hnext
          | original w =>
            have hrest : rest.length ≤ fuel := by simp only [SimpleGraph.Walk.length_cons] at hlen; omega
            have bound := ih rest hp.of_cons.of_cons hrest
            rw [compressFuel]
            dsimp only
            simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons]
            omega

private theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

theorem compressFuel_words (fuel : ℕ) {u v : Fin n}
    (p : (graph tables.graphData).Walk (.original u) (.original v))
    (hp : p.IsPath) (hlen : p.length ≤ fuel) (K : ℕ)
    (dimension : n + requests + fuel + 3 ≤ K) :
    WordsWithin K (compressFuel tables fuel p hp hlen).events := by
  induction fuel generalizing u v with
  | zero =>
    cases p with
    | nil =>
      have index : u.val.size ≤ K := (size_le_self _).trans (by have := u.isLt; omega)
      have unit : 1 ≤ K := by omega
      simp [compressFuel, WordsWithin, List.mem_cons, index, unit]
    | cons edge tail => simp at hlen
  | succ fuel ih =>
    have input : (fuel + 1).size ≤ K := (size_le_self _).trans (by omega)
    have tailfuel : fuel.size ≤ K := (size_le_self _).trans (by omega)
    have one : 1 ≤ K := by omega
    have two : 2 ≤ K := by omega
    cases p with
    | nil =>
      have index : u.val.size ≤ K := (size_le_self _).trans (by have := u.isLt; omega)
      simp [compressFuel, WordsWithin, List.mem_cons, index, input, one]
    | @cons _ next _ edge tail =>
      cases next with
      | original w => simp [graph] at edge
      | leaf i side =>
        cases tail with
        | @cons _ next _ hleaf rest => exact False.elim (leaf_impossible tables i side edge hleaf rest hp)
      | edge e =>
        cases tail with
        | @cons _ next _ hnext rest =>
          cases next with
          | edge f => simp [graph] at hnext
          | leaf i side => simp [graph] at hnext
          | original w =>
            have hrest : rest.length ≤ fuel := by simp only [SimpleGraph.Walk.length_cons] at hlen; omega
            have inner := ih rest hp.of_cons.of_cons hrest (by omega)
            have first : u.val.size ≤ K := (size_le_self _).trans (by have := u.isLt; omega)
            have second : w.val.size ≤ K := (size_le_self _).trans (by have := w.isLt; omega)
            rw [compressFuel]
            dsimp only
            simp_all only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
              List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              and_true, true_and, Nat.zero_le]

end BuyAtBulk.Computation.Runtime.Original
