import BuyAtBulk.Computation.ShortestPath.RecoveryComplexity

/-! Concrete finite input: graph adjacency is a stored Boolean matrix, and
node weights are a stored rational vector. No adjacency oracle is required. -/
namespace BuyAtBulk.Computation.ShortestPath

structure GraphEncoding (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  symmetric : ∀ u v : Fin n, adjacency[u.val][v.val] = adjacency[v.val][u.val]
  diagonal : ∀ u : Fin n, adjacency[u.val][u.val] = false

namespace GraphEncoding
variable {n : ℕ} (input : GraphEncoding n)

def graph : SimpleGraph (Fin n) where
  Adj u v := input.adjacency[u.val][v.val] = true
  symm := ⟨by intro u v edge; rw [input.symmetric v u]; exact edge⟩
  loopless := ⟨by intro v edge; rw [input.diagonal v] at edge; contradiction⟩

instance graphAdjDecidable : DecidableRel input.graph.Adj := fun u v =>
  inferInstanceAs (Decidable (input.adjacency[u.val][v.val] = true))

def distances (weights : Vector ℚ n) (target : Fin n) : Vector (WithTop ℚ) n :=
  shortestDistances input.graph (fun v => weights[v.val]) target

def path (weights : Vector ℚ n) (source target : Fin n) : Option (input.graph.Path source target) :=
  shortestPath input.graph (fun v => weights[v.val]) source target

/-- A supplied vertex numbering gives an actual Boolean encoding. The
numbering is an input, so no noncomputable finite enumeration is hidden here. -/
def ofGraph {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (numbering : V ≃ Fin n) : GraphEncoding n where
  adjacency := Vector.ofFn fun u => Vector.ofFn fun v => decide (G.Adj (numbering.symm u) (numbering.symm v))
  symmetric := by
    intro u v
    simp only [Vector.getElem_ofFn]
    simp [G.adj_comm]
  diagonal := by
    intro u
    simp

def ofGraphIso {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (numbering : V ≃ Fin n) :
    G ≃g (ofGraph G numbering).graph where
  toEquiv := numbering
  map_rel_iff' := by intro u v; simp [graph, ofGraph]

theorem encoded_shortest_path (weights : Vector ℚ n) (nonneg : ∀ v : Fin n, 0 ≤ weights[v.val])
    (source target : Fin n) (reachable : Nonempty (input.graph.Path source target)) :
    ∃ result : input.graph.Path source target,
      input.path weights source target = some result ∧
      NodeMetric.walkWeight input.graph (fun v => weights[v.val]) result.val =
        NodeMetric.distance input.graph (fun v => weights[v.val]) source target reachable ∧
      (countedIterate input.graph (fun v => weights[v.val]) target n).2 = n ^ 3 ∧
      (recoverScheduled input.graph (fun v => weights[v.val]) target n source).2 ≤ n ^ 4 + n ^ 2 + n := by
  obtain ⟨result, returned, exact_cost⟩ := shortestPath_correct input.graph (fun v => weights[v.val]) nonneg source target reachable
  exact ⟨result, returned, exact_cost, (shortest_relaxation_count input.graph (fun v => weights[v.val]) target).2,
    (shortestPath_scheduled_bound input.graph (fun v => weights[v.val]) source target).2⟩

end GraphEncoding
end BuyAtBulk.Computation.ShortestPath
