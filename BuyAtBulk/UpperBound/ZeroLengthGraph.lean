import BuyAtBulk.UpperBound.ZeroLengthSupport
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Restrict transit to zero-physical-length nodes while retaining the full
vertex set and all buying prices/openings. Unused positive-length nodes remain
isolated, so the original buying comparator B can be preserved exactly. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} (G : SimpleGraph V) (physical : V → ℚ)

def zeroGraph : SimpleGraph V where
  Adj u v := G.Adj u v ∧ physical u = 0 ∧ physical v = 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

theorem zeroGraph_le : zeroGraph G physical ≤ G := fun _ _ edge => edge.1

def restrictZeroWalk {s t : V} (walk : G.Walk s t)
    (zero_nodes : ∀ v ∈ walk.support, physical v = 0) : (zeroGraph G physical).Walk s t :=
  match walk with
  | .nil => .nil
  | .cons edge tail => .cons ⟨edge, zero_nodes _ (by simp), zero_nodes _ (by simp)⟩
      (restrictZeroWalk tail (fun v hv => zero_nodes v (by simp [hv])))

@[simp] theorem restrictZeroWalk_support {s t : V} (walk : G.Walk s t)
    (zero_nodes : ∀ v ∈ walk.support, physical v = 0) :
    (restrictZeroWalk G physical walk zero_nodes).support = walk.support := by
  induction walk with
  | nil => rfl
  | @cons u v w edge tail ih =>
    let hz : ∀ a ∈ tail.support, physical a = 0 := fun a ha =>
      zero_nodes a (List.mem_cons_of_mem u ha)
    change u :: (restrictZeroWalk G physical tail hz).support = u :: tail.support
    rw [ih hz]

def restrictZeroPath {s t : V} (path : G.Path s t)
    (zero_nodes : ∀ v ∈ path.val.support, physical v = 0) : (zeroGraph G physical).Path s t :=
  ⟨restrictZeroWalk G physical path.val zero_nodes, .mk' (by simpa using path.property.support_nodup)⟩

@[simp] theorem restrictZeroPath_support {s t : V} (path : G.Path s t)
    (zero_nodes : ∀ v ∈ path.val.support, physical v = 0) :
    (restrictZeroPath G physical path zero_nodes).val.support = path.val.support :=
  restrictZeroWalk_support G physical path.val zero_nodes

def projectZeroPath {s t : V} (path : (zeroGraph G physical).Path s t) : G.Path s t :=
  ⟨path.val.mapLe (zeroGraph_le G physical), .mk' (by
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using path.property.support_nodup)⟩

@[simp] theorem projectZeroPath_support {s t : V} (path : (zeroGraph G physical).Path s t) :
    (projectZeroPath G physical path).val.support = path.val.support :=
  SimpleGraph.Walk.support_mapLe_eq_support _ _

theorem zeroGraph_walk_nodes {s t : V} (walk : (zeroGraph G physical).Walk s t) :
    physical s = 0 → ∀ v ∈ walk.support, physical v = 0 := by
  induction walk with
  | @nil u =>
    intro hs v hv
    have heq : v = u := by simpa using hv
    simpa only [heq] using hs
  | @cons s u t edge tail ih =>
    intro hs v hv
    rcases List.mem_cons.mp hv with rfl | ht
    · exact hs
    · exact ih edge.2.2 v ht

theorem projectZeroPath_physical_zero [Fintype V] {s t : V}
    (path : (zeroGraph G physical).Path s t) (source_zero : physical s = 0) :
    NodeMetric.walkWeight G physical (projectZeroPath G physical path).val = 0 := by
  classical
  unfold NodeMetric.walkWeight
  apply Finset.sum_eq_zero
  intro v hv
  apply zeroGraph_walk_nodes G physical path.val source_zero v
  simpa only [projectZeroPath_support, List.mem_toFinset] using hv

end BuyAtBulk.UpperBound
