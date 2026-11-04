import BuyAtBulk.Model.CompactFlow
import Mathlib.Data.List.Nodup

/-! Integer directed-arc traversals and their exact vertex balance identities. -/
noncomputable section
namespace BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V}
local instance compactFlowPathDecEq : DecidableEq V := Classical.decEq _

/-- Directed transport-arc traversal multiplicity in a graph walk. -/
def transportVisits {s t : V} : G.Walk s t → V → V → ℚ
  | .nil, _, _ => 0
  | @SimpleGraph.Walk.cons _ _ u v _ _ p, a, b =>
      (if u = a ∧ v = b then 1 else 0) + transportVisits p a b

/-- Split-arc traversal multiplicity, including both endpoint node arcs. -/
def nodeVisits {s t : V} (p : G.Walk s t) (v : V) : ℚ := p.support.count v

omit [Fintype V] in
theorem transportVisits_nonneg {s t : V} (p : G.Walk s t) (a b : V) :
    0 ≤ transportVisits p a b := by
  induction p with
  | nil => exact le_rfl
  | cons hadj p ih => exact add_nonneg (by split_ifs <;> norm_num) ih

omit [Fintype V] in
theorem transportVisits_nonedge {s t : V} (p : G.Walk s t) (a b : V)
    (hab : ¬G.Adj a b) : transportVisits p a b = 0 := by
  induction p with
  | nil => rfl
  | @cons u v t hadj p ih =>
    have hn : ¬(u = a ∧ v = b) := by rintro ⟨rfl, rfl⟩; exact hab hadj
    simp [transportVisits, hn, ih]

theorem visits_outgoing {s t : V} (p : G.Walk s t) (v : V) :
    nodeVisits p v = (∑ u, transportVisits p v u) + (if t = v then 1 else 0) := by
  induction p with
  | nil => simp [nodeVisits, transportVisits, List.count_singleton]
  | @cons s u t hadj p ih =>
    simp only [nodeVisits, SimpleGraph.Walk.support_cons, List.count_cons, Nat.cast_add,
      transportVisits, Finset.sum_add_distrib] at *
    have hv : (∑ x : V, if s = v ∧ u = x then (1 : ℚ) else 0) =
        if s = v then 1 else 0 := by by_cases h : s = v <;> simp [h]
    rw [hv]
    rw [ih]
    by_cases h : s = v <;> simp only [beq_iff_eq, h, ite_true, ite_false, Nat.cast_one, Nat.cast_zero] <;> ring

theorem visits_incoming {s t : V} (p : G.Walk s t) (v : V) :
    nodeVisits p v = (∑ u, transportVisits p u v) + (if s = v then 1 else 0) := by
  induction p with
  | nil => simp [nodeVisits, transportVisits, List.count_singleton]
  | @cons s u t hadj p ih =>
    simp only [nodeVisits, SimpleGraph.Walk.support_cons, List.count_cons, Nat.cast_add,
      transportVisits, Finset.sum_add_distrib] at *
    have hv : (∑ x : V, if s = x ∧ u = v then (1 : ℚ) else 0) =
        if u = v then 1 else 0 := by by_cases h : u = v <;> simp [h]
    rw [hv, ih]
    by_cases hs : s = v <;> by_cases hu : u = v <;> simp only [beq_iff_eq, hs, hu, ite_true, ite_false, Nat.cast_one, Nat.cast_zero] <;> ring

omit [Fintype V] in
theorem nodeVisits_path {s t : V} (p : G.Path s t) (v : V) :
    nodeVisits p.val v = if v ∈ p.val.support then 1 else 0 := by
  classical
  by_cases hv : v ∈ p.val.support
  · simp [nodeVisits, hv]
  · simp [nodeVisits, hv, List.count_eq_zero.mpr hv]

end BuyAtBulk.CompactFlow
