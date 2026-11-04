import Mathlib.Data.Fintype.Sum
import BuyAtBulk.LowerBound.IntegralOptimum
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.DeriveFintype

/-! The actual undirected graph from `lower_bound.tex`. -/
namespace BuyAtBulk.LowerBound

/-- Each request is indexed by one `k`-subset. -/
abbrev Request (k : ℕ) := {A : Finset (Ground k) // A.card = k}

inductive Vertex (k : ℕ) where
  | root
  | paid (j : Ground k)
  | terminal (A : Request k)
  deriving DecidableEq, Fintype

/-- The root is joined to every paid node, and terminal `A` to its members. -/
def graph (k : ℕ) : SimpleGraph (Vertex k) where
  Adj u v := match u, v with
    | .root, .paid _ => True
    | .paid _, .root => True
    | .paid j, .terminal A => j ∈ A.val
    | .terminal A, .paid j => j ∈ A.val
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

/-- All requests can be connected using only paid nodes in `C`.
Root and terminal buying prices, and all physical lengths, are zero. -/
def NetworkFeasible (k : ℕ) (C : Finset (Ground k)) : Prop :=
  ∀ A : Request k, ∃ p : (graph k).Walk .root (.terminal A),
    ∀ j, Vertex.paid j ∈ p.support → j ∈ C

/-- Every root-to-terminal walk visits a paid neighbor belonging to that
terminal's subset, including walks through other terminals. -/
theorem walk_hits (k : ℕ) (A : Request k)
    (p : (graph k).Walk .root (.terminal A)) :
    ∃ j ∈ A.val, Vertex.paid j ∈ p.support := by
  have hrev : ∃ j ∈ A.val, Vertex.paid j ∈ p.reverse.support := by
    generalize heq : p.reverse = q
    cases q with
    | cons hstep tail =>
      rename_i v
      cases v with
      | root => simp [graph] at hstep
      | terminal B => simp [graph] at hstep
      | paid j => exact ⟨j, hstep, by simp⟩
  simpa [SimpleGraph.Walk.support_reverse] using hrev

/-- Network connectivity forces the cover condition, including routes which
pass through other terminals. Conversely a cover gives two-edge routes. -/
theorem networkFeasible_iff (k : ℕ) (C : Finset (Ground k)) :
    NetworkFeasible k C ↔ HitsAll k C := by
  classical
  constructor
  · intro h A hA
    obtain ⟨p, hp⟩ := h ⟨A, hA⟩
    obtain ⟨j, hjA, hjp⟩ := walk_hits k ⟨A, hA⟩ p
    refine ⟨j, hjA, hp j ?_⟩
    exact hjp
  · intro h A
    obtain ⟨j, hjA, hjC⟩ := h A.val A.property
    have hroot : (graph k).Adj .root (.paid j) := trivial
    have hterminal : (graph k).Adj (.paid j) (.terminal A) := hjA
    refine ⟨.cons hroot (.cons hterminal .nil), ?_⟩
    intro i hi
    have hij : i = j := by simpa using hi
    simpa [hij] using hjC


/-- The graph construction has integral node buying optimum exactly `k+1`. -/
theorem network_integral_optimum (k : ℕ) (hk : 1 ≤ k) :
    (∀ C : Finset (Ground k), NetworkFeasible k C → k + 1 ≤ C.card) ∧
    ∃ C : Finset (Ground k), NetworkFeasible k C ∧ C.card = k + 1 := by
  obtain ⟨hlower, C, hC, hcard⟩ := integral_optimum k hk
  exact ⟨fun C h => hlower C ((networkFeasible_iff k C).mp h),
    C, (networkFeasible_iff k C).mpr hC, hcard⟩

end BuyAtBulk.LowerBound
