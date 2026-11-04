import BuyAtBulk.Computation.Rounding.Algorithm
import BuyAtBulk.UpperBound.CoreRun.Initialization

/-! The actual zero-buying-budget branch finds shortest routes using only
zero-buying nodes. The LP supplies existence, never a chosen runtime path. -/
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [vertexDecEq : DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [graphDecAdj : DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem positive_path_free (lp : NodeLP G h) (budget_zero : lp.buyingBudget = 0)
    (i : Fin h) (path : G.Path (lp.source i) (lp.target i)) (positive : 0 < lp.flow i path)
    (v : V) (member : v ∈ path.val.support) : lp.buying v = 0 := by
  have canonical_eq : vertexDecEq = Classical.decEq V := Subsingleton.elim _ _
  cases canonical_eq
  letI : DecidableEq V := Classical.decEq V
  have canonical_adj : graphDecAdj = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases canonical_adj
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have buying_term : lp.buying v * lp.opening v ≤ lp.buyingBudget :=
    Finset.single_le_sum (fun a _ => mul_nonneg (lp.buying_nonneg a) (lp.opening_bounds a).1) (Finset.mem_univ v)
  have flow_term : lp.flow i path ≤ ∑ q : G.Path (lp.source i) (lp.target i),
      if v ∈ q.val.support then lp.flow i q else 0 := by
    have bound := Finset.single_le_sum (s := Finset.univ)
      (f := fun q : G.Path (lp.source i) (lp.target i) => if v ∈ q.val.support then lp.flow i q else 0)
      (fun q _ => by split_ifs; exact lp.flow_nonneg i q; rfl) (Finset.mem_univ path)
    simpa only [if_pos member] using bound
  have opening_pos : 0 < lp.opening v := positive.trans_le (flow_term.trans (lp.capacity i v))
  rw [budget_zero] at buying_term
  have buying_nonneg := lp.buying_nonneg v
  nlinarith

theorem short_positive_path (lp : NodeLP G h) (i : Fin h) :
    ∃ path : G.Path (lp.source i) (lp.target i), 0 < lp.flow i path ∧
      NodeMetric.walkWeight G lp.physical path.val ≤ lp.fractionalLength i := by
  have canonical_eq : vertexDecEq = Classical.decEq V := Subsingleton.elim _ _
  cases canonical_eq
  letI : DecidableEq V := Classical.decEq V
  have canonical_adj : graphDecAdj = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases canonical_adj
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨path, positive⟩ := lp.exists_positive_flow_path i
  by_contra missing
  push Not at missing
  have nonnegative : ∀ q : G.Path (lp.source i) (lp.target i),
      0 ≤ (NodeMetric.walkWeight G lp.physical q.val - lp.fractionalLength i) * lp.flow i q := by
    intro q
    by_cases pos : 0 < lp.flow i q
    · exact mul_nonneg (sub_nonneg.mpr (missing q pos).le) (lp.flow_nonneg i q)
    · have zero : lp.flow i q = 0 := le_antisymm (le_of_not_gt pos) (lp.flow_nonneg i q)
      simp only [zero, mul_zero, le_refl]
  have sum_pos : 0 < ∑ q : G.Path (lp.source i) (lp.target i),
      (NodeMetric.walkWeight G lp.physical q.val - lp.fractionalLength i) * lp.flow i q := by
    apply Finset.sum_pos' (fun q _ => nonnegative q)
    exact ⟨path, Finset.mem_univ _, mul_pos (sub_pos.mpr (missing path positive)) positive⟩
  have sum_zero : (∑ q : G.Path (lp.source i) (lp.target i),
      (NodeMetric.walkWeight G lp.physical q.val - lp.fractionalLength i) * lp.flow i q) = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, lp.unit, mul_one]
    exact sub_self _
  linarith

theorem freeRoutes_correct (physical : V → ℚ) (nonnegative : ∀ v, 0 ≤ physical v)
    (source target : Fin h → V) (lengths : Fin h → ℚ) (state : RoundingState G)
    (witness : ∀ i, HasShortBoughtRoute G physical state (source i) (target i) (lengths i))
    (order : List (Fin h)) :
    ∃ entries, freeRoutes G numbering physical source target lengths state order = some entries ∧
      entries.map (fun entry => entry.1) = order ∧
      ∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ state.bought ∧
        NodeMetric.walkWeight G physical entry.2.val ≤ lengths entry.1 := by
  induction order with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons i order ih =>
    cases query : Attachment.boughtRoute G numbering physical state (source i) (target i) (lengths i) with
    | none => exact False.elim ((Attachment.boughtRoute_none_iff G numbering physical nonnegative state
        (source i) (target i) (lengths i)).mp query (witness i))
    | some path =>
      have bounded := Attachment.boughtRoute_some G numbering physical nonnegative state path query
      obtain ⟨entries, computed, indices, routes⟩ := ih
      refine ⟨⟨i, path⟩ :: entries, ?_, by simp only [List.map_cons, indices], ?_⟩
      · simp only [freeRoutes, query, computed, Option.map_some]
      · intro entry member
        rcases List.mem_cons.mp member with same | old
        · subst entry
          exact bounded
        · exact routes entry old

theorem zero_budget_routes (lp : NodeLP G h) (budget_zero : lp.buyingBudget = 0)
    (lengths : Fin h → ℚ) (metadata : ∀ i, lengths i = lp.fractionalLength i) :
    ∃ entries, freeRoutes G numbering lp.physical lp.source lp.target lengths
        (zeroState G numbering lp.buying) (List.finRange h) = some entries ∧
      entries.map (fun entry => entry.1) = List.finRange h ∧
      ∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ (zeroState G numbering lp.buying).bought ∧
        NodeMetric.walkWeight G lp.physical entry.2.val ≤ lp.fractionalLength entry.1 := by
  have witnesses : ∀ i, HasShortBoughtRoute G lp.physical (zeroState G numbering lp.buying)
      (lp.source i) (lp.target i) (lengths i) := by
    intro i
    obtain ⟨path, positive, short⟩ := short_positive_path lp i
    refine ⟨path, ?_, by simpa only [metadata i] using short⟩
    intro v member
    apply (Core.mem_zeroBuyingNodes numbering lp.buying v).mpr
    exact positive_path_free lp budget_zero i path positive v (List.mem_toFinset.mp member)
  obtain ⟨entries, computed, indices, routes⟩ := freeRoutes_correct numbering lp.physical lp.physical_nonneg
    lp.source lp.target lengths (zeroState G numbering lp.buying) witnesses (List.finRange h)
  exact ⟨entries, computed, indices, fun entry member => by simpa only [metadata entry.1] using routes entry member⟩

theorem zeroState_buying (buying : V → ℚ) : nodeBuying buying (zeroState G numbering buying).bought = 0 := by
  unfold nodeBuying
  apply Finset.sum_eq_zero
  intro v _
  by_cases member : v ∈ (zeroState G numbering buying).bought
  · rw [if_pos member]
    exact (Core.mem_zeroBuyingNodes numbering buying v).mp member
  · rw [if_neg member]

end BuyAtBulk.Computation.Rounding
