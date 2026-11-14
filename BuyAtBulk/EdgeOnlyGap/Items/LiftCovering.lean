import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import BuyAtBulk.EdgeOnlyGap.Helpers.EdgeCard
import BuyAtBulk.EdgeOnlyGap.Items.Parameters

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

private lemma liftGraph_adj_edge (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (e : Edges H) (j k : Fin q) :
    (liftGraph H q π).Adj (e.val.1, j) (e.val.2, k) ↔ k = π e j := by
  unfold liftGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨e', h1, h2, hk⟩ | ⟨e', h1, h2, _⟩⟩
    · dsimp at h1 h2
      have he : e' = e := Subtype.ext (Prod.ext h1.symm h2.symm)
      subst he
      exact hk
    · dsimp at h1 h2
      have hlt1 : e.val.1 < e.val.2 := e.prop.1
      have hlt2 : e'.val.1 < e'.val.2 := e'.prop.1
      rw [← h1, ← h2] at hlt2
      exact False.elim (lt_asymm hlt1 hlt2)
  · intro hk
    refine ⟨?_, Or.inl ⟨e, rfl, rfl, hk⟩⟩
    intro heq
    have h1 : e.val.1 = e.val.2 := congrArg Prod.fst heq
    exact ne_of_lt e.prop.1 h1

private lemma liftGraph_degree (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (v : Fin H.n × Fin q) :
    (liftGraph H q π).degree v = H.graph.degree v.1 := by
  classical
  have hadj_fst : ∀ w : Fin H.n × Fin q, (liftGraph H q π).Adj v w → H.graph.Adj v.1 w.1 := by
    intro w hw
    unfold liftGraph at hw
    rw [SimpleGraph.fromRel_adj] at hw
    rcases hw with ⟨_, ⟨e, h1, h2, _⟩ | ⟨e, h1, h2, _⟩⟩
    · rw [h1, h2]; exact e.prop.2
    · rw [h1, h2]; exact e.prop.2.symm
  let proj : (liftGraph H q π).neighborSet v → H.graph.neighborSet v.1 :=
    fun w => ⟨w.val.1, hadj_fst w.val w.prop⟩
  have hinj : Function.Injective proj := by
    intro w₁ w₂ h
    have hx : w₁.val.1 = w₂.val.1 := congrArg Subtype.val h
    have hadj : H.graph.Adj v.1 w₁.val.1 := hadj_fst w₁.val w₁.prop
    apply Subtype.ext
    apply Prod.ext hx
    rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
    · let e : Edges H := ⟨(v.1, w₁.val.1), hlt, hadj⟩
      have h1 : (liftGraph H q π).Adj (e.val.1, v.2) (e.val.2, w₁.val.2) := w₁.prop
      have h2 : (liftGraph H q π).Adj (e.val.1, v.2) (e.val.2, w₂.val.2) := by
        change (liftGraph H q π).Adj v (w₁.val.1, w₂.val.2)
        rw [hx]; exact w₂.prop
      rw [liftGraph_adj_edge] at h1 h2
      exact h1.trans h2.symm
    · let e : Edges H := ⟨(w₁.val.1, v.1), hgt, hadj.symm⟩
      have h1 : (liftGraph H q π).Adj (e.val.1, w₁.val.2) (e.val.2, v.2) := w₁.prop.symm
      have h2 : (liftGraph H q π).Adj (e.val.1, w₂.val.2) (e.val.2, v.2) := by
        change (liftGraph H q π).Adj (w₁.val.1, w₂.val.2) v
        rw [hx]; exact w₂.prop.symm
      rw [liftGraph_adj_edge] at h1 h2
      exact (π e).injective (h1.symm.trans h2)
  have hsurj : Function.Surjective proj := by
    intro x
    have hadj : H.graph.Adj v.1 x.val := x.prop
    rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
    · let e : Edges H := ⟨(v.1, x.val), hlt, hadj⟩
      have hw : (liftGraph H q π).Adj v (x.val, π e v.2) :=
        (liftGraph_adj_edge H q π e v.2 (π e v.2)).mpr rfl
      exact ⟨⟨(x.val, π e v.2), hw⟩, rfl⟩
    · let e : Edges H := ⟨(x.val, v.1), hgt, hadj.symm⟩
      have hw : (liftGraph H q π).Adj (x.val, (π e).symm v.2) v :=
        (liftGraph_adj_edge H q π e ((π e).symm v.2) v.2).mpr (by simp)
      exact ⟨⟨(x.val, (π e).symm v.2), hw.symm⟩, rfl⟩
  rw [← (liftGraph H q π).card_neighborSet_eq_degree, ← H.graph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (Equiv.ofBijective proj ⟨hinj, hsurj⟩)

private lemma comap_degree {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj] (e : α ≃ β) (x : α) :
    (G.comap e).degree x = G.degree (e x) := by
  classical
  rw [← (G.comap e).card_neighborSet_eq_degree, ← G.card_neighborSet_eq_degree]
  refine Fintype.card_congr
    { toFun := fun y => ⟨e y.val, y.prop⟩
      invFun := fun y => ⟨e.symm y.val, by
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.comap_adj, Equiv.apply_symm_apply]
        exact y.prop⟩
      left_inv := fun y => by ext; simp
      right_inv := fun y => by ext; simp }

/-- Implicit local matching uniqueness and lift counts, pp. 2–3, 5. -/
theorem liftCovering (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
  (lifted H q π).n = H.n*q ∧
  requests (lifted H q π) = q*requests H ∧
  (∀ v : Fin H.n × Fin q, (liftGraph H q π).degree v = H.graph.degree v.1) ∧
  (∀ (e : Edges H) (j k : Fin q),
    (liftGraph H q π).Adj (e.val.1,j) (e.val.2,k) ↔ k=π e j) := by
  classical
  refine ⟨rfl, ?_, liftGraph_degree H q π, liftGraph_adj_edge H q π⟩
  let ev : Fin ((lifted H q π).n) ≃ Fin H.n × Fin q :=
    (finCongr (by simp [lifted] : (lifted H q π).n = Fintype.card (Fin H.n × Fin q))).trans
      (Fintype.equivFin (Fin H.n × Fin q)).symm
  have hdeg_lifted : ∀ x : Fin (lifted H q π).n,
      (lifted H q π).graph.degree x = (liftGraph H q π).degree (ev x) :=
    fun x => comap_degree (liftGraph H q π) ev x
  have hsum1 : 2 * requests (lifted H q π) = ∑ x, (lifted H q π).graph.degree x := by
    rw [requests, edgeCard, (lifted H q π).graph.sum_degrees_eq_twice_card_edges]
  have hsum2 : 2 * requests H = ∑ u, H.graph.degree u := by
    rw [requests, edgeCard, H.graph.sum_degrees_eq_twice_card_edges]
  have hsum3 : (∑ x, (lifted H q π).graph.degree x) = q * ∑ u, H.graph.degree u := by
    calc
      (∑ x, (lifted H q π).graph.degree x) = ∑ x, (liftGraph H q π).degree (ev x) :=
        Finset.sum_congr rfl fun x _ => hdeg_lifted x
      _ = ∑ v : Fin H.n × Fin q, (liftGraph H q π).degree v :=
        Equiv.sum_comp ev (fun v => (liftGraph H q π).degree v)
      _ = ∑ v : Fin H.n × Fin q, H.graph.degree v.1 :=
        Finset.sum_congr rfl fun v _ => liftGraph_degree H q π v
      _ = ∑ u : Fin H.n, ∑ _j : Fin q, H.graph.degree u := Fintype.sum_prod_type _
      _ = ∑ u : Fin H.n, q * H.graph.degree u := by simp
      _ = q * ∑ u : Fin H.n, H.graph.degree u := by rw [Finset.mul_sum]
  rw [hsum3, ← hsum2] at hsum1
  rw [Nat.mul_left_comm q 2] at hsum1
  omega

end BuyAtBulk.EdgeOnlyGap
