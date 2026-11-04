import BuyAtBulk.UpperBound.Girth.ShortPaths
import Mathlib.Data.Fintype.BigOperators

namespace BuyAtBulk.UpperBound.Girth
open SimpleGraph
open scoped BigOperators

/-- All length-`i` simple paths from a fixed root, with their endpoints. -/
abbrev RootedPath {V : Type} (G : SimpleGraph V) (root : V) (i : ℕ) :=
  (v : V) × {p : G.Walk root v // p.IsPath ∧ p.length = i}

noncomputable instance rootedPathFintype {V : Type} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) : Fintype (RootedPath G root i) := by
  classical
  unfold RootedPath
  infer_instance

/-- The neighbor choices excluding the one parent of a rooted path. -/
noncomputable def choices {V : Type} [Fintype V] (G : SimpleGraph V)
    {root : V} {i : ℕ} (p : RootedPath G root i) : Finset V := by
  classical
  exact (G.neighborFinset p.1).erase p.2.val.penultimate

noncomputable def extend {V : Type} [Fintype V] {G : SimpleGraph V} {r i : ℕ}
    (hr : 1 ≤ r) (hg : HighGirth G r) (hi : i < r) {root : V}
    (e : (p : RootedPath G root i) × {w // w ∈ choices G p}) :
    RootedPath G root (i + 1) := by
  classical
  obtain ⟨⟨v, p, hp, hlen⟩, w, hw⟩ := e
  have hw' : w ≠ p.penultimate ∧ G.Adj v w := by
    simpa only [choices, Finset.mem_erase, mem_neighborFinset] using hw
  have hnot : w ∉ p.support := by
    intro hmem
    exact hw'.1 (neighbor_mem_support_eq_parent hr hg p hp (by omega) hw'.2 hmem)
  exact ⟨w, p.concat hw'.2, hp.concat hnot hw'.2, by simp [hlen]⟩

/-- Distinct parent-path/child choices yield distinct extended paths. -/
theorem extend_injective {V : Type} [Fintype V] {G : SimpleGraph V} {r i : ℕ}
    (hr : 1 ≤ r) (hg : HighGirth G r) (hi : i < r) (root : V) :
    Function.Injective (extend hr hg hi (root := root)) := by
  classical
  rintro ⟨⟨v, p, hp, hlen⟩, w, hw⟩ ⟨⟨v', p', hp', hlen'⟩, w', hw'⟩ heq
  have hww : w = w' := congrArg Sigma.fst heq
  subst w'
  have hwalk : p.concat (by simpa [choices] using (Finset.mem_erase.mp hw).2) =
      p'.concat (by simpa [choices] using (Finset.mem_erase.mp hw').2) := by
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
  obtain ⟨hvv, hpp⟩ := SimpleGraph.Walk.concat_inj hwalk
  subst v'
  have hpp' : p = p' := by simpa using hpp
  subst p'
  rfl

/-- A girth obstruction makes the endpoint map injective on short paths. -/
theorem rootedPath_card_le {V : Type} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    (hg : HighGirth G r) (root : V) : Fintype.card (RootedPath G root r) ≤ Fintype.card V := by
  classical
  apply Fintype.card_le_of_injective (fun p : RootedPath G root r => p.1)
  rintro ⟨v, p, hp, hlen⟩ ⟨v', p', hp', hlen'⟩ heq
  dsimp at heq
  subst v'
  have hpp := short_path_unique hg p p' hp hp' (by omega)
  subst p'
  rfl

/-- Minimum-degree exploration grows by at least `d-1` at every level. -/
theorem rootedPath_card_lower {V : Type} [Fintype V] {G : SimpleGraph V}
    {r d : ℕ} (hr : 1 ≤ r) (hg : HighGirth G r)
    (hdegree : ∀ v, d ≤ Nat.card (G.neighborSet v)) (root : V) :
    ∀ i ≤ r, (d - 1) ^ i ≤ Fintype.card (RootedPath G root i) := by
  classical
  intro i hi
  induction i with
  | zero =>
    simp only [pow_zero]
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨root, .nil, .nil, rfl⟩⟩
  | succ i ih =>
    have ih' := ih (by omega)
    have hstep : Fintype.card (RootedPath G root i) * (d - 1) ≤
        Fintype.card (RootedPath G root (i + 1)) := calc
      _ = ∑ p : RootedPath G root i, (d - 1) := by simp
      _ ≤ ∑ p : RootedPath G root i, (choices G p).card := by
        apply Finset.sum_le_sum
        intro p hp
        have hdeg : d ≤ G.degree p.1 := by
          simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hdegree p.1
        exact (Nat.sub_le_sub_right hdeg 1).trans
          (by simpa [choices, card_neighborFinset_eq_degree] using
            (Finset.pred_card_le_card_erase (s := G.neighborFinset p.1) (a := p.2.val.penultimate)))
      _ = Fintype.card ((p : RootedPath G root i) × {w // w ∈ choices G p}) := by simp
      _ ≤ _ := Fintype.card_le_of_injective _ (extend_injective hr hg (by omega) root)
    exact (by simpa [pow_succ] using (Nat.mul_le_mul_right (d - 1) ih').trans hstep)

/-- The elementary Moore inequality, derived from actual graph paths. -/
theorem moore_bound {V : Type} [Fintype V] {G : SimpleGraph V} {r d : ℕ}
    (hr : 1 ≤ r) (hg : HighGirth G r) (hdegree : ∀ v, d ≤ Nat.card (G.neighborSet v)) (root : V) :
    (d - 1) ^ r ≤ Fintype.card V :=
  (rootedPath_card_lower hr hg hdegree root r le_rfl).trans (rootedPath_card_le hg root)

end BuyAtBulk.UpperBound.Girth
