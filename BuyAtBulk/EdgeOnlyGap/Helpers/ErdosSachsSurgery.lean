import BuyAtBulk.EdgeOnlyGap.Helpers.ErdosSachsWalks
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card

/-! Edge additions and edge swaps preserving maximum degree and girth, used in the proof of the
Erdős–Sachs theorem. -/

noncomputable section

namespace BuyAtBulk.EdgeOnlyGap.ErdosSachs

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Maximum degree at most `d` and every cycle of length at least `g`. -/
def Good (d g : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ w, G.degree w ≤ d) ∧ ∀ a (c : G.Walk a a), c.IsCycle → g ≤ c.length

/-- Every walk from `a` to `b` has length at least `g - 1`. -/
def Far (G : SimpleGraph V) (g : ℕ) (a b : V) : Prop :=
  ∀ p : G.Walk a b, g ≤ p.length + 1

omit [Fintype V] in
theorem Far.symm {G : SimpleGraph V} {g : ℕ} {a b : V} (h : Far G g a b) : Far G g b a :=
  fun p => by simpa using h p.reverse

omit [Fintype V] in
theorem Far.ne {G : SimpleGraph V} {g : ℕ} {a b : V} (h : Far G g a b) (hg : 3 ≤ g) : a ≠ b := by
  rintro rfl; have := h .nil; simp at this; omega

omit [Fintype V] in
theorem Far.not_adj {G : SimpleGraph V} {g : ℕ} {a b : V} (h : Far G g a b) (hg : 3 ≤ g) :
    ¬ G.Adj a b := by
  intro hab; have := h (.cons hab .nil); simp at this; omega

/-- At most one neighbour `z` of `w` has `s(w, z) = e`, and none unless `w ∈ e`. -/
theorem card_filter_edge_le (w : V) (e : Sym2 V) :
    (univ.filter fun z => s(w, z) = e).card ≤ if w ∈ e then 1 else 0 := by
  split_ifs with hw
  · obtain ⟨o, rfl⟩ := Sym2.mem_iff_exists.mp hw
    calc (univ.filter fun z => s(w, z) = s(w, o)).card ≤ ({o} : Finset V).card := by
          apply card_le_card
          intro z hz
          simp only [mem_filter, mem_univ, true_and, Sym2.congr_right] at hz
          simp [hz]
      _ = 1 := card_singleton o
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro z _ hz
    exact hw (hz ▸ Sym2.mem_mk_left w z)

/-! ### Adding one edge -/

/-- `G` with the edge `ux` added. -/
def addEdge (G : SimpleGraph V) (u x : V) : SimpleGraph V :=
  fromEdgeSet (G.edgeSet ∪ {s(u, x)})

omit [Fintype V] in
theorem mem_addEdge_edgeSet {G : SimpleGraph V} {u x : V} {e : Sym2 V} :
    e ∈ (addEdge G u x).edgeSet ↔ (e ∈ G.edgeSet ∨ e = s(u, x)) ∧ ¬ e.IsDiag := by
  simp [addEdge, edgeSet_fromEdgeSet]
  tauto

theorem addEdge_degree_le (G : SimpleGraph V) (u x w : V) :
    (addEdge G u x).degree w ≤ G.degree w + if w ∈ s(u, x) then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  calc ((addEdge G u x).neighborFinset w).card
      ≤ (G.neighborFinset w ∪ univ.filter fun z => s(w, z) = s(u, x)).card := by
        apply card_le_card
        intro z hz
        rw [mem_neighborFinset, addEdge, fromEdgeSet_adj] at hz
        simp only [mem_union, mem_neighborFinset, mem_filter, mem_univ, true_and]
        rcases hz.1 with h | h
        · exact Or.inl h
        · exact Or.inr (by simpa using h)
    _ ≤ _ := (card_union_le _ _).trans (by gcongr; exact card_filter_edge_le w _)

theorem addEdge_good {G : SimpleGraph V} {d g : ℕ} (hG : Good d g G) {u x : V}
    (hu : G.degree u < d) (hx : G.degree x < d) (hfar : Far G g u x) (hg : 3 ≤ g) :
    Good d g (addEdge G u x) ∧ G.edgeSet.ncard < (addEdge G u x).edgeSet.ncard := by
  have hne := hfar.ne hg
  have hnadj := hfar.not_adj hg
  refine ⟨⟨fun w => ?_, fun a c hc => ?_⟩, ?_⟩
  · have := addEdge_degree_le G u x w
    have := hG.1 w
    split_ifs at * with hw
    · rcases Sym2.mem_iff.mp hw with rfl | rfl <;> omega
    · omega
  · by_contra hlt
    push Not at hlt
    by_cases he : s(u, x) ∈ c.edges
    · obtain ⟨W, hW, hWc, hWl⟩ := cycle_edge_walk c hc he
      have hWG : ∀ e ∈ W.edges, e ∈ G.edgeSet := by
        intro e he'
        have := (mem_addEdge_edgeSet.mp (c.edges_subset_edgeSet (hWc e he'))).1
        rcases this with h | rfl
        · exact h
        · exact absurd he' hW
      have := hfar.symm (W.transfer G hWG)
      rw [Walk.length_transfer] at this
      omega
    · have hcG : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e he'
        rcases (mem_addEdge_edgeSet.mp (c.edges_subset_edgeSet he')).1 with h | rfl
        · exact h
        · exact absurd he' he
      have := hG.2 a (c.transfer G hcG) (hc.transfer hcG)
      rw [Walk.length_transfer] at this
      omega
  · have hset : (addEdge G u x).edgeSet = insert s(u, x) G.edgeSet := by
      ext e
      rw [mem_addEdge_edgeSet, Set.mem_insert_iff]
      constructor
      · rintro ⟨h | h, -⟩
        · exact Or.inr h
        · exact Or.inl h
      · rintro (rfl | h)
        · exact ⟨Or.inr rfl, by simpa using hne⟩
        · exact ⟨Or.inl h, G.not_isDiag_of_mem_edgeSet h⟩
    rw [hset, Set.ncard_insert_of_notMem (by simpa using hnadj)]
    omega

/-! ### Swapping `xy` for `ux` and `vy` -/

/-- `G` with `xy` removed and `ux`, `vy` added. -/
def swapEdges (G : SimpleGraph V) (u v x y : V) : SimpleGraph V :=
  fromEdgeSet ((G.edgeSet \ {s(x, y)}) ∪ {s(u, x), s(v, y)})

omit [Fintype V] in
theorem mem_swapEdges_edgeSet {G : SimpleGraph V} {u v x y : V} {e : Sym2 V} :
    e ∈ (swapEdges G u v x y).edgeSet ↔
      ((e ∈ G.edgeSet ∧ e ≠ s(x, y)) ∨ e = s(u, x) ∨ e = s(v, y)) ∧ ¬ e.IsDiag := by
  simp [swapEdges, edgeSet_fromEdgeSet]
  tauto

theorem swapEdges_degree_le (G : SimpleGraph V) (u v x y w : V) (hxy : G.Adj x y) :
    (swapEdges G u v x y).degree w + (if w ∈ s(x, y) then 1 else 0) ≤
      G.degree w + (if w ∈ s(u, x) then 1 else 0) + (if w ∈ s(v, y) then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  set N := G.neighborFinset w
  set N₀ := N.filter fun z => s(w, z) ≠ s(x, y)
  have hsub : (swapEdges G u v x y).neighborFinset w ⊆
      (N₀ ∪ univ.filter fun z => s(w, z) = s(u, x)) ∪ univ.filter fun z => s(w, z) = s(v, y) := by
    intro z hz
    rw [mem_neighborFinset, swapEdges, fromEdgeSet_adj] at hz
    simp only [N₀, N, mem_union, mem_filter, mem_neighborFinset, mem_univ, true_and]
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff,
      mem_edgeSet] at hz
    tauto
  have hN₀ : N₀.card + (if w ∈ s(x, y) then 1 else 0) ≤ N.card := by
    split_ifs with hw
    · obtain ⟨o, ho⟩ := Sym2.mem_iff_exists.mp hw
      have hoN : o ∈ N := by
        rw [mem_neighborFinset, ← mem_edgeSet, ← ho]; exact hxy
      have : N₀ ⊆ N.erase o := by
        intro z hz
        simp only [N₀, mem_filter] at hz
        refine mem_erase.mpr ⟨?_, hz.1⟩
        rintro rfl; exact hz.2 ho.symm
      have := card_le_card this
      rw [card_erase_of_mem hoN] at this
      have : 0 < N.card := card_pos.mpr ⟨o, hoN⟩
      omega
    · simpa using card_filter_le N _
  have h1 := card_filter_edge_le w s(u, x)
  have h2 := card_filter_edge_le w s(v, y)
  have := card_le_card hsub
  have := card_union_le (N₀ ∪ univ.filter fun z => s(w, z) = s(u, x))
    (univ.filter fun z => s(w, z) = s(v, y))
  have := card_union_le N₀ (univ.filter fun z => s(w, z) = s(u, x))
  omega

theorem swapEdges_good {G : SimpleGraph V} {d g : ℕ} (hG : Good d g G) {u v x y : V}
    (hxy : G.Adj x y) (fux : Far G g u x) (fvx : Far G g v x) (fvy : Far G g v y)
    (fuy : Far G g u y) (hg : 3 ≤ g)
    (hu : G.degree u + 1 + (if u = v then 1 else 0) ≤ d) (hv : G.degree v + 1 ≤ d) :
    Good d g (swapEdges G u v x y) ∧
      G.edgeSet.ncard < (swapEdges G u v x y).edgeSet.ncard := by
  have hux := fux.ne hg
  have hvy := fvy.ne hg
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have hvx := fvx.ne hg
  have huy := fuy.ne hg
  refine ⟨⟨fun w => ?_, fun a c hc => ?_⟩, ?_⟩
  · have h := swapEdges_degree_le G u v x y w hxy
    have := hG.1 w
    by_cases hwu : w = u
    · subst hwu
      have : ¬ w ∈ s(x, y) := by simp [Sym2.mem_iff, hux, huy]
      by_cases hwv : w = v
      · subst hwv; simp [Sym2.mem_iff, this] at h hu ⊢; omega
      · simp [Sym2.mem_iff, this, hwv, huy] at h hu; omega
    by_cases hwv : w = v
    · subst hwv
      have : ¬ w ∈ s(x, y) := by simp [Sym2.mem_iff, hvx, hvy]
      simp [Sym2.mem_iff, this, hwu, hvx] at h; omega
    by_cases hwx : w = x
    · subst hwx; simp [Sym2.mem_iff, hwu, hwv, hxy'] at h; omega
    by_cases hwy : w = y
    · subst hwy; simp [Sym2.mem_iff, hwu, hwv, hxy'.symm] at h; omega
    simp [Sym2.mem_iff, hwu, hwv, hwx, hwy] at h; omega
  · by_contra hlt
    push Not at hlt
    have hmem := fun e (he : e ∈ c.edges) => mem_swapEdges_edgeSet.mp (c.edges_subset_edgeSet he)
    by_cases he : s(u, x) ∈ c.edges
    · obtain ⟨W, hW, hWc, hWl⟩ := cycle_edge_walk c hc he
      have hsplit : ∀ e ∈ W.edges,
          e ∈ (G.deleteEdges {s(x, y)}).edgeSet ∨ e = s(v, y) := by
        intro e he'
        rw [edgeSet_deleteEdges]
        rcases (hmem e (hWc e he')).1 with ⟨h1, h2⟩ | rfl | rfl
        · exact Or.inl ⟨h1, h2⟩
        · exact absurd he' hW
        · exact Or.inr rfl
      rcases walk_split (G.deleteEdges {s(x, y)}) v y W hsplit with
        ⟨W', hl⟩ | ⟨p₁, q₁, W₁, W₂, hs, hl⟩
      · obtain ⟨W'', hl', -⟩ := deleteEdges_walk W'
        have := fux.symm W''
        omega
      · obtain ⟨W₁', hl₁, hav⟩ := deleteEdges_walk W₁
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have := fvx.symm W₁'
          omega
        · have := girth_avoid hG.2 hxy W₁' hav
          omega
    · by_cases hf : s(v, y) ∈ c.edges
      · obtain ⟨W, hW, hWc, hWl⟩ := cycle_edge_walk c hc hf
        have hWG : ∀ e ∈ W.edges, e ∈ G.edgeSet := by
          intro e he'
          rcases (hmem e (hWc e he')).1 with ⟨h1, -⟩ | rfl | rfl
          · exact h1
          · exact absurd (hWc _ he') he
          · exact absurd he' hW
        have := fvy (W.transfer G hWG).reverse
        rw [Walk.length_reverse, Walk.length_transfer] at this
        omega
      · have hcG : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
          intro e he'
          rcases (hmem e he').1 with ⟨h1, -⟩ | rfl | rfl
          · exact h1
          · exact absurd he' he
          · exact absurd he' hf
        have := hG.2 a (c.transfer G hcG) (hc.transfer hcG)
        rw [Walk.length_transfer] at this
        omega
  · have hnux : s(u, x) ∉ G.edgeSet := fux.not_adj hg
    have hnvy : s(v, y) ∉ G.edgeSet := fvy.not_adj hg
    have hset : (swapEdges G u v x y).edgeSet =
        insert s(v, y) (insert s(u, x) (G.edgeSet \ {s(x, y)})) := by
      ext e
      rw [mem_swapEdges_edgeSet]
      simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | rfl | rfl, -⟩
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · rintro (rfl | rfl | h)
        · exact ⟨Or.inr (Or.inr rfl), by simpa using hvy⟩
        · exact ⟨Or.inr (Or.inl rfl), by simpa using hux⟩
        · exact ⟨Or.inl h, G.not_isDiag_of_mem_edgeSet h.1⟩
    have hvy_ne : s(v, y) ≠ s(u, x) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hxy' h2.symm
      · exact huy h2.symm
    rw [hset, Set.ncard_insert_of_notMem,
      Set.ncard_exchange (s := G.edgeSet) (a := s(u, x)) (b := s(x, y)) hnux (G.mem_edgeSet.mpr hxy)]
    · omega
    · simp only [Set.mem_insert_iff, Set.mem_sdiff, not_or]
      exact ⟨hvy_ne, fun h => hnvy h.1⟩

end BuyAtBulk.EdgeOnlyGap.ErdosSachs
