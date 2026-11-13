import BuyAtBulk.EdgeOnlyGap.Helpers.ErdosSachsSurgery
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The maximal-graph argument for the Erdős–Sachs theorem: an edge-maximal graph with maximum
degree `d` and girth `g` on `2·d^g` vertices is `d`-regular. -/

noncomputable section

namespace BuyAtBulk.EdgeOnlyGap.ErdosSachs

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Vertices reachable from `c` by a walk of length at most `r`. -/
def ball (G : SimpleGraph V) (c : V) (r : ℕ) : Finset V :=
  univ.filter fun z => ∃ p : G.Walk c z, p.length ≤ r

/-- The Moore-type count `1 + d + ⋯ + d^r`. -/
def ballBound (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => 1 + d * ballBound d r

theorem card_ball_le (G : SimpleGraph V) {d : ℕ} (hdeg : ∀ w, G.degree w ≤ d) :
    ∀ (r : ℕ) (c : V), (ball G c r).card ≤ ballBound d r
  | 0, c => by
    calc (ball G c 0).card ≤ ({c} : Finset V).card := by
          apply card_le_card
          intro z hz
          simp only [ball, mem_filter, mem_univ, true_and, Nat.le_zero] at hz
          obtain ⟨p, hp⟩ := hz
          simp [(Walk.eq_of_length_eq_zero hp).symm]
      _ = ballBound d 0 := by simp [ballBound]
  | r + 1, c => by
    have hsub : ball G c (r + 1) ⊆ insert c ((G.neighborFinset c).biUnion fun w => ball G w r) := by
      intro z hz
      simp only [ball, mem_filter, mem_univ, true_and] at hz
      obtain ⟨p, hp⟩ := hz
      cases p with
      | nil => exact mem_insert_self _ _
      | @cons _ w _ h p' =>
        refine mem_insert_of_mem (mem_biUnion.mpr ⟨w, (G.mem_neighborFinset _ _).mpr h, ?_⟩)
        simp only [ball, mem_filter, mem_univ, true_and]
        exact ⟨p', by simp at hp; omega⟩
    calc (ball G c (r + 1)).card
        ≤ (insert c ((G.neighborFinset c).biUnion fun w => ball G w r)).card := card_le_card hsub
      _ ≤ ((G.neighborFinset c).biUnion fun w => ball G w r).card + 1 := card_insert_le _ _
      _ ≤ (∑ w ∈ G.neighborFinset c, (ball G w r).card) + 1 := by gcongr; exact card_biUnion_le
      _ ≤ (∑ _w ∈ G.neighborFinset c, ballBound d r) + 1 := by
          gcongr with w; exact card_ball_le G hdeg r w
      _ = G.degree c * ballBound d r + 1 := by
          rw [sum_const, smul_eq_mul, card_neighborFinset_eq_degree]
      _ ≤ d * ballBound d r + 1 := by gcongr; exact hdeg c
      _ = ballBound d (r + 1) := by simp [ballBound]; ring

theorem ballBound_lt {d : ℕ} (hd : 2 ≤ d) (r : ℕ) : ballBound d r < d ^ (r + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have key : ∀ r, e * ballBound (e + 1) r + 1 ≤ (e + 1) ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [ballBound]
    | succ r ih =>
      calc e * ballBound (e + 1) (r + 1) + 1 = (e + 1) * (e * ballBound (e + 1) r + 1) := by
            simp only [ballBound]; ring
        _ ≤ (e + 1) * (e + 1) ^ (r + 1) := Nat.mul_le_mul_left _ ih
        _ = (e + 1) ^ (r + 1 + 1) := by ring
  have := key r
  have : ballBound (e + 1) r ≤ e * ballBound (e + 1) r := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The Erdős–Sachs construction on `2·d^g` vertices. -/
theorem exists_regular_girth (d g : ℕ) (hd : 4 ≤ d) (hg : 4 ≤ g) :
    ∃ G : SimpleGraph (Fin (2 * d ^ g)), (∀ w, G.degree w = d) ∧
      ∀ a (c : G.Walk a a), c.IsCycle → g ≤ c.length := by
  set N := 2 * d ^ g with hN
  have hne : (univ.filter fun G : SimpleGraph (Fin N) => Good d g G).Nonempty := by
    refine ⟨⊥, mem_filter.mpr ⟨mem_univ _, fun w => by simp, fun a c hc => ?_⟩⟩
    cases c with
    | nil => exact absurd hc (by simp [Walk.isCycle_def])
    | cons h _ => exact absurd h (by simp)
  obtain ⟨G, hGmem, hGmax⟩ := exists_max_image _ (fun G : SimpleGraph (Fin N) => G.edgeSet.ncard) hne
  have hG : Good d g G := (mem_filter.mp hGmem).2
  have hmax : ∀ G' : SimpleGraph (Fin N), Good d g G' → G'.edgeSet.ncard ≤ G.edgeSet.ncard :=
    fun G' h => hGmax G' (mem_filter.mpr ⟨mem_univ _, h⟩)
  refine ⟨G, ?_, hG.2⟩
  -- a vertex far from a deficient vertex is not deficient
  have claim : ∀ u x, G.degree u < d → Far G g u x → G.degree x = d := by
    intro u x hu hfar
    by_contra hx
    have hx' : G.degree x < d := lt_of_le_of_ne (hG.1 x) hx
    obtain ⟨hgood, hlt⟩ := addEdge_good hG hu hx' hfar (by omega)
    exact absurd (hmax _ hgood) (not_le.mpr hlt)
  intro u
  by_contra hu'
  have hu : G.degree u < d := lt_of_le_of_ne (hG.1 u) hu'
  -- choose the partner `v`
  obtain ⟨v, hv, hpair⟩ : ∃ v, G.degree v < d ∧
      G.degree u + 1 + (if u = v then 1 else 0) ≤ d := by
    by_cases h2 : G.degree u + 2 ≤ d
    · exact ⟨u, hu, by simp; omega⟩
    · by_contra hno
      push Not at hno
      have hall : ∀ w ∈ univ.erase u, G.degree w = d := by
        intro w hw
        have hwu : u ≠ w := fun h => (mem_erase.mp hw).1 h.symm
        by_contra hw'
        have := hno w (lt_of_le_of_ne (hG.1 w) hw')
        simp [hwu] at this
        omega
      have hsum := G.sum_degrees_eq_twice_card_edges
      rw [← add_sum_erase _ _ (mem_univ u), sum_congr rfl hall, sum_const, card_erase_of_mem
        (mem_univ u), card_univ, Fintype.card_fin, smul_eq_mul] at hsum
      have hdu : G.degree u + 1 = d := by omega
      have hpos : 1 ≤ N := by
        have : 0 < d ^ g := pow_pos (by omega) g
        omega
      have : (N - 1) * d + d = 2 * (d ^ g * d) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos, hN]; ring
      generalize (N - 1) * d = A at hsum this
      generalize d ^ g * d = B at this
      omega
  -- a vertex outside both balls of radius `g - 1`
  have hball : (ball G u (g - 1) ∪ ball G v (g - 1)).card < N := by
    have h1 := card_ball_le G hG.1 (g - 1) u
    have h2 := card_ball_le G hG.1 (g - 1) v
    have h3 := ballBound_lt (by omega : 2 ≤ d) (g - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ g)] at h3
    have := card_union_le (ball G u (g - 1)) (ball G v (g - 1))
    omega
  obtain ⟨x, -, hxB⟩ : ∃ x ∈ (univ : Finset (Fin N)), x ∉ ball G u (g - 1) ∪ ball G v (g - 1) := by
    by_contra hall
    push Not at hall
    have := card_le_card (show univ ⊆ ball G u (g - 1) ∪ ball G v (g - 1) from
      fun z _ => hall z (mem_univ z))
    rw [card_univ, Fintype.card_fin] at this
    omega
  simp only [mem_union, not_or, ball, mem_filter, mem_univ, true_and, not_exists, not_le]
    at hxB
  obtain ⟨hxu, hxv⟩ := hxB
  have farx : ∀ c, (∀ p : G.Walk c x, g - 1 < p.length) → Far G g c x :=
    fun c h p => by have := h p; omega
  have fary : ∀ c y, G.Adj x y → (∀ p : G.Walk c x, g - 1 < p.length) → Far G g c y :=
    fun c y hxy h p => by
      have := h (p.concat hxy.symm)
      rw [Walk.length_concat] at this
      omega
  have hdx : G.degree x = d := claim u x hu (farx u hxu)
  obtain ⟨y, hy⟩ : (G.neighborFinset x).Nonempty := by
    rw [← card_pos, card_neighborFinset_eq_degree, hdx]; omega
  have hxy : G.Adj x y := (G.mem_neighborFinset _ _).mp hy
  obtain ⟨hgood, hlt⟩ := swapEdges_good hG hxy (farx u hxu) (farx v hxv) (fary v y hxy hxv)
    (fary u y hxy hxu) (by omega) (by convert hpair) (by omega)
  exact absurd (hmax _ hgood) (not_le.mpr hlt)

end BuyAtBulk.EdgeOnlyGap.ErdosSachs
