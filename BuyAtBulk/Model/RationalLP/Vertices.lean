import BuyAtBulk.Model.RationalLP.Boundary

/-! Every feasible point of a rational LP bounded by the unit cube is dominated
by a vertex. Termination uses strictly increasing active constraint sets. -/
noncomputable section
namespace BuyAtBulk.RationalLP.Problem
variable {J C : Type} [Fintype J] [Fintype C] (P : Problem J C)

private theorem vertex_domination_aux (cube : P.InUnitCube) (k : ℕ) :
    ∀ x : J → ℚ, P.Feasible x → Fintype.card C - (P.active x).card = k →
      ∃ y : J → ℚ, P.Feasible y ∧ P.Vertex y ∧ P.objective y ≤ P.objective x := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hx hcount
    by_cases vertex : P.Vertex x
    · exact ⟨x, hx, vertex, le_rfl⟩
    obtain ⟨d, dne, hdir, hobj⟩ := P.improving_direction x vertex
    obtain ⟨y, hy, hyobj, hactive⟩ := P.boundary_step cube x d hx dne hdir hobj
    have hcard := Finset.card_lt_card hactive
    have hbound : (P.active y).card ≤ Fintype.card C := Finset.card_le_univ _
    have hlt : Fintype.card C - (P.active y).card < k := by omega
    obtain ⟨z, hz, hvertex, hzobj⟩ := ih _ hlt y hy rfl
    exact ⟨z, hz, hvertex, hzobj.trans hyobj⟩

/-- A rational vertex with no greater objective exists above every feasible
input point; no real-to-rational approximation is involved. -/
theorem vertex_domination (cube : P.InUnitCube) (x : J → ℚ) (hx : P.Feasible x) :
    ∃ y : J → ℚ, P.Feasible y ∧ P.Vertex y ∧ P.objective y ≤ P.objective x :=
  P.vertex_domination_aux cube (Fintype.card C - (P.active x).card) x hx rfl

omit [Fintype J] in
/-- Distinct vertices have different active constraint sets. -/
theorem vertex_active_injective :
    Function.Injective (fun x : {x : J → ℚ // P.Feasible x ∧ P.Vertex x} => P.active x.val) := by
  classical
  intro x y heq
  change P.active x.val = P.active y.val at heq
  apply Subtype.ext
  apply y.property.2 x.val
  intro i hi
  rw [← heq] at hi
  exact (Finset.mem_filter.mp hi).2

/-- A nonempty rational LP with unit-cube bounded feasible set attains its exact
minimum at a rational vertex. Finiteness comes from active constraint subsets. -/
theorem minimum_attained (cube : P.InUnitCube) (feasible : ∃ x, P.Feasible x) :
    P.HasMinimum := by
  classical
  let T := {x : J → ℚ // P.Feasible x ∧ P.Vertex x}
  let finiteT : Finite T := Finite.of_injective _ P.vertex_active_injective
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨x, hx⟩ := feasible
  obtain ⟨v, hv, hvvertex, _⟩ := P.vertex_domination cube x hx
  let Tnonempty : Nonempty T := ⟨⟨v, hv, hvvertex⟩⟩
  obtain ⟨z, _, hzmin⟩ := (Finset.univ : Finset T).exists_min_image
    (fun y => P.objective y.val) Finset.univ_nonempty
  refine ⟨z.val, z.property.1, ?_⟩
  intro y hy
  obtain ⟨v, hv, hvvertex, hvobj⟩ := P.vertex_domination cube y hy
  exact (hzmin ⟨v, hv, hvvertex⟩ (Finset.mem_univ _)).trans hvobj

end BuyAtBulk.RationalLP.Problem
