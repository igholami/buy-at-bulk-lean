import BuyAtBulk.Model.CompactFlowReachability
import Mathlib.Data.List.FinRange

/-! Executable directed positive-arc breadth expansion. Tables store actual
walks, not proofs of reachability or a function that recomputes earlier tables.
Each round materializes at most one entry for each vertex. -/
namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def vertices (numbering : V ≃ Fin n) : List V := (List.finRange n).map numbering.symm

@[simp] theorem vertices_length : (vertices numbering).length = n := by simp [vertices]

@[simp] theorem vertices_complete (v : V) : v ∈ vertices numbering := by
  exact List.mem_map.mpr ⟨numbering v, List.mem_finRange _, numbering.symm_apply_apply v⟩

theorem numbered_card (numbering : V ≃ Fin n) : Fintype.card V = n := by
  simpa only [Fintype.card_fin] using Fintype.card_congr numbering

abbrev Table (source : V) := List (Σ target, G.Walk source target)

def lookup {source : V} : Table G source → (target : V) → Option (G.Walk source target)
  | [], _ => none
  | ⟨v, path⟩ :: rest, target =>
      if equal : v = target then some (path.copy rfl equal) else lookup rest target

def extend (flow : V → V → ℚ) {source : V} :
    Table G source → (target : V) → Option (G.Walk source target)
  | [], _ => none
  | ⟨v, path⟩ :: rest, target =>
      if edge : G.Adj v target then
        if 0 < flow v target then some (path.concat edge) else extend flow rest target
      else extend flow rest target

def next (flow : V → V → ℚ) {source : V} (table : Table G source)
    (target : V) : Option (G.Walk source target) :=
  match lookup G table target with
  | some path => some path
  | none => extend G flow table target

def step (flow : V → V → ℚ) {source : V} (table : Table G source) : Table G source :=
  (vertices numbering).filterMap fun target => (next G flow table target).map fun path => ⟨target, path⟩

def iterate (flow : V → V → ℚ) (source : V) : ℕ → Table G source
  | 0 => [⟨source, .nil⟩]
  | rounds + 1 => step G numbering flow (iterate flow source rounds)

def positivePath (flow : V → V → ℚ) (source target : V) : Option (G.Path source target) :=
  (lookup G (iterate G numbering flow source n) target).map SimpleGraph.Walk.toPath

/-- Tables materialize one optional result per numbered vertex. -/
theorem step_length (flow : V → V → ℚ) {source : V} (table : Table G source) :
    (step G numbering flow table).length ≤ n := by
  exact (List.length_filterMap_le _ _).trans_eq (vertices_length numbering)

theorem lookup_exists_of_entry {source target : V} {table : Table G source}
    (member : ∃ path, (⟨target, path⟩ : Σ v, G.Walk source v) ∈ table) :
    ∃ path, lookup G table target = some path := by
  induction table with
  | nil => simpa using member
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases equal : v = target
    · exact ⟨first.copy rfl equal, by simp [lookup, equal]⟩
    · simp only [lookup, dif_neg equal]
      apply ih
      obtain ⟨path, member⟩ := member
      rcases List.mem_cons.mp member with same | member
      · exact False.elim (equal (congrArg Sigma.fst same).symm)
      · exact ⟨path, member⟩

theorem lookup_origin {source target : V} {table : Table G source}
    {path : G.Walk source target} (returned : lookup G table target = some path) :
    ∃ original, (⟨target, original⟩ : Σ v, G.Walk source v) ∈ table := by
  induction table with
  | nil => simp [lookup] at returned
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases equal : v = target
    · subst target
      exact ⟨first, by simp⟩
    · simp only [lookup, dif_neg equal] at returned
      obtain ⟨original, member⟩ := ih returned
      exact ⟨original, List.mem_cons_of_mem _ member⟩

theorem next_entry {source target : V} (flow : V → V → ℚ) (table : Table G source)
    {path : G.Walk source target} (returned : next G flow table target = some path) :
    (⟨target, path⟩ : Σ v, G.Walk source v) ∈ step G numbering flow table := by
  exact List.mem_filterMap.mpr ⟨target, vertices_complete numbering _, by simp [returned]⟩

theorem step_preserves {source target : V} (flow : V → V → ℚ) (table : Table G source)
    (found : ∃ path, lookup G table target = some path) :
    ∃ path, lookup G (step G numbering flow table) target = some path := by
  obtain ⟨path, returned⟩ := found
  apply lookup_exists_of_entry G
  exact ⟨path, next_entry G numbering flow table (by simp [next, returned])⟩

theorem extend_complete (flow : V → V → ℚ) {source target : V}
    (table : Table G source) (witness : ∃ v path,
      (⟨v, path⟩ : Σ u, G.Walk source u) ∈ table ∧ G.Adj v target ∧ 0 < flow v target) :
    ∃ path, extend G flow table target = some path := by
  induction table with
  | nil => simpa using witness
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases edge : G.Adj v target
    · by_cases positive : 0 < flow v target
      · exact ⟨first.concat edge, by simp [extend, edge, positive]⟩
      · simp only [extend, dif_pos edge, if_neg positive]
        apply ih
        obtain ⟨u, path, member, adj, pos⟩ := witness
        rcases List.mem_cons.mp member with same | member
        · have vertices : u = v := congrArg Sigma.fst same
          subst u
          exact False.elim (positive pos)
        · exact ⟨u, path, member, adj, pos⟩
    · simp only [extend, dif_neg edge]
      apply ih
      obtain ⟨u, path, member, adj, pos⟩ := witness
      rcases List.mem_cons.mp member with same | member
      · have vertices : u = v := congrArg Sigma.fst same
        subst u
        exact False.elim (edge adj)
      · exact ⟨u, path, member, adj, pos⟩

theorem step_extends (flow : V → V → ℚ) {source u target : V}
    (table : Table G source) (found : ∃ path, lookup G table u = some path)
    (edge : G.Adj u target) (positive : 0 < flow u target) :
    ∃ path, lookup G (step G numbering flow table) target = some path := by
  cases previous : lookup G table target with
  | some path => exact step_preserves G numbering flow table ⟨path, previous⟩
  | none =>
    obtain ⟨initialPath, prefix_found⟩ := found
    obtain ⟨original, member⟩ := lookup_origin G prefix_found
    obtain ⟨path, returned⟩ := extend_complete G flow table ⟨u, original, member, edge, positive⟩
    exact lookup_exists_of_entry G ⟨path, next_entry G numbering flow table (by simp [next, previous, returned])⟩

end BuyAtBulk.Computation.FlowDecomposition
