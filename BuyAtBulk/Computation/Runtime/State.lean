import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.Attachment.Primitives

/-! Runtime purchases use Boolean cells. Finset decoding appears only in the
semantic refinement, never as a chosen representative of a quotient. -/
namespace BuyAtBulk.Computation.Runtime.StoredState
open BuyAtBulk.UpperBound
variable {n : ℕ} (G : SimpleGraph (Fin n))

structure State where
  bought : Vector Bool n
  centers : List (CenterRecord (Fin n))
  edges : List (AuxiliaryEdge G)

def boughtSet (flags : Vector Bool n) : Finset (Fin n) :=
  ((List.finRange n).filter fun v => flags[v.val]).toFinset

@[simp] theorem mem_boughtSet (flags : Vector Bool n) (v : Fin n) :
    v ∈ boughtSet flags ↔ flags[v.val] = true := by simp [boughtSet]

def decode (state : State G) : RoundingState G :=
  ⟨boughtSet state.bought, state.centers, state.edges⟩

def markCell (flags : Vector Bool n) (u v : Fin n) : Traced Bool :=
  if u = v then
    ⟨true, [⟨.scan, [v.val.size]⟩, ⟨.branch, [u.val.size, v.val.size]⟩, ⟨.write, [v.val.size, 1]⟩]⟩
  else
    ⟨flags[v.val], [⟨.scan, [v.val.size]⟩, ⟨.branch, [u.val.size, v.val.size]⟩,
      ⟨.read, [v.val.size, 1]⟩, ⟨.write, [v.val.size, 1]⟩]⟩

def mark (state : State G) (u : Fin n) : Traced (State G) :=
  let cells := Vector.ofFn fun v => markCell state.bought u v
  ⟨{state with bought := cells.map Traced.value},
    ⟨.write, [n.size]⟩ :: (List.finRange n).flatMap (fun v => (cells[v.val]).events)⟩

@[simp] theorem mark_flag (state : State G) (u v : Fin n) :
    (mark G state u).value.bought[v.val] = if u = v then true else state.bought[v.val] := by
  simp only [mark, Vector.getElem_map, Vector.getElem_ofFn]
  unfold markCell
  split <;> rfl

theorem mark_count (state : State G) (u : Fin n) : (mark G state u).events.length ≤ 4 * n + 1 := by
  have per (v : Fin n) : (markCell state.bought u v).events.length ≤ 4 := by
    unfold markCell
    split <;> simp
  simp only [mark, List.length_cons, List.length_flatMap, Vector.getElem_ofFn]
  have bound : ((List.finRange n).map fun v => (markCell state.bought u v).events.length).sum ≤ 4 * n := by
    calc
      _ ≤ ((List.finRange n).map fun _ => 4).sum := List.sum_le_sum (fun v _ => per v)
      _ = _ := by simp [Nat.mul_comm]
  simpa only [Fin.eta] using Nat.add_le_add_right bound 1

theorem decode_mark (state : State G) (u : Fin n) :
    decode G (mark G state u).value =
      {decode G state with bought := insert u (decode G state).bought} := by
  have bought : boughtSet (mark G state u).value.bought = insert u (boughtSet state.bought) := by
    ext v
    simp only [mem_boughtSet, mark_flag, Finset.mem_insert]
    by_cases same : u = v
    · subst v; simp
    · simp [same, Ne.symm same]
  cases state
  simp only [decode, mark] at *
  congr

def buyWalk (state : State G) {u v : Fin n} : G.Walk u v → Traced (State G)
  | .nil =>
      let result := mark G state u
      ⟨result.value, ⟨.branch, [1]⟩ :: result.events⟩
  | .cons _ tail =>
      let first := mark G state u
      let rest := buyWalk first.value tail
      ⟨rest.value, ⟨.branch, [1]⟩ :: first.events ++ rest.events⟩

theorem buyWalk_count (state : State G) {u v : Fin n} (walk : G.Walk u v) :
    (buyWalk G state walk).events.length ≤ (walk.length + 1) * (4 * n + 2) := by
  induction walk generalizing state with
  | @nil a =>
      have bound := mark_count G state a
      simp only [buyWalk, List.length_cons, SimpleGraph.Walk.length_nil]
      omega
  | @cons a b c edge tail ih =>
      have first := mark_count G state a
      have rest := ih (mark G state a).value
      simp only [buyWalk, List.length_cons, List.length_append, SimpleGraph.Walk.length_cons]
      nlinarith

theorem decode_buyWalk (state : State G) {u v : Fin n} (walk : G.Walk u v) :
    decode G (buyWalk G state walk).value =
      {decode G state with bought := (decode G state).bought ∪ walk.support.toFinset} := by
  induction walk generalizing state with
  | @nil a =>
      simpa only [buyWalk, SimpleGraph.Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
        Finset.union_insert, Finset.union_empty] using decode_mark G state a
  | @cons a b c edge tail ih =>
      simpa only [buyWalk, ih, decode_mark, SimpleGraph.Walk.support_cons, List.toFinset_cons,
        Finset.insert_union, Finset.union_insert] using ih (mark G state a).value

private theorem index_width (v : Fin n) : v.val.size ≤ n :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt)

theorem mark_words (state : State G) (u : Fin n) (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (mark G state u).events := by
  apply (wordsWithin_cons K _ _).mpr
  constructor
  · simpa only [List.mem_singleton, forall_eq] using (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  · intro event member word present
    obtain ⟨v, _, membership⟩ := List.mem_flatMap.mp member
    have ui := (index_width u).trans indices
    have vi := (index_width v).trans indices
    have cell : WordsWithin K (markCell state.bought u v).events := by
      unfold markCell
      split <;> simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop
    exact cell event (by simpa only [Vector.getElem_ofFn, Fin.eta] using membership) word present

theorem buyWalk_words (state : State G) {u v : Fin n} (walk : G.Walk u v)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (buyWalk G state walk).events := by
  induction walk generalizing state with
  | @nil a =>
      have marked := mark_words G state a K indices one
      simpa only [buyWalk, wordsWithin_cons, List.mem_singleton, forall_eq] using And.intro one marked
  | @cons a b c edge tail ih =>
      have marked := mark_words G state a K indices one
      have recursive := ih (mark G state a).value
      simpa only [buyWalk, wordsWithin_append, wordsWithin_cons, List.mem_singleton, forall_eq] using
        And.intro (And.intro one marked) recursive

def purchase (state : State G) {u v : Fin n} (path : G.Path u v) : Traced (State G) :=
  buyWalk G state path.val

theorem decode_purchase (state : State G) {u v : Fin n} (path : G.Path u v) :
    decode G (purchase G state path).value = Attachment.purchase G (decode G state) path :=
  decode_buyWalk G state path.val

theorem purchase_count (state : State G) {u v : Fin n} (path : G.Path u v) :
    (purchase G state path).events.length ≤ (n + 1) * (4 * n + 2) := by
  have bound := buyWalk_count G state path.val
  have length : path.val.length ≤ n := by simpa using Nat.le_of_lt path.property.length_lt
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right length 1))

def recordBirth (state : State G) (v : Fin n) (scale : ℚ) : Traced (State G) :=
  ⟨{state with centers := ⟨v, scale⟩ :: state.centers},
    [⟨.cons, [v.val.size, (Rational.Code.ofRat scale).bits]⟩]⟩

def recordEdge (state : State G) {u v : Fin n} (path : G.Path u v) (scale : ℚ) : Traced (State G) :=
  ⟨{state with edges := ⟨u, v, scale, path⟩ :: state.edges},
    [⟨.cons, [u.val.size, v.val.size, (Rational.Code.ofRat scale).bits]⟩]⟩

@[simp] theorem decode_recordBirth (state : State G) (v : Fin n) (scale : ℚ) :
    decode G (recordBirth G state v scale).value = UpperBound.recordBirth G (decode G state) v scale := rfl

@[simp] theorem decode_recordEdge (state : State G) {u v : Fin n} (path : G.Path u v) (scale : ℚ) :
    decode G (recordEdge G state path scale).value = UpperBound.recordEdge G (decode G state) path scale := rfl

@[simp] theorem purchase_centers (state : State G) {u v : Fin n} (path : G.Path u v) :
    (purchase G state path).value.centers = state.centers := by
  have equality := congrArg (fun s : RoundingState G => s.centers) (decode_purchase G state path)
  simpa only [decode, Attachment.purchase] using equality

@[simp] theorem purchase_edges (state : State G) {u v : Fin n} (path : G.Path u v) :
    (purchase G state path).value.edges = state.edges := by
  have equality := congrArg (fun s : RoundingState G => s.edges) (decode_purchase G state path)
  simpa only [decode, Attachment.purchase] using equality

end BuyAtBulk.Computation.Runtime.StoredState
