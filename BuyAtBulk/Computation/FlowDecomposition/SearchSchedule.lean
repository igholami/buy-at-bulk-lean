import BuyAtBulk.Computation.FlowDecomposition.SearchComplexity

/-! Instrumented directed search. The counter counts table entries inspected
by lookups and positive-arc extension scans. Walk-copy sizes are bounded in
SearchComplexity; these counters are not advertised as total bit operations. -/
namespace BuyAtBulk.Computation.FlowDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def lookupScheduled {source : V} : Table G source → (target : V) → Option (G.Walk source target) × ℕ
  | [], _ => (none, 0)
  | ⟨v, path⟩ :: rest, target =>
      if equal : v = target then (some (path.copy rfl equal), 1) else
        let recursive := lookupScheduled rest target
        (recursive.1, recursive.2 + 1)

def extendScheduled (flow : V → V → ℚ) {source : V} :
    Table G source → (target : V) → Option (G.Walk source target) × ℕ
  | [], _ => (none, 0)
  | ⟨v, path⟩ :: rest, target =>
      if edge : G.Adj v target then
        if 0 < flow v target then (some (path.concat edge), 1) else
          let recursive := extendScheduled flow rest target
          (recursive.1, recursive.2 + 1)
      else
        let recursive := extendScheduled flow rest target
        (recursive.1, recursive.2 + 1)

def nextScheduled (flow : V → V → ℚ) {source : V} (table : Table G source)
    (target : V) : Option (G.Walk source target) × ℕ :=
  let old := lookupScheduled G table target
  match old.1 with
  | some path => (some path, old.2)
  | none =>
      let fresh := extendScheduled G flow table target
      (fresh.1, old.2 + fresh.2)

def collectScheduled (flow : V → V → ℚ) {source : V} (table : Table G source) :
    List (V) → Table G source × ℕ
  | [] => ([], 0)
  | target :: rest =>
      let found := nextScheduled G flow table target
      let recursive := collectScheduled flow table rest
      (match found.1 with
        | none => recursive.1
        | some path => ⟨target, path⟩ :: recursive.1,
        found.2 + recursive.2)

def iterateScheduled (flow : V → V → ℚ) (source : V) : ℕ → Table G source × ℕ
  | 0 => ([⟨source, .nil⟩], 0)
  | rounds + 1 =>
      let previous := iterateScheduled flow source rounds
      let following := collectScheduled G flow previous.1 (vertices numbering)
      (following.1, previous.2 + following.2)

def positivePathScheduled (flow : V → V → ℚ) (source target : V) : Option (G.Path source target) × ℕ :=
  let table := iterateScheduled G numbering flow source n
  let found := lookupScheduled G table.1 target
  (found.1.map SimpleGraph.Walk.toPath, table.2 + found.2)

theorem lookupScheduled_value {source target : V} (table : Table G source) :
    (lookupScheduled G table target).1 = lookup G table target := by
  induction table with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨v, path⟩
    by_cases same : v = target <;> simp [lookupScheduled, lookup, same, ih]

theorem lookupScheduled_bound {source target : V} (table : Table G source) :
    (lookupScheduled G table target).2 ≤ table.length := by
  induction table with
  | nil => simp [lookupScheduled]
  | cons first rest ih =>
    rcases first with ⟨v, path⟩
    by_cases same : v = target
    · simp [lookupScheduled, same]
    · simpa [lookupScheduled, same, Nat.add_comm] using Nat.succ_le_succ ih

theorem extendScheduled_value (flow : V → V → ℚ) {source target : V} (table : Table G source) :
    (extendScheduled G flow table target).1 = extend G flow table target := by
  induction table with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨v, path⟩
    by_cases edge : G.Adj v target <;> by_cases pos : 0 < flow v target <;>
      simp [extendScheduled, extend, edge, pos, ih]

theorem extendScheduled_bound (flow : V → V → ℚ) {source target : V} (table : Table G source) :
    (extendScheduled G flow table target).2 ≤ table.length := by
  induction table with
  | nil => simp [extendScheduled]
  | cons first rest ih =>
    rcases first with ⟨v, path⟩
    by_cases edge : G.Adj v target <;> by_cases pos : 0 < flow v target
    · simp [extendScheduled, edge, pos]
    all_goals simpa [extendScheduled, edge, pos, Nat.add_comm] using Nat.succ_le_succ ih

theorem nextScheduled_value (flow : V → V → ℚ) {source target : V} (table : Table G source) :
    (nextScheduled G flow table target).1 = next G flow table target := by
  simp only [nextScheduled, lookupScheduled_value, next]
  cases lookup G table target <;> simp [extendScheduled_value]

theorem nextScheduled_bound (flow : V → V → ℚ) {source target : V} (table : Table G source) :
    (nextScheduled G flow table target).2 ≤ 2 * table.length := by
  have old := lookupScheduled_bound G (target := target) table
  have fresh := extendScheduled_bound G flow (target := target) table
  simp only [nextScheduled]
  split <;> dsimp only <;> omega

theorem collectScheduled_value (flow : V → V → ℚ) {source : V} (table : Table G source)
    (targets : List (V)) :
    (collectScheduled G flow table targets).1 =
      targets.filterMap (fun target => (next G flow table target).map fun path => ⟨target, path⟩) := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
    simp only [collectScheduled, List.filterMap_cons, ih, nextScheduled_value]
    cases next G flow table target <;> rfl

theorem collectScheduled_bound (flow : V → V → ℚ) {source : V} (table : Table G source)
    (targets : List (V)) :
    (collectScheduled G flow table targets).2 ≤ targets.length * (2 * table.length) := by
  induction targets with
  | nil => simp [collectScheduled]
  | cons target rest ih =>
    have current := nextScheduled_bound G flow (target := target) table
    simp only [collectScheduled, List.length_cons]
    nlinarith

theorem iterateScheduled_value (flow : V → V → ℚ) (source : V) (rounds : ℕ) :
    (iterateScheduled G numbering flow source rounds).1 = iterate G numbering flow source rounds := by
  induction rounds with
  | zero => rfl
  | succ k ih => simp only [iterateScheduled, collectScheduled_value, ih, iterate, step]

theorem iterateScheduled_bound (flow : V → V → ℚ) (source : V) (rounds : ℕ) :
    (iterateScheduled G numbering flow source rounds).2 ≤ 2 * rounds * n * n := by
  induction rounds with
  | zero => simp [iterateScheduled]
  | succ k ih =>
    have paid := collectScheduled_bound G flow (iterateScheduled G numbering flow source k).1 (vertices numbering)
    rw [vertices_length, iterateScheduled_value] at paid
    have entries := iterate_length G numbering flow source k
    have bounded := Nat.mul_le_mul_left (2 * n) entries
    simp only [iterateScheduled]
    rw [iterateScheduled_value]
    nlinarith

theorem positivePathScheduled_value (flow : V → V → ℚ) (source target : V) :
    (positivePathScheduled G numbering flow source target).1 = positivePath G numbering flow source target := by
  simp only [positivePathScheduled, lookupScheduled_value, iterateScheduled_value, positivePath]

theorem positivePathScheduled_bound (flow : V → V → ℚ) (source target : V) :
    (positivePathScheduled G numbering flow source target).2 ≤ 2 * n ^ 3 + n := by
  have rounds := iterateScheduled_bound G numbering flow source n
  have last := lookupScheduled_bound G (target := target) (iterateScheduled G numbering flow source n).1
  rw [iterateScheduled_value] at last
  have count := iterate_length G numbering flow source n
  simp only [positivePathScheduled, iterateScheduled_value]
  nlinarith

end BuyAtBulk.Computation.FlowDecomposition
