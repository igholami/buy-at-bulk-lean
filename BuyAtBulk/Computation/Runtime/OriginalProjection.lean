import BuyAtBulk.Computation.Runtime.OriginalCompression

/-! Instrumented length, last-edge removal, and full typed projection. The
single-pass last-edge removal refines the model's length/take implementation. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def walkLength {u v : Vertex tables.graphData} : (graph tables.graphData).Walk u v → Traced ℕ
  | .nil => ⟨0, [⟨.branch, [1]⟩, ⟨.write, [0]⟩]⟩
  | .cons _ tail =>
    let next := walkLength tail
    ⟨next.value + 1, [⟨Operation.branch, [1]⟩] ++ next.events ++
      [⟨.natAdd, [next.value.size, 1]⟩, ⟨.write, [(next.value + 1).size]⟩]⟩

@[simp] theorem walkLength_value {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    (walkLength tables walk).value = walk.length := by induction walk <;> simp_all [walkLength]

theorem walkLength_count {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    (walkLength tables walk).events.length = 3 * walk.length + 2 := by
  induction walk <;> simp_all [walkLength] <;> omega

private theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

theorem walkLength_words {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v)
    (K : ℕ) (dimension : walk.length + 2 ≤ K) : WordsWithin K (walkLength tables walk).events := by
  have one : 1 ≤ K := by omega
  induction walk with
  | nil => simp [walkLength, WordsWithin]; omega
  | cons edge tail ih =>
    have head : (tail.length + 1).size ≤ K := (size_le_self _).trans (by simp only [SimpleGraph.Walk.length_cons] at dimension; omega)
    have previous : tail.length.size ≤ K := (size_le_self _).trans (by simp only [SimpleGraph.Walk.length_cons] at dimension; omega)
    have tailwords := ih (by simp only [SimpleGraph.Walk.length_cons] at dimension; omega)
    simp_all [walkLength, wordsWithin_append, wordsWithin_cons]

def compress {u v : Fin n}
    (walk : (graph tables.graphData).Walk (.original u) (.original v)) (simple : walk.IsPath) :
    Traced (tables.graphData.graph.Walk u v) :=
  let length := walkLength tables walk
  let result := compressFuel tables length.value walk simple (by rw [walkLength_value])
  ⟨result.value, length.events ++ result.events⟩

@[simp] theorem compress_value {u v : Fin n}
    (walk : (graph tables.graphData).Walk (.original u) (.original v)) (simple : walk.IsPath) :
    (compress tables walk simple).value = (compressPath tables.graphData walk simple).val := by
  simp only [compress, compressFuel_value, walkLength_value, compressPath]

theorem compress_count {u v : Fin n}
    (walk : (graph tables.graphData).Walk (.original u) (.original v)) (simple : walk.IsPath) :
    (compress tables walk simple).events.length ≤ 12 * walk.length + 5 := by
  have inner := compressFuel_count tables walk.length walk simple (le_rfl)
  simp only [compress, List.length_append, walkLength_count, walkLength_value]
  omega

theorem compress_words {u v : Fin n}
    (walk : (graph tables.graphData).Walk (.original u) (.original v)) (simple : walk.IsPath)
    (K : ℕ) (dimension : n + requests + walk.length + 5 ≤ K) :
    WordsWithin K (compress tables walk simple).events := by
  have length := walkLength_words tables walk K (by omega)
  have result := compressFuel_words tables walk.length walk simple (le_rfl) K (by omega)
  simpa only [compress, walkLength_value, wordsWithin_append] using And.intro length result

private def vertexWords (vertex : Vertex tables.graphData) : List ℕ :=
  [(label tables vertex).1.size, (label tables vertex).2.1.size, (label tables vertex).2.2.size]

def dropLast {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    Traced ((graph tables.graphData).Walk u walk.penultimate) :=
  match walk with
  | .nil => ⟨.nil, [⟨.branch, [1]⟩, ⟨.path, vertexWords tables u⟩]⟩
  | .cons first tail =>
    match tail with
    | .nil => ⟨.nil, [⟨.branch, [1]⟩, ⟨.branch, [1]⟩, ⟨.path, vertexWords tables u⟩]⟩
    | .cons second rest =>
      let next := dropLast (.cons second rest)
      ⟨.cons first next.value,
        [⟨Operation.branch, [1]⟩, ⟨.branch, [1]⟩] ++ next.events ++ [⟨.cons, vertexWords tables u⟩]⟩
termination_by walk.length

theorem dropLast_value {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    (dropLast tables walk).value = walk.dropLast := by
  induction walk with
  | nil => simp [dropLast]
  | cons edge tail ih =>
    cases tail with
    | nil => simp [dropLast]
    | cons second rest =>
      rw [dropLast]
      dsimp only
      rw [ih]
      rfl

theorem dropLast_count {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    (dropLast tables walk).events.length ≤ 3 * walk.length + 2 := by
  induction walk with
  | nil => simp [dropLast]
  | cons edge tail ih =>
    cases tail with
    | nil => simp [dropLast]
    | cons second rest =>
      rw [dropLast]
      dsimp only
      simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons] at ih ⊢
      omega

theorem dropLast_words {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v)
    (K : ℕ) (dimension : n + requests + 3 ≤ K) : WordsWithin K (dropLast tables walk).events := by
  have one : 1 ≤ K := by omega
  induction walk with
  | @nil u =>
    have head := label_widths tables u K dimension
    simp [dropLast, vertexWords, wordsWithin_cons, head, one]
  | @cons u x v edge tail ih =>
    have head := label_widths tables u K dimension
    cases tail with
    | nil => simp [dropLast, vertexWords, wordsWithin_cons, head, one]
    | cons second rest =>
      rw [dropLast]
      dsimp only
      simp_all [vertexWords, wordsWithin_append, wordsWithin_cons]

def project (i : Fin requests)
    (path : (graph tables.graphData).Path (.leaf i false) (.leaf i true)) :
    Traced (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  classical
  rcases path with ⟨walk, simple⟩
  cases walk with
  | @cons _ next _ first tail =>
    have next_eq : next = Vertex.original (tables.graphData.source i) :=
      (leaf_neighbor_iff tables.graphData i false next).mp first
    subst next
    have nonnil : ¬ tail.Nil := SimpleGraph.Walk.not_nil_of_ne (by intro same; cases same)
    have last_eq : tail.penultimate = Vertex.original (tables.graphData.target i) :=
      (leaf_neighbor_iff tables.graphData i true tail.penultimate).mp (tail.adj_penultimate nonnil).symm
    let removed := dropLast tables tail
    let interior := removed.value.copy rfl last_eq
    have simple_interior : interior.IsPath := by
      apply SimpleGraph.Walk.IsPath.mk'
      simpa only [interior, removed, SimpleGraph.Walk.support_copy, dropLast_value] using simple.of_cons.dropLast.support_nodup
    let compressed := compress tables interior simple_interior
    have simple_result : compressed.value.IsPath := by
      rw [show compressed.value = (compressPath tables.graphData interior simple_interior).val from compress_value tables interior simple_interior]
      exact (compressPath tables.graphData interior simple_interior).property.1
    exact ⟨⟨compressed.value, simple_result⟩,
      [⟨Operation.branch, [1]⟩, ⟨.read, [i.val.size]⟩] ++ removed.events ++ compressed.events⟩

theorem project_value (i : Fin requests)
    (path : (graph tables.graphData).Path (.leaf i false) (.leaf i true)) :
    (project tables i path).value = projectPath tables.graphData i path := by
  rcases path with ⟨walk, simple⟩
  cases walk with
  | @cons _ next _ first tail =>
    have next_eq : next = Vertex.original (tables.graphData.source i) :=
      (leaf_neighbor_iff tables.graphData i false next).mp first
    subst next
    apply Subtype.ext
    simp only [project, projectPath, projectWalk, compress_value, dropLast_value]

theorem project_count (i : Fin requests)
    (path : (graph tables.graphData).Path (.leaf i false) (.leaf i true)) :
    (project tables i path).events.length ≤ 15 * path.val.length + 10 := by
  rcases path with ⟨walk, simple⟩
  cases walk with
  | @cons _ next _ first tail =>
    have next_eq : next = Vertex.original (tables.graphData.source i) :=
      (leaf_neighbor_iff tables.graphData i false next).mp first
    subst next
    have nonnil : ¬ tail.Nil := SimpleGraph.Walk.not_nil_of_ne (by intro same; cases same)
    have last_eq : tail.penultimate = Vertex.original (tables.graphData.target i) :=
      (leaf_neighbor_iff tables.graphData i true tail.penultimate).mp (tail.adj_penultimate nonnil).symm
    let interior := (dropLast tables tail).value.copy rfl last_eq
    have simple_interior : interior.IsPath := by
      apply SimpleGraph.Walk.IsPath.mk'
      simpa only [interior, SimpleGraph.Walk.support_copy, dropLast_value] using simple.of_cons.dropLast.support_nodup
    have interior_length : interior.length ≤ tail.length := by
      simp only [interior, SimpleGraph.Walk.length_copy, dropLast_value, SimpleGraph.Walk.length_dropLast]
      omega
    have dropped := dropLast_count tables tail
    have compressed := compress_count tables interior simple_interior
    change ([(⟨Operation.branch, [1]⟩ : Event), ⟨.read, [i.val.size]⟩] ++
      (dropLast tables tail).events ++ (compress tables interior simple_interior).events).length ≤ _
    simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons]
    omega

theorem project_words (i : Fin requests)
    (path : (graph tables.graphData).Path (.leaf i false) (.leaf i true))
    (K : ℕ) (dimension : n + requests + path.val.length + 6 ≤ K) :
    WordsWithin K (project tables i path).events := by
  rcases path with ⟨walk, simple⟩
  cases walk with
  | @cons _ next _ first tail =>
    have next_eq : next = Vertex.original (tables.graphData.source i) :=
      (leaf_neighbor_iff tables.graphData i false next).mp first
    subst next
    have nonnil : ¬ tail.Nil := SimpleGraph.Walk.not_nil_of_ne (by intro same; cases same)
    have last_eq : tail.penultimate = Vertex.original (tables.graphData.target i) :=
      (leaf_neighbor_iff tables.graphData i true tail.penultimate).mp (tail.adj_penultimate nonnil).symm
    let interior := (dropLast tables tail).value.copy rfl last_eq
    have simple_interior : interior.IsPath := by
      apply SimpleGraph.Walk.IsPath.mk'
      simpa only [interior, SimpleGraph.Walk.support_copy, dropLast_value] using simple.of_cons.dropLast.support_nodup
    have interior_length : interior.length ≤ tail.length := by
      simp only [interior, SimpleGraph.Walk.length_copy, dropLast_value, SimpleGraph.Walk.length_dropLast]
      omega
    have dropped := dropLast_words tables tail K (by simp only [SimpleGraph.Walk.length_cons] at dimension; omega)
    have compressed := compress_words tables interior simple_interior K (by
      simp only [SimpleGraph.Walk.length_cons] at dimension
      omega)
    have index : i.val.size ≤ K := (size_le_self _).trans (by have := i.isLt; omega)
    have one : 1 ≤ K := by simp only [SimpleGraph.Walk.length_cons] at dimension; omega
    change WordsWithin K ([⟨Operation.branch, [1]⟩, ⟨.read, [i.val.size]⟩] ++
      (dropLast tables tail).events ++ (compress tables interior simple_interior).events)
    simp_all only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, true_and]

end BuyAtBulk.Computation.Runtime.Original
