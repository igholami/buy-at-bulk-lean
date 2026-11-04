import BuyAtBulk.Computation.Runtime.Weights
import BuyAtBulk.Computation.Attachment.CenterSearch

namespace BuyAtBulk.Computation.Runtime.AttachmentQueries
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def boughtRoute (physical : Vector ℚ n) (state : StoredState.State input.graph)
    (source target : Fin n) (threshold : ℚ) : Traced (Option (input.graph.Path source target)) :=
  let weights := Weights.bought physical state threshold
  let result := Queries.shortRoute input weights.value source target threshold
  ⟨result.value, weights.events ++ result.events⟩

theorem boughtRoute_value (physical : Vector ℚ n) (state : StoredState.State input.graph)
    (source target : Fin n) (threshold : ℚ) :
    (boughtRoute input physical state source target threshold).value =
      Attachment.boughtRoute input.graph (Equiv.refl _) (fun v => physical[v.val])
        (StoredState.decode input.graph state) source target threshold := by
  have weights : (fun v => (Weights.bought physical state threshold).value[v.val]) =
      Attachment.boughtWeight input.graph (fun v => physical[v.val]) (StoredState.decode input.graph state) threshold :=
    funext (Weights.bought_get physical state threshold)
  simpa only [boughtRoute, Attachment.boughtRoute, weights] using
    Queries.shortRoute_value input (Weights.bought physical state threshold).value source target threshold

theorem boughtRoute_count (physical : Vector ℚ n) (state : StoredState.State input.graph)
    (source target : Fin n) (threshold : ℚ) :
    (boughtRoute input physical state source target threshold).events.length ≤
      (n + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 36) + 3 * n ^ 2 + 20 * n + 15 := by
  have weights := Weights.bought_count physical state threshold
  have queried := Queries.shortRoute_count input (Weights.bought physical state threshold).value source target threshold
  simp only [boughtRoute, List.length_append]
  omega

def nearRecord (weights : Vector ℚ n) (scale : ℚ) (z : Fin n) :
    List (CenterRecord (Fin n)) → Traced (Option (Σ v, input.graph.Path z v))
  | [] => ⟨none, [⟨.branch, [1]⟩]⟩
  | record :: rest =>
      let eligible := ratLe scale record.birthScale
      let control := [⟨Operation.branch, [1]⟩, ⟨.scan, [record.endpoint.val.size]⟩,
        ⟨.read, [(Code.ofRat record.birthScale).bits]⟩] ++ eligible.events ++ [⟨.branch, [1]⟩]
      if eligible.value then
        let threshold := ratDiv scale 8
        let route := Queries.shortRoute input weights z record.endpoint threshold.value
        let entryTrace := control ++ [⟨.read, [record.endpoint.val.size]⟩] ++ threshold.events ++ route.events ++ [⟨.branch, [1]⟩]
        match route.value with
        | some path => ⟨some ⟨record.endpoint, path⟩, entryTrace ++ [⟨.cons, [record.endpoint.val.size]⟩]⟩
        | none =>
            let recursive := nearRecord weights scale z rest
            ⟨recursive.value, entryTrace ++ recursive.events⟩
      else
        let recursive := nearRecord weights scale z rest
        ⟨recursive.value, control ++ recursive.events⟩

theorem nearRecord_value (weights : Vector ℚ n) (scale : ℚ) (z : Fin n) (records : List (CenterRecord (Fin n))) :
    (nearRecord input weights scale z records).value =
      Attachment.nearRecord input.graph (Equiv.refl _) (fun v => weights[v.val]) scale z records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [nearRecord, Attachment.nearRecord, ratDiv_value]
      by_cases high : scale ≤ record.birthScale
      · simp only [ratLe, emit_value, high, decide_true, ite_true]
        rw [← Queries.shortRoute_value]
        cases returned : (Queries.shortRoute input weights z record.endpoint (scale / 8)).value <;>
          simp [returned, ih]
      · simp [ratLe, emit_value, high, ih]

def routeBudget (n : ℕ) : ℕ :=
  (n + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 36) + 3 * n ^ 2 + 8 * n + 14

theorem nearRecord_count (weights : Vector ℚ n) (scale : ℚ) (z : Fin n) (records : List (CenterRecord (Fin n))) :
    (nearRecord input weights scale z records).events.length ≤ records.length * (routeBudget n + 10) + 1 := by
  induction records with
  | nil => simp [nearRecord]
  | cons record rest ih =>
      have query : (Queries.shortRoute input weights z record.endpoint (ratDiv scale 8).value).events.length ≤ routeBudget n :=
        Queries.shortRoute_count input weights z record.endpoint _
      simp only [nearRecord]
      split
      · split <;> simp only [List.length_append, List.length_cons, List.length_nil,
          ratLe, emit, ratDiv_length, Nat.add_mul, Nat.one_mul] <;> omega
      · simp only [List.length_append, List.length_cons, List.length_nil,
          ratLe, emit, Nat.add_mul, Nat.one_mul]
        omega

theorem boughtRoute_words (physical : Vector ℚ n) (state : StoredState.State input.graph)
    (source target : Fin n) (threshold : ℚ) (L : ℕ) (constant : 5 ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L) :
    WordsWithin (2 * ((10 * L + 25) + Runtime.ShortestPath.labelBudget n (10 * L + 25)) + 9 + n + n + L + 1)
      (boughtRoute input physical state source target threshold).events := by
  let weights := Weights.bought physical state threshold
  let K := 2 * ((10 * L + 25) + Runtime.ShortestPath.labelBudget n (10 * L + 25)) + 9 + n + n + L + 1
  have width (v : Fin n) : (Code.ofRat weights.value[v.val]).bits + 1 ≤ 10 * L + 25 := by
    have actual := Weights.boughtCell_bits physical state threshold v L constant physical_width threshold_width
    simpa only [weights, Weights.bought, Weights.materialize_get] using Nat.add_le_add_right actual 1
  have construction := (Weights.bought_words physical state threshold L constant physical_width threshold_width).mono
    (show 10 * L + 24 + n ≤ K by dsimp [K]; omega)
  have query := Queries.shortRoute_words input weights.value source target threshold (10 * L + 25) L (by omega) width threshold_width
  simpa only [boughtRoute, wordsWithin_append] using And.intro construction query

theorem nearRecord_words (weights : Vector ℚ n) (scale : ℚ) (z : Fin n) (records : List (CenterRecord (Fin n)))
    (L M : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L)
    (scale_width : (Code.ofRat scale).bits ≤ M)
    (birth_width : ∀ record ∈ records, (Code.ofRat record.birthScale).bits ≤ M) :
    WordsWithin (2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n + (2 * M + 22) + 1)
      (nearRecord input weights scale z records).events := by
  let K := 2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n + (2 * M + 22) + 1
  have one : 1 ≤ K := by dsimp [K]; omega
  have scalar : M ≤ K := by dsimp [K]; omega
  have indices (v : Fin n) : v.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (show v.val ≤ K by dsimp [K]; omega)
  have literal : (Code.ofRat 8).bits = 7 := by decide
  have threshold_width : (Code.ofRat (scale / 8)).bits ≤ 2 * M + 22 := by
    have arithmetic := ratDiv_result_bits scale 8
    omega
  have division : WordsWithin K (ratDiv scale 8).events := by
    intro event member word present
    exact (ratDiv_words scale 8 event member word present).trans (by dsimp [K]; omega)
  revert birth_width
  induction records with
  | nil => intro _; simp [nearRecord, WordsWithin, one]
  | cons record rest ih =>
      intro birth_width
      have birth := (birth_width record List.mem_cons_self).trans scalar
      have scale_bound := scale_width.trans scalar
      have endpoint := indices record.endpoint
      have recursive := ih (fun r member => birth_width r (List.mem_cons_of_mem _ member))
      have query := Queries.shortRoute_words input weights z record.endpoint (scale / 8) L (2 * M + 22) constant inputs threshold_width
      have comparison : WordsWithin K (ratLe scale record.birthScale).events := by
        simpa [ratLe, emit, WordsWithin] using And.intro scale_bound birth
      simp only [nearRecord]
      split
      · split <;> simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratDiv_value,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop
      · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop

end BuyAtBulk.Computation.Runtime.AttachmentQueries
