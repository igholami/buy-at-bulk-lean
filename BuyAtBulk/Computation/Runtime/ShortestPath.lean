import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.ShortestPath.Encoding
import BuyAtBulk.Computation.HelperExpressions

/-! Instrumented dense relaxation. Each event is generated where its actual
operand is consumed. Counts include reads, branch tests, writes and scan
control, not only successful edge relaxations. Recovery is separate. -/
namespace BuyAtBulk.Computation.Runtime.ShortestPath
open BuyAtBulk.Computation.ShortestPath
open Rational
variable {n : ℕ}

def width : WithTop ℚ → ℕ
  | ⊤ => 1
  | (q : ℚ) => (Code.ofRat q).bits + 1

def read (old : Vector (WithTop ℚ) n) (v : Fin n) : Traced (WithTop ℚ) :=
  emit .read [v.val.size, width old[v.val]] old[v.val]

def minimum (a b : WithTop ℚ) : Traced (WithTop ℚ) :=
  emit .ratCompare [width a, width b] (min a b)

def addition (a : ℚ) (b : WithTop ℚ) : Traced (WithTop ℚ) :=
  match b with
  | ⊤ => emit .branch [1] ⊤
  | (q : ℚ) =>
      let result := ratAdd a q
      ⟨(result.value : WithTop ℚ), ⟨.branch, [1]⟩ :: result.events⟩

@[simp] theorem addition_value (a : ℚ) (b : WithTop ℚ) :
    (addition a b).value = (a : WithTop ℚ) + b := by
  cases b <;> simp [addition]

theorem addition_count (a : ℚ) (b : WithTop ℚ) : (addition a b).events.length ≤ 3 := by
  cases b <;> simp [addition]

def candidate (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v u : Fin n) : Traced (WithTop ℚ) :=
  let adjacent := input.adjacency[v.val][u.val]
  let control : List Event := [⟨.read, [v.val.size, u.val.size, 1]⟩, ⟨.branch, [1]⟩]
  if adjacent then
    let operand := read old u
    let result := addition weights[v.val] operand.value
    ⟨result.value, control ++ [⟨.read, [v.val.size, (Code.ofRat weights[v.val]).bits]⟩] ++ operand.events ++ result.events⟩
  else ⟨⊤, control⟩

@[simp] theorem candidate_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v u : Fin n) :
    (candidate input weights old v u).value =
      BuyAtBulk.Computation.ShortestPath.candidate input.graph (fun x => weights[x.val]) old v u := by
  unfold candidate BuyAtBulk.Computation.ShortestPath.candidate GraphEncoding.graph
  cases h : input.adjacency[v.val][u.val] <;> simp [h, read]

theorem candidate_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v u : Fin n) :
    (candidate input weights old v u).events.length ≤ 7 := by
  have bound := addition_count weights[v.val] (read old u).value
  unfold candidate
  dsimp only
  split <;> simp_all [read] <;> omega

def scan (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) : List (Fin n) → Traced (WithTop ℚ)
  | [] =>
      let result := read old v
      ⟨result.value, ⟨.branch, [1]⟩ :: result.events⟩
  | u :: rest =>
      let tail := scan input weights old v rest
      let next := candidate input weights old v u
      let result := minimum next.value tail.value
      ⟨result.value, [⟨.branch, [1]⟩, ⟨.scan, [u.val.size]⟩] ++
        tail.events ++ next.events ++ result.events⟩

theorem scan_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (vertices : List (Fin n)) :
    (scan input weights old v vertices).value =
      (countedScan input.graph (fun x => weights[x.val]) old v vertices).1 := by
  induction vertices with
  | nil => rfl
  | cons u rest ih => simp [scan, countedScan, minimum, ih]

theorem scan_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (vertices : List (Fin n)) :
    (scan input weights old v vertices).events.length ≤ 10 * vertices.length + 2 := by
  induction vertices with
  | nil => simp [scan, read]
  | cons u rest ih =>
      have bound := candidate_count input weights old v u
      simp only [scan, List.length_append, List.length_cons, List.length_nil, minimum, emit,
        List.length_cons, List.length_nil]
      omega

def step (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) : Traced (Vector (WithTop ℚ) n) :=
  let rows := Vector.ofFn fun v => scan input weights old v (List.finRange n)
  ⟨rows.map Traced.value,
    ⟨.write, [n.size]⟩ :: (List.finRange n).flatMap (fun v =>
      [⟨.scan, [v.val.size]⟩] ++ (rows[v.val]).events ++
      [⟨.write, [v.val.size, width (rows[v.val]).value]⟩])⟩

theorem step_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) :
    (step input weights old).value =
      BuyAtBulk.Computation.ShortestPath.step input.graph (fun x => weights[x.val]) old := by
  apply Vector.ext
  intro i hi
  simp only [step, Vector.getElem_map, Vector.getElem_ofFn, scan_value, countedScan_value]
  simp [BuyAtBulk.Computation.ShortestPath.step]

theorem step_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) :
    (step input weights old).events.length ≤ n * (10 * n + 4) + 1 := by
  have per (v : Fin n) :
      ([⟨Operation.scan, [v.val.size]⟩] ++
        (scan input weights old v (List.finRange n)).events ++
        [⟨Operation.write, [v.val.size, width (scan input weights old v (List.finRange n)).value]⟩] : List Event).length ≤ 10 * n + 4 := by
    have bound := scan_count input weights old v (List.finRange n)
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_finRange] at *
    omega
  simp only [step, List.length_cons, List.length_flatMap, Vector.getElem_ofFn]
  have sum_bound : ((List.finRange n).map fun v =>
      ([⟨Operation.scan, [v.val.size]⟩] ++
        (scan input weights old v (List.finRange n)).events ++
        [⟨Operation.write, [v.val.size, width (scan input weights old v (List.finRange n)).value]⟩] : List Event).length).sum ≤
      n * (10 * n + 4) := by
    calc
      _ ≤ ((List.finRange n).map fun _ => 10 * n + 4).sum := by
        apply List.sum_le_sum
        intro v member
        exact per v
      _ = _ := by simp
  simpa only [Fin.eta] using Nat.add_le_add_right sum_bound 1

def initialCell (weights : Vector ℚ n) (target v : Fin n) : Traced (WithTop ℚ) :=
  if v = target then
    ⟨(weights[target.val] : WithTop ℚ),
      [⟨.scan, [v.val.size]⟩, ⟨.branch, [v.val.size, target.val.size]⟩,
       ⟨.read, [target.val.size, (Code.ofRat weights[target.val]).bits]⟩,
       ⟨.write, [v.val.size, (Code.ofRat weights[target.val]).bits]⟩]⟩
  else ⟨⊤, [⟨.scan, [v.val.size]⟩, ⟨.branch, [v.val.size, target.val.size]⟩,
    ⟨.write, [v.val.size, 1]⟩]⟩

def initial (weights : Vector ℚ n) (target : Fin n) : Traced (Vector (WithTop ℚ) n) :=
  ⟨Vector.ofFn fun v => (initialCell weights target v).value,
    ⟨.write, [n.size]⟩ :: (List.finRange n).flatMap (fun v => (initialCell weights target v).events)⟩

theorem initial_value (weights : Vector ℚ n) (target : Fin n) :
    (initial weights target).value = BuyAtBulk.Computation.ShortestPath.initial (fun v => weights[v.val]) target := by
  apply Vector.ext
  intro i hi
  simp only [initial, BuyAtBulk.Computation.ShortestPath.initial, Vector.getElem_ofFn]
  unfold initialCell
  split <;> rfl

theorem initial_count (weights : Vector ℚ n) (target : Fin n) :
    (initial weights target).events.length ≤ 4 * n + 1 := by
  have per (v : Fin n) : (initialCell weights target v).events.length ≤ 4 := by
    unfold initialCell
    split <;> simp
  simp only [initial, List.length_cons, List.length_flatMap]
  have bound : ((List.finRange n).map fun v => (initialCell weights target v).events.length).sum ≤ 4 * n := by
    calc
      _ ≤ ((List.finRange n).map fun _ => 4).sum := List.sum_le_sum (fun v _ => per v)
      _ = _ := by simp [Nat.mul_comm]
  omega

def iterate (input : GraphEncoding n) (weights : Vector ℚ n) (target : Fin n) :
    ℕ → Traced (Vector (WithTop ℚ) n)
  | 0 =>
      let result := initial weights target
      ⟨result.value, ⟨.recurse, [1]⟩ :: result.events⟩
  | rounds + 1 =>
      let previous := iterate input weights target rounds
      let next := step input weights previous.value
      ⟨next.value, ⟨.recurse, [rounds.size]⟩ :: previous.events ++ next.events⟩

theorem iterate_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds : ℕ) :
    (iterate input weights target rounds).value =
      BuyAtBulk.Computation.ShortestPath.iterate input.graph (fun v => weights[v.val]) target rounds := by
  induction rounds with
  | zero => exact initial_value weights target
  | succ k ih => simp only [iterate, step_value, ih, BuyAtBulk.Computation.ShortestPath.iterate]

theorem iterate_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds : ℕ) :
    (iterate input weights target rounds).events.length ≤
      rounds * (n * (10 * n + 4) + 2) + 4 * n + 2 := by
  induction rounds with
  | zero =>
      have bound := initial_count weights target
      simp only [iterate, List.length_cons]
      omega
  | succ k ih =>
      have bound := step_count input weights (iterate input weights target k).value
      simp only [iterate, List.length_cons, List.length_append]
      nlinarith

/-- Traversal metadata is a sum over actual vertex visits, including the
last endpoint. This lemma does not replace a walk by its simple-path support. -/
theorem traversalCost_list (G : SimpleGraph (Fin n)) (weights : Vector ℚ n)
    {u v : Fin n} (walk : G.Walk u v) :
    traversalCost G (fun x => weights[x.val]) walk = (walk.support.map fun x => weights[x.val]).sum := by
  induction walk with
  | nil => simp [traversalCost]
  | cons edge tail ih => simp [traversalCost, ih]

/-- Every finite round label is an actual walk sum with at most rounds+1
summands. The resulting width is linear in rounds, rather than a recursively
reapplied doubling bound for rational addition. No nonnegativity is needed. -/
theorem iterate_label_width (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds : ℕ) (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L) (v : Fin n) :
    width (BuyAtBulk.Computation.ShortestPath.iterate input.graph
      (fun x => weights[x.val]) target rounds)[v.val] ≤
        2 * (2 * (rounds + 1) + 1) * L + 3 := by
  let table := BuyAtBulk.Computation.ShortestPath.iterate input.graph (fun x => weights[x.val]) target rounds
  cases value : table[v.val] with
  | top => simp only [value, width]; omega
  | coe q =>
      have finite : table[v.val] ≠ ⊤ := by rw [value]; exact WithTop.coe_ne_top
      obtain ⟨walk, returned⟩ := recover_exists input.graph (fun x => weights[x.val]) target rounds v finite
      obtain ⟨cost, length⟩ := recover_valid input.graph (fun x => weights[x.val]) target rounds v walk returned
      have same : traversalCost input.graph (fun x => weights[x.val]) walk = q :=
        WithTop.coe_injective (cost.trans value)
      have bounds := HelperExpressions.sum_rat_bits (walk.support.map fun x => weights[x.val]) L constant (by
        intro q member
        obtain ⟨u, member, rfl⟩ := List.mem_map.mp member
        exact inputs u)
      rw [← traversalCost_list, same] at bounds
      have size : (walk.support.map fun x => weights[x.val]).length ≤ rounds + 1 := by
        simp only [List.length_map, SimpleGraph.Walk.length_support]
        omega
      change (Code.ofRat q).bits + 1 ≤ _
      nlinarith

theorem addition_words (a : ℚ) (b : WithTop ℚ) (L B K : ℕ)
    (left : (Code.ofRat a).bits ≤ L) (right : width b ≤ B)
    (one : 1 ≤ K) (budget : 2 * (L + B) + 8 ≤ K) :
    WordsWithin K (addition a b).events := by
  cases b with
  | top => simp [addition, emit, WordsWithin, one]
  | coe q =>
      have qbound : (Code.ofRat q).bits ≤ B := by simpa only [width] using Nat.le_trans (Nat.le_add_right _ 1) right
      have arithmetic : WordsWithin K (ratAdd a q).events := by
        intro event member word present
        exact (ratAdd_words a q event member word present).trans (by omega)
      simpa only [addition, wordsWithin_cons, List.mem_singleton, forall_eq, and_true] using And.intro one arithmetic

theorem minimum_words (a b : WithTop ℚ) (K : ℕ) (left : width a ≤ K) (right : width b ≤ K) :
    WordsWithin K (minimum a b).events := by
  simpa [minimum, emit, WordsWithin] using And.intro left right

theorem scan_width (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (vertices : List (Fin n)) (B K : ℕ)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B)
    (candidates : ∀ u : Fin n, width (candidate input weights old v u).value ≤ K)
    (old_le : B ≤ K) : width (scan input weights old v vertices).value ≤ K := by
  induction vertices with
  | nil => exact (old_width v).trans old_le
  | cons u rest ih =>
      change width (min _ _) ≤ K
      by_cases order : (candidate input weights old v u).value ≤ (scan input weights old v rest).value
      · rw [min_eq_left order]; exact candidates u
      · rw [min_eq_right (le_of_not_ge order)]; exact ih

theorem addition_width (a : ℚ) (b : WithTop ℚ) (L B : ℕ)
    (left : (Code.ofRat a).bits ≤ L) (right : width b ≤ B) :
    width (addition a b).value ≤ 2 * (L + B) + 9 := by
  cases b with
  | top => simp [addition, emit, width]
  | coe q =>
      have raw := Code.bounded_bits (Code.add_bounded
        (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat q)))
      have normalized : (Code.ofRat (a + q)).bits ≤ ((Code.ofRat a).add (Code.ofRat q)).bits := by
        simpa using Code.normalized_bits_le ((Code.ofRat a).add (Code.ofRat q))
      simp only [addition, ratAdd_value, width] at *
      nlinarith

theorem candidate_width (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v u : Fin n) (L B : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B) :
    width (candidate input weights old v u).value ≤ 2 * (L + B) + 9 := by
  have bound := addition_width weights[v.val] old[u.val] L B (inputs v) (old_width u)
  unfold candidate
  dsimp only
  split
  · exact bound
  · simp only [width]; omega

theorem candidate_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v u : Fin n) (L B K : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B)
    (indices : n ≤ K) (budget : 2 * (L + B) + 9 ≤ K) :
    WordsWithin K (candidate input weights old v u).events := by
  have ui : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt u.isLt |>.trans indices)
  have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
  have arithmetic := addition_words weights[v.val] old[u.val] L B K (inputs v) (old_width u) (by omega) (by omega)
  unfold candidate
  dsimp only
  split
  · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
    simp only [read, emit] at *
    simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    have wi : (Code.ofRat weights[v.val]).bits ≤ K := (inputs v).trans (by omega)
    have oi : width old[u.val] ≤ K := (old_width u).trans (by omega)
    have one : 1 ≤ K := by omega
    aesop
  · simp [WordsWithin, ui, vi, show 1 ≤ K by omega]

theorem scan_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (vertices : List (Fin n)) (L B K : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B)
    (indices : n ≤ K) (budget : 2 * (L + B) + 9 ≤ K) :
    WordsWithin K (scan input weights old v vertices).events := by
  have one : 1 ≤ K := by omega
  have old_le : B ≤ K := by omega
  have candidate_bounds (u : Fin n) : width (candidate input weights old v u).value ≤ K :=
    (candidate_width input weights old v u L B inputs old_width).trans budget
  induction vertices with
  | nil =>
      have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
      have stored := (old_width v).trans old_le
      simpa [scan, read, emit, WordsWithin] using And.intro one (And.intro vi stored)
  | cons u rest ih =>
      have ui : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt u.isLt |>.trans indices)
      have next := candidate_words input weights old v u L B K inputs old_width indices budget
      have tail := scan_width input weights old v rest B K old_width candidate_bounds old_le
      have compared := minimum_words (candidate input weights old v u).value
        (scan input weights old v rest).value K (candidate_bounds u) tail
      simp only [scan, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop

theorem step_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (L B K : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B)
    (indices : n ≤ K) (budget : 2 * (L + B) + 9 ≤ K) :
    WordsWithin K (step input weights old).events := by
  have old_le : B ≤ K := by omega
  apply (wordsWithin_cons K _ _).mpr
  constructor
  · simpa only [List.mem_singleton, forall_eq] using
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  · intro event member word present
    obtain ⟨v, member, event_mem⟩ := List.mem_flatMap.mp member
    have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
    have scanned := scan_words input weights old v (List.finRange n) L B K inputs old_width indices budget
    have result_width := scan_width input weights old v (List.finRange n) B K old_width
      (fun u => (candidate_width input weights old v u L B inputs old_width).trans budget) old_le
    have row : WordsWithin K ([⟨Operation.scan, [v.val.size]⟩] ++
        (scan input weights old v (List.finRange n)).events ++
        [⟨Operation.write, [v.val.size, width (scan input weights old v (List.finRange n)).value]⟩]) := by
      simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
      exact ⟨⟨vi, scanned⟩, vi, result_width⟩
    exact row event (by simpa only [Vector.getElem_ofFn, Fin.eta] using event_mem) word present

theorem initial_words (weights : Vector ℚ n) (target : Fin n) (L K : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (indices : n ≤ K) (budget : L ≤ K) (one : 1 ≤ K) :
    WordsWithin K (initial weights target).events := by
  apply (wordsWithin_cons K _ _).mpr
  constructor
  · simpa only [List.mem_singleton, forall_eq] using
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  · intro event member word present
    obtain ⟨v, member, event_mem⟩ := List.mem_flatMap.mp member
    have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
    have ti : target.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt target.isLt |>.trans indices)
    have stored := (inputs target).trans budget
    have cell : WordsWithin K (initialCell weights target v).events := by
      unfold initialCell
      split <;> simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop
    exact cell event event_mem word present

def labelBudget (rounds L : ℕ) : ℕ := 2 * (2 * (rounds + 1) + 1) * L + 3

/-- All words in all arithmetic, scanning, control and storage events of the
actual relaxation trace obey one polynomial bound. -/
theorem iterate_words_upto (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (R L K : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L)
    (indices : n ≤ K) (depth : R ≤ K)
    (budget : 2 * (L + labelBudget R L) + 9 ≤ K) :
    ∀ rounds ≤ R, WordsWithin K (iterate input weights target rounds).events := by
  intro rounds
  induction rounds with
  | zero =>
      intro _
      have base := initial_words weights target L K
        (fun u => (Nat.le_add_right _ 1).trans (inputs u)) indices (by omega) (by omega)
      simpa only [iterate, wordsWithin_cons, List.mem_singleton, forall_eq] using And.intro (by omega : 1 ≤ K) base
  | succ k ih =>
      intro bounded
      have previous := ih (by omega)
      have old_width (u : Fin n) : width (iterate input weights target k).value[u.val] ≤ labelBudget R L := by
        rw [iterate_value]
        have width_bound := iterate_label_width input weights target k L constant inputs u
        unfold labelBudget
        nlinarith
      have next := step_words input weights (iterate input weights target k).value L (labelBudget R L) K
        (fun u => (Nat.le_add_right _ 1).trans (inputs u)) old_width indices budget
      have ki : k.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : k ≤ K)
      simpa only [iterate, wordsWithin_cons, wordsWithin_append, List.mem_singleton, forall_eq] using
        And.intro (And.intro ki previous) next

theorem iterate_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L) :
    WordsWithin (2 * (L + labelBudget rounds L) + 9 + n + rounds)
      (iterate input weights target rounds).events := by
  apply iterate_words_upto input weights target rounds L _ constant inputs (by omega) (by omega) (by omega) rounds le_rfl

end BuyAtBulk.Computation.Runtime.ShortestPath
