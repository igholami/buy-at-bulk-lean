import BuyAtBulk.Computation.Runtime.State
import BuyAtBulk.Computation.Runtime.RouteQuery

/-! The numerical query weights are computed into stored vectors. Every
coefficient read and arithmetic operation is part of the returned trace. -/
namespace BuyAtBulk.Computation.Runtime.Weights
open Rational
variable {n : ℕ} {G : SimpleGraph (Fin n)}

def materialize {α : Type} (f : Fin n → Traced α) (width : α → ℕ) : Traced (Vector α n) :=
  let cells := Vector.ofFn f
  ⟨cells.map Traced.value,
    ⟨.write, [n.size]⟩ :: (List.finRange n).flatMap (fun v =>
      [⟨.scan, [v.val.size]⟩] ++ (cells[v.val]).events ++
      [⟨.write, [v.val.size, width (cells[v.val]).value]⟩])⟩

@[simp] theorem materialize_get {α : Type} (f : Fin n → Traced α) (width : α → ℕ) (v : Fin n) :
    (materialize f width).value[v.val] = (f v).value := by simp [materialize]

theorem materialize_count {α : Type} (f : Fin n → Traced α) (width : α → ℕ) (C : ℕ)
    (bounds : ∀ v, (f v).events.length ≤ C) :
    (materialize f width).events.length ≤ n * (C + 2) + 1 := by
  have per (v : Fin n) :
      ([⟨Operation.scan, [v.val.size]⟩] ++ (f v).events ++
        [⟨Operation.write, [v.val.size, width (f v).value]⟩] : List Event).length ≤ C + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    have bound := bounds v
    omega
  simp only [materialize, List.length_cons, List.length_flatMap, Vector.getElem_ofFn]
  have sum : ((List.finRange n).map fun v =>
      ([⟨Operation.scan, [v.val.size]⟩] ++ (f v).events ++
        [⟨Operation.write, [v.val.size, width (f v).value]⟩] : List Event).length).sum ≤ n * (C + 2) := by
    calc
      _ ≤ ((List.finRange n).map fun _ => C + 2).sum := List.sum_le_sum (fun v _ => per v)
      _ = _ := by simp
  simpa only [Fin.eta] using Nat.add_le_add_right sum 1

theorem materialize_words {α : Type} (f : Fin n → Traced α) (width : α → ℕ) (K : ℕ)
    (indices : n ≤ K) (bounds : ∀ v, WordsWithin K (f v).events)
    (values : ∀ v, width (f v).value ≤ K) :
    WordsWithin K (materialize f width).events := by
  apply (wordsWithin_cons K _ _).mpr
  constructor
  · simpa only [List.mem_singleton, forall_eq] using (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  · intro event member word present
    obtain ⟨v, _, membership⟩ := List.mem_flatMap.mp member
    have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
    have row : WordsWithin K ([⟨Operation.scan, [v.val.size]⟩] ++ (f v).events ++
        [⟨Operation.write, [v.val.size, width (f v).value]⟩]) := by
      simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      exact ⟨⟨vi, bounds v⟩, vi, values v⟩
    exact row event (by simpa only [Vector.getElem_ofFn, Fin.eta] using membership) word present

def mixedCell (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (v : Fin n) : Traced ℚ :=
  let residual := if state.bought[v.val] then 0 else buying[v.val]
  let quotient := ratDiv scale allowance
  let product := ratMul quotient.value physical[v.val]
  let result := ratAdd residual product.value
  ⟨result.value,
    [⟨.read, [v.val.size, 1]⟩, ⟨.branch, [1]⟩] ++
    (if state.bought[v.val] then [] else [⟨.read, [v.val.size, (Code.ofRat buying[v.val]).bits]⟩]) ++
    [⟨.read, [(Code.ofRat scale).bits]⟩, ⟨.read, [(Code.ofRat allowance).bits]⟩] ++ quotient.events ++
    [⟨.read, [v.val.size, (Code.ofRat physical[v.val]).bits]⟩] ++ product.events ++ result.events⟩

@[simp] theorem mixedCell_value (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (v : Fin n) :
    (mixedCell buying physical state allowance scale v).value =
      Attachment.mixedWeight G (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode G state) allowance scale v := by
  simp only [mixedCell, ratDiv_value, ratMul_value, ratAdd_value,
    Attachment.mixedWeight, StoredState.decode, StoredState.mem_boughtSet]

theorem mixedCell_count (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (v : Fin n) :
    (mixedCell buying physical state allowance scale v).events.length ≤ 12 := by
  simp only [mixedCell, List.length_append, List.length_cons, List.length_nil,
    ratDiv_length, ratMul_length, ratAdd_length]
  split <;> simp

def mixed (buying physical : Vector ℚ n) (state : StoredState.State G) (allowance scale : ℚ) :
    Traced (Vector ℚ n) := materialize (mixedCell buying physical state allowance scale) (fun q => (Code.ofRat q).bits)

theorem mixed_count (buying physical : Vector ℚ n) (state : StoredState.State G) (allowance scale : ℚ) :
    (mixed buying physical state allowance scale).events.length ≤ 14 * n + 1 := by
  simpa only [mixed, Nat.mul_comm] using materialize_count
    (mixedCell buying physical state allowance scale) (fun q => (Code.ofRat q).bits) 12
    (mixedCell_count buying physical state allowance scale)

theorem mixedCell_bits (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (v : Fin n) (L : ℕ) (constant : 5 ≤ L)
    (buying_width : ∀ u : Fin n, (Code.ofRat buying[u.val]).bits ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (allowance_width : (Code.ofRat allowance).bits ≤ L) (scale_width : (Code.ofRat scale).bits ≤ L) :
    (Code.ofRat (mixedCell buying physical state allowance scale v).value).bits ≤ 22 * L + 56 := by
  have residual : (Code.ofRat (if state.bought[v.val] then 0 else buying[v.val])).bits ≤ L := by
    split
    · have zero : (Code.ofRat 0).bits = 3 := by decide
      omega
    · exact buying_width v
  have quotient := ratDiv_result_bits scale allowance
  have product := ratMul_result_bits (scale / allowance) physical[v.val]
  have result := ratAdd_result_bits (if state.bought[v.val] then 0 else buying[v.val]) ((scale / allowance) * physical[v.val])
  simp only [mixedCell, ratDiv_value, ratMul_value, ratAdd_value]
  have physical := physical_width v
  omega

theorem mixedCell_words (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (v : Fin n) (L : ℕ) (constant : 5 ≤ L)
    (buying_width : ∀ u : Fin n, (Code.ofRat buying[u.val]).bits ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (allowance_width : (Code.ofRat allowance).bits ≤ L) (scale_width : (Code.ofRat scale).bits ≤ L) :
    WordsWithin (22 * L + 56 + n) (mixedCell buying physical state allowance scale v).events := by
  let K := 22 * L + 56 + n
  have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [K]; omega : v.val ≤ K)
  have one : 1 ≤ K := by dsimp [K]; omega
  have residual : (Code.ofRat (if state.bought[v.val] then 0 else buying[v.val])).bits ≤ L := by
    split
    · have zero : (Code.ofRat 0).bits = 3 := by decide
      omega
    · exact buying_width v
  have quotient_bits : (Code.ofRat (scale / allowance)).bits ≤ 4 * L + 8 := by
    have actual := ratDiv_result_bits scale allowance
    omega
  have product_bits : (Code.ofRat ((scale / allowance) * physical[v.val])).bits ≤ 10 * L + 24 := by
    have actual := ratMul_result_bits (scale / allowance) physical[v.val]
    have leaf := physical_width v
    omega
  have quotient : WordsWithin K (ratDiv scale allowance).events := by
    intro event member word present
    exact (ratDiv_words scale allowance event member word present).trans (by dsimp [K]; omega)
  have product : WordsWithin K (ratMul (scale / allowance) physical[v.val]).events := by
    intro event member word present
    have leaf := physical_width v
    exact (ratMul_words _ _ event member word present).trans (by dsimp [K]; omega)
  have result : WordsWithin K (ratAdd (if state.bought[v.val] then 0 else buying[v.val])
      ((scale / allowance) * physical[v.val])).events := by
    intro event member word present
    exact (ratAdd_words _ _ event member word present).trans (by dsimp [K]; omega)
  have bw := (buying_width v).trans (show L ≤ K by dsimp [K]; omega)
  have pw := (physical_width v).trans (show L ≤ K by dsimp [K]; omega)
  have aw := allowance_width.trans (show L ≤ K by dsimp [K]; omega)
  have sw := scale_width.trans (show L ≤ K by dsimp [K]; omega)
  simp only [mixedCell, ratDiv_value, ratMul_value, ratAdd_value, wordsWithin_append, wordsWithin_cons,
    wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  cases flag : state.bought[v.val] <;> simp only [flag, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at * <;> aesop

theorem mixed_words (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (L : ℕ) (constant : 5 ≤ L)
    (buying_width : ∀ u : Fin n, (Code.ofRat buying[u.val]).bits ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (allowance_width : (Code.ofRat allowance).bits ≤ L) (scale_width : (Code.ofRat scale).bits ≤ L) :
    WordsWithin (22 * L + 56 + n) (mixed buying physical state allowance scale).events := by
  apply materialize_words
  · omega
  · intro v
    exact mixedCell_words buying physical state allowance scale v L constant buying_width physical_width allowance_width scale_width
  · intro v
    exact (mixedCell_bits buying physical state allowance scale v L constant buying_width physical_width allowance_width scale_width).trans (by omega)

def positivePart (threshold : ℚ) : Traced ℚ :=
  let test := ratLe threshold 0
  ⟨if test.value then 0 else threshold,
    [⟨.read, [(Code.ofRat threshold).bits]⟩] ++ test.events ++ [⟨.branch, [1]⟩]⟩

@[simp] theorem positivePart_value (threshold : ℚ) : (positivePart threshold).value = max threshold 0 := by
  by_cases nonpos : threshold ≤ 0
  · simp [positivePart, ratLe, emit, nonpos, max_eq_right nonpos]
  · simp [positivePart, ratLe, emit, nonpos, max_eq_left (le_of_not_ge nonpos)]

@[simp] theorem positivePart_count (threshold : ℚ) : (positivePart threshold).events.length = 3 := rfl

def boughtCell (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ) (v : Fin n) : Traced ℚ :=
  let maximum := positivePart threshold
  let penalty := ratAdd maximum.value 1
  let surcharge := if state.bought[v.val] then 0 else penalty.value
  let result := ratAdd physical[v.val] surcharge
  ⟨result.value,
    [⟨.read, [v.val.size, 1]⟩, ⟨.branch, [1]⟩] ++ maximum.events ++ penalty.events ++
    [⟨.read, [v.val.size, (Code.ofRat physical[v.val]).bits]⟩] ++ result.events⟩

@[simp] theorem boughtCell_value (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ) (v : Fin n) :
    (boughtCell physical state threshold v).value =
      Attachment.boughtWeight G (fun v => physical[v.val]) (StoredState.decode G state) threshold v := by
  simp only [boughtCell, ratAdd_value, positivePart_value,
    Attachment.boughtWeight, StoredState.decode, StoredState.mem_boughtSet]

@[simp] theorem boughtCell_count (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ) (v : Fin n) :
    (boughtCell physical state threshold v).events.length = 10 := by
  simp only [boughtCell, List.length_append, List.length_cons, List.length_nil, positivePart_count, ratAdd_length]

def bought (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ) : Traced (Vector ℚ n) :=
  materialize (boughtCell physical state threshold) (fun q => (Code.ofRat q).bits)

theorem bought_count (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ) :
    (bought physical state threshold).events.length ≤ 12 * n + 1 := by
  simpa only [bought, Nat.mul_comm] using materialize_count
    (boughtCell physical state threshold) (fun q => (Code.ofRat q).bits) 10
    (fun v => (boughtCell_count physical state threshold v).le)

theorem boughtCell_bits (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ)
    (v : Fin n) (L : ℕ) (constant : 5 ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L) :
    (Code.ofRat (boughtCell physical state threshold v).value).bits ≤ 10 * L + 24 := by
  have maximum : (Code.ofRat (max threshold 0)).bits ≤ L := by
    rcases le_total threshold 0 with h | h
    · rw [max_eq_right h]
      have zero : (Code.ofRat 0).bits = 3 := by decide
      omega
    · rw [max_eq_left h]; exact threshold_width
  have one : (Code.ofRat 1).bits = 4 := by decide
  have penalty := ratAdd_result_bits (max threshold 0) 1
  have surcharge : (Code.ofRat (if state.bought[v.val] then 0 else max threshold 0 + 1)).bits ≤ 4 * L + 8 := by
    split
    · have zero : (Code.ofRat 0).bits = 3 := by decide
      omega
    · omega
  have result := ratAdd_result_bits physical[v.val] (if state.bought[v.val] then 0 else max threshold 0 + 1)
  simp only [boughtCell, ratAdd_value, positivePart_value]
  have physical := physical_width v
  omega

theorem positivePart_words (threshold : ℚ) (L K : ℕ) (constant : 5 ≤ L)
    (input_width : (Code.ofRat threshold).bits ≤ L) (budget : L ≤ K) :
    WordsWithin K (positivePart threshold).events := by
  have zero : (Code.ofRat 0).bits = 3 := by decide
  have stored := input_width.trans budget
  have one : 1 ≤ K := by omega
  have z : (Code.ofRat 0).bits ≤ K := by omega
  simp [positivePart, ratLe, emit, WordsWithin, stored, one, z]

theorem boughtCell_words (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ)
    (v : Fin n) (L : ℕ) (constant : 5 ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L) :
    WordsWithin (10 * L + 24 + n) (boughtCell physical state threshold v).events := by
  let K := 10 * L + 24 + n
  have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [K]; omega : v.val ≤ K)
  have one : 1 ≤ K := by dsimp [K]; omega
  have maximum : (Code.ofRat (max threshold 0)).bits ≤ L := by
    rcases le_total threshold 0 with h | h
    · rw [max_eq_right h]
      have zero : (Code.ofRat 0).bits = 3 := by decide
      omega
    · rw [max_eq_left h]; exact threshold_width
  have literal : (Code.ofRat 1).bits = 4 := by decide
  have penalty_bits : (Code.ofRat (max threshold 0 + 1)).bits ≤ 4 * L + 8 := by
    have actual := ratAdd_result_bits (max threshold 0) 1
    omega
  have surcharge : (Code.ofRat (if state.bought[v.val] then 0 else max threshold 0 + 1)).bits ≤ 4 * L + 8 := by
    split
    · have zero : (Code.ofRat 0).bits = 3 := by decide
      omega
    · exact penalty_bits
  have maximized := positivePart_words threshold L K constant threshold_width (by dsimp [K]; omega)
  have penalty : WordsWithin K (ratAdd (max threshold 0) 1).events := by
    intro event member word present
    exact (ratAdd_words _ _ event member word present).trans (by dsimp [K]; omega)
  have result : WordsWithin K (ratAdd physical[v.val]
      (if state.bought[v.val] then 0 else max threshold 0 + 1)).events := by
    intro event member word present
    have leaf := physical_width v
    exact (ratAdd_words _ _ event member word present).trans (by dsimp [K]; omega)
  have pw := (physical_width v).trans (show L ≤ K by dsimp [K]; omega)
  simp only [boughtCell, ratAdd_value, positivePart_value, wordsWithin_append, wordsWithin_cons,
    wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  aesop

theorem bought_words (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ)
    (L : ℕ) (constant : 5 ≤ L)
    (physical_width : ∀ u : Fin n, (Code.ofRat physical[u.val]).bits ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L) :
    WordsWithin (10 * L + 24 + n) (bought physical state threshold).events := by
  apply materialize_words
  · omega
  · intro v
    exact boughtCell_words physical state threshold v L constant physical_width threshold_width
  · intro v
    exact (boughtCell_bits physical state threshold v L constant physical_width threshold_width).trans (by omega)

@[simp] theorem mixed_get (buying physical : Vector ℚ n) (state : StoredState.State G)
    (allowance scale : ℚ) (v : Fin n) :
    (mixed buying physical state allowance scale).value[v.val] =
      Attachment.mixedWeight G (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode G state) allowance scale v := by
  simp [mixed]

@[simp] theorem bought_get (physical : Vector ℚ n) (state : StoredState.State G) (threshold : ℚ) (v : Fin n) :
    (bought physical state threshold).value[v.val] =
      Attachment.boughtWeight G (fun v => physical[v.val]) (StoredState.decode G state) threshold v := by
  simp [bought]

end BuyAtBulk.Computation.Runtime.Weights
