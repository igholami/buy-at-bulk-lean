import BuyAtBulk.Computation.Runtime.CoreRows

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational

@[simp] theorem neg_bits (q : ℚ) : (Code.ofRat (-q)).bits = (Code.ofRat q).bits := by
  simp [Code.ofRat, Code.bits]

theorem toll_bits (buying radius distance : ℚ) (B : ℕ)
    (buy_width : (Code.ofRat buying).bits ≤ B) (radius_width : (Code.ofRat radius).bits ≤ B)
    (distance_width : (Code.ofRat distance).bits ≤ B) :
    (Code.ofRat (toll buying radius distance).value).bits ≤ 10*B+24 := by
  have first := ratAdd_result_bits radius (-distance)
  have second := ratAdd_result_bits (radius + -distance) buying
  rw [neg_bits] at first
  have zero : (Code.ofRat 0).bits = 3 := by decide
  simp only [toll, Traced.bind_value, emit_value, ratAdd_value]
  split_ifs <;> omega

theorem toll_words (buying radius distance : ℚ) (B : ℕ)
    (buy_width : (Code.ofRat buying).bits ≤ B) (radius_width : (Code.ofRat radius).bits ≤ B)
    (distance_width : (Code.ofRat distance).bits ≤ B) :
    WordsWithin (12*B+40) (toll buying radius distance).events := by
  let K := 12*B+40
  have first_width : (Code.ofRat (radius + -distance)).bits ≤ 4*B+8 := by
    have actual := ratAdd_result_bits radius (-distance)
    rw [neg_bits] at actual
    omega
  have second_width : (Code.ofRat (radius + -distance + buying)).bits ≤ 10*B+24 := by
    have actual := ratAdd_result_bits (radius + -distance) buying
    omega
  have first : WordsWithin K (ratAdd radius (-distance)).events := by
    intro event member word present
    have actual := ratAdd_words radius (-distance) event member word present
    rw [neg_bits] at actual
    dsimp [K]; omega
  have second : WordsWithin K (ratAdd (radius + -distance) buying).events := by
    intro event member word present
    have actual := ratAdd_words (radius + -distance) buying event member word present
    dsimp [K]; omega
  have zero : (Code.ofRat 0).bits = 3 := by decide
  simp only [toll, Traced.bind_events, Traced.bind_value, emit_value, ratAdd_value, ratLe,
    wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true, neg_bits]
  split_ifs <;> dsimp [K] at * <;> (repeat' apply And.intro) <;> first | exact first | exact second | omega

theorem tollFromLabel_bits (buying radius : ℚ) (label : WithTop ℚ) (B : ℕ)
    (buy_width : (Code.ofRat buying).bits ≤ B) (radius_width : (Code.ofRat radius).bits ≤ B)
    (label_width : Runtime.ShortestPath.width label ≤ B) :
    (Code.ofRat (tollFromLabel buying radius label).value).bits ≤ 10*B+24 := by
  cases label with
  | top => simp [tollFromLabel, Code.ofRat, Code.bits]
  | coe distance =>
      exact toll_bits buying radius distance B buy_width radius_width (by
        change (Code.ofRat distance).bits+1 ≤ B at label_width; omega)

theorem tollFromLabel_words (buying radius : ℚ) (label : WithTop ℚ) (B : ℕ)
    (buy_width : (Code.ofRat buying).bits ≤ B) (radius_width : (Code.ofRat radius).bits ≤ B)
    (label_width : Runtime.ShortestPath.width label ≤ B) :
    WordsWithin (12*B+40) (tollFromLabel buying radius label).events := by
  cases label with
  | top => simp [tollFromLabel, WordsWithin, Code.ofRat, Code.bits]
  | coe distance =>
      have actual := toll_words buying radius distance B buy_width radius_width (by
        change (Code.ofRat distance).bits+1 ≤ B at label_width; omega)
      simpa only [tollFromLabel, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_singleton, forall_eq, and_true] using And.intro (by omega : 1 ≤ 12*B+40) actual

end BuyAtBulk.Computation.Runtime.StoredCore
