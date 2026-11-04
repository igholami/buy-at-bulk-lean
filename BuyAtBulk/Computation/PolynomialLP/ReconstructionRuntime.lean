import BuyAtBulk.Computation.PolynomialLP.RationalReconstruction
import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.Rational.Expression

/-! Concrete rational-native continued-fraction runtime. Floors use an actual
integer-division instruction on stored normalized components, not a real-floor
oracle. Partial convergent words are bounded using linear expression trees. -/
namespace BuyAtBulk.PolynomialLP.ReconstructionRuntime
open Computation.Rational Computation.Runtime

theorem tail_num_le (q : ℚ) : (continuedTail q).num.natAbs ≤ q.den := by
  by_cases zero : Int.fract q = 0
  · simp [continuedTail,zero]
  · simp only [continuedTail_num q zero,Int.natAbs_natCast,le_refl]

theorem tail_den_le (q : ℚ) : (continuedTail q).den ≤ q.den := by
  by_cases zero : Int.fract q = 0
  · simp only [continuedTail,zero,inv_zero,Rat.den_zero]
    exact q.den_pos
  · exact (continuedTail_den_lt q zero).le

theorem tail_bounded (q : ℚ) (B : ℕ) (input : (Code.ofRat q).Bounded B) :
    (Code.ofRat (continuedTail q)).Bounded B := by
  have den : q.den < 2^B := by simpa only [Code.ofRat,Int.natAbs_natCast] using input.2
  exact ⟨(tail_num_le q).trans_lt den,by simpa only [Code.ofRat,Int.natAbs_natCast] using (tail_den_le q).trans_lt den⟩

theorem floor_abs (q : ℚ) : (⌊q⌋ : ℤ).natAbs ≤ q.num.natAbs := by
  rw [Rat.floor_def']
  exact Int.natAbs_ediv_le_natAbs _ _

theorem floor_code_bits (q : ℚ) (B : ℕ) (input : (Code.ofRat q).Bounded B) :
    (Code.ofRat (⌊q⌋ : ℚ)).bits ≤ B+3 := by
  have numerator := Nat.size_le.mpr ((floor_abs q).trans_lt input.1)
  simpa [Code.ofRat,Code.bits] using Nat.add_le_add_right numerator 3

def expression : ℚ → ℕ → Expr
  | q,0 => .literal (Code.ofRat (⌊q⌋ : ℚ))
  | q,n+1 => .add (.literal (Code.ofRat (⌊q⌋ : ℚ))) (.inv (expression (continuedTail q) n))

@[simp] theorem expression_value (q : ℚ) (n : ℕ) : (expression q n).value = rationalConvergent q n := by
  induction n generalizing q <;> simp_all [expression,Expr.value,rationalConvergent]

@[simp] theorem expression_size (q : ℚ) (n : ℕ) : (expression q n).treeSize = 3*n+1 := by
  induction n generalizing q <;> simp_all [expression,Expr.treeSize] <;> omega

theorem expression_leaves (q : ℚ) (n B : ℕ) (input : (Code.ofRat q).Bounded B) :
    (expression q n).maxLeafBudget ≤ B+4 := by
  induction n generalizing q with
  | zero => exact Nat.add_le_add_right (floor_code_bits q B input) 1
  | succ n ih =>
    exact max_le (Nat.add_le_add_right (floor_code_bits q B input) 1)
      (ih _ (tail_bounded q B input))

theorem convergent_bits (q : ℚ) (n B : ℕ) (input : (Code.ofRat q).Bounded B) :
    (Code.ofRat (rationalConvergent q n)).bits ≤ 2*(3*n+1)*(B+4)+2 := by
  have bound := (expression q n).normalized_bits (B+4) (by omega) (expression_leaves q n B input)
  simpa only [expression_value,expression_size] using bound

def floorRational (q : ℚ) : Traced ℚ :=
  let f := q.num/(q.den : ℤ)
  let result : ℚ := f
  ⟨result,[⟨.read, [q.num.natAbs.size+1,q.den.size+1]⟩,
    ⟨.intDiv,[q.num.natAbs.size+1,q.den.size+1,f.natAbs.size+1]⟩,
    ⟨.ratCast,[f.natAbs.size+1,(Code.ofRat result).bits]⟩,
    ⟨.write,[(Code.ofRat result).bits]⟩]⟩

@[simp] theorem floorRational_value (q : ℚ) : (floorRational q).value = (⌊q⌋ : ℚ) := by
  simp [floorRational,Rat.floor_def']
@[simp] theorem floorRational_count (q : ℚ) : (floorRational q).events.length = 4 := rfl

def tail (q : ℚ) : Traced ℚ :=
  let f := floorRational q
  let negative := emit .ratNeg [(Code.ofRat f.value).bits,(Code.ofRat (-f.value)).bits] (-f.value)
  let fraction := ratAdd q negative.value
  let result := ratDiv 1 fraction.value
  ⟨result.value,f.events++[⟨.read,[(Code.ofRat q).bits]⟩]++negative.events++fraction.events++result.events++
    [⟨.write,[(Code.ofRat result.value).bits]⟩]⟩

@[simp] theorem tail_value (q : ℚ) : (tail q).value = continuedTail q := by
  simp [tail,continuedTail,Int.fract,sub_eq_add_neg]
@[simp] theorem tail_count (q : ℚ) : (tail q).events.length = 11 := rfl

def convergent : ℚ → ℕ → Traced ℚ
  | q,0 =>
      let f := floorRational q
      ⟨f.value,[⟨.recurse,[0]⟩,⟨.branch,[1]⟩]++f.events⟩
  | q,n+1 =>
      let f := floorRational q
      let t := tail q
      let child := convergent t.value n
      let inverse := ratDiv 1 child.value
      let result := ratAdd f.value inverse.value
      ⟨result.value,[⟨.recurse,[(n+1).size]⟩,⟨.branch,[1]⟩]++f.events++t.events++child.events++
        inverse.events++result.events++[⟨.write,[(Code.ofRat result.value).bits]⟩]⟩

@[simp] theorem convergent_value (q : ℚ) (n : ℕ) : (convergent q n).value = rationalConvergent q n := by
  induction n generalizing q <;> simp_all [convergent,rationalConvergent]

theorem convergent_count (q : ℚ) (n : ℕ) : (convergent q n).events.length = 22*n+6 := by
  induction n generalizing q with
  | zero => simp [convergent]
  | succ n ih =>
    simp only [convergent,List.length_append,List.length_cons,List.length_nil,floorRational_count,
      tail_count,ratDiv_length,ratAdd_length,ih]
    omega

theorem floorRational_words (q : ℚ) (B : ℕ) (input : (Code.ofRat q).Bounded B) :
    WordsWithin (B+3) (floorRational q).events := by
  have numerator : q.num.natAbs.size ≤ B := Nat.size_le.mpr input.1
  have denominator : q.den.size ≤ B := by
    apply Nat.size_le.mpr
    simpa only [Code.ofRat,Int.natAbs_natCast] using input.2
  have floor := Nat.size_le.mpr ((floor_abs q).trans_lt input.1)
  have encoded := floor_code_bits q B input
  simp only [floorRational,← Rat.floor_def',wordsWithin_cons,wordsWithin_nil,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  repeat' apply And.intro
  all_goals omega

theorem fract_bounded (q : ℚ) (B : ℕ) (input : (Code.ofRat q).Bounded B) :
    (Code.ofRat (Int.fract q)).Bounded B := by
  have positive : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have num_nonnegative : 0 ≤ (Int.fract q).num := Rat.num_nonneg.mpr (Int.fract_nonneg q)
  have num_small : ((Int.fract q).num : ℚ) < (q.den : ℚ) := by
    have bound := Int.fract_lt_one q
    rw [← (Int.fract q).num_div_den,Rat.den_intFract] at bound
    exact (div_lt_one positive).mp bound
  have abs_num : (Int.fract q).num.natAbs < q.den := by
    have bound : (Int.fract q).num < (q.den : ℤ) := by exact_mod_cast num_small
    exact_mod_cast (show ((Int.fract q).num.natAbs : ℤ) < (q.den : ℤ) by
      simpa only [Int.natAbs_of_nonneg num_nonnegative] using bound)
  have den : q.den < 2^B := by simpa only [Code.ofRat,Int.natAbs_natCast] using input.2
  exact ⟨abs_num.trans den,by simpa only [Code.ofRat,Int.natAbs_natCast,Rat.den_intFract] using den⟩

theorem tail_words (q : ℚ) (B : ℕ) (input : (Code.ofRat q).Bounded B) :
    WordsWithin (8*B+32) (tail q).events := by
  have q_bits := Code.bounded_bits input
  have f_bits := floor_code_bits q B input
  have neg_bits : (Code.ofRat (-(⌊q⌋ : ℚ))).bits = (Code.ofRat (⌊q⌋ : ℚ)).bits := by simp [Code.ofRat,Code.bits]
  have fwords := (floorRational_words q B input).mono (show B+3 ≤ 8*B+32 by omega)
  have addwords := WordsWithin.mono (ratAdd_words q (-(⌊q⌋ : ℚ)))
    (show 2*((Code.ofRat q).bits+(Code.ofRat (-(⌊q⌋ : ℚ))).bits)+8 ≤ 8*B+32 by omega)
  have fractional : q+(-(⌊q⌋ : ℚ)) = Int.fract q := by simp [Int.fract,sub_eq_add_neg]
  have frac_bits := Code.bounded_bits (fract_bounded q B input)
  have divwords := WordsWithin.mono (ratDiv_words 1 (Int.fract q))
    (show 2*((Code.ofRat 1).bits+(Code.ofRat (Int.fract q)).bits)+8 ≤ 8*B+32 by
      rw [show (Code.ofRat 1).bits=4 by decide]; omega)
  have result_bits := Code.bounded_bits (tail_bounded q B input)
  simp only [tail,wordsWithin_append,floorRational_value,emit_value,ratAdd_value,ratDiv_value,fractional]
  repeat' apply And.intro
  all_goals first
    | exact fwords
    | exact addwords
    | simpa only [one_div,continuedTail] using divwords
    | simp only [wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true,emit]
      repeat' apply And.intro
      all_goals first | omega | simpa only [one_div,continuedTail] using (show (Code.ofRat (continuedTail q)).bits ≤ 8*B+32 by omega)

def wordBudget (n B : ℕ) : ℕ := 64*(n+1)*(B+4)+128

theorem convergent_words (q : ℚ) (n B : ℕ) (input : (Code.ofRat q).Bounded B) :
    WordsWithin (wordBudget n B) (convergent q n).events := by
  induction n generalizing q with
  | zero =>
    have floor := (floorRational_words q B input).mono
      (show B+3 ≤ wordBudget 0 B by unfold wordBudget; omega)
    simp only [convergent,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    exact ⟨⟨by unfold wordBudget; omega,by unfold wordBudget; omega⟩,floor⟩
  | succ n ih =>
    let K := wordBudget (n+1) B
    have floor := (floorRational_words q B input).mono (show B+3 ≤ K by dsimp [K,wordBudget]; nlinarith)
    have tail := (tail_words q B input).mono (show 8*B+32 ≤ K by dsimp [K,wordBudget]; nlinarith)
    have child := (ih (continuedTail q) (tail_bounded q B input)).mono
      (show wordBudget n B ≤ K by dsimp [K,wordBudget]; nlinarith)
    have child_bits : (Code.ofRat (convergent (continuedTail q) n).value).bits ≤ 2*(3*n+1)*(B+4)+2 := by
      rw [convergent_value]
      exact convergent_bits _ n B (tail_bounded q B input)
    have floor_bits := floor_code_bits q B input
    have inverse_bits := ratDiv_result_bits 1 (convergent (continuedTail q) n).value
    rw [show (Code.ofRat 1).bits=4 by decide] at inverse_bits
    have inverse := WordsWithin.mono (ratDiv_words 1 (convergent (continuedTail q) n).value)
      (show 2*((Code.ofRat 1).bits+(Code.ofRat (convergent (continuedTail q) n).value).bits)+8 ≤ K by
        rw [show (Code.ofRat 1).bits=4 by decide]; dsimp [K,wordBudget]; nlinarith)
    have added := WordsWithin.mono
      (ratAdd_words (floorRational q).value (ratDiv 1 (convergent (continuedTail q) n).value).value)
      (show 2*((Code.ofRat (floorRational q).value).bits+
        (Code.ofRat (ratDiv 1 (convergent (continuedTail q) n).value).value).bits)+8 ≤ K by
          rw [floorRational_value,ratDiv_value]; dsimp [K,wordBudget]; nlinarith)
    have write : (Code.ofRat (ratAdd (floorRational q).value
        (ratDiv 1 (convergent (continuedTail q) n).value).value).value).bits ≤ K := by
      have current := convergent_bits q (n+1) B input
      simpa only [rationalConvergent,convergent_value,floorRational_value,ratAdd_value,ratDiv_value,one_div] using
        current.trans (show 2*(3*(n+1)+1)*(B+4)+2 ≤ K by dsimp [K,wordBudget]; nlinarith)
    have counter : (n+1).size ≤ n+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [convergent,wordsWithin_append,tail_value,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    repeat' apply And.intro
    all_goals first
      | exact floor
      | exact tail
      | exact child
      | exact inverse
      | exact added
      | exact write
      | dsimp [K,wordBudget] at *; nlinarith

/-- Complete continued-fraction evaluation contract for the named rational
program: exact value, linear primitive count, polynomial intermediate words. -/
theorem convergent_runtime (q : ℚ) (n B : ℕ) (input : (Code.ofRat q).Bounded B) :
    (convergent q n).value = rationalConvergent q n ∧
    (convergent q n).events.length = 22*n+6 ∧
    WordsWithin (wordBudget n B) (convergent q n).events :=
  ⟨convergent_value q n,convergent_count q n,convergent_words q n B input⟩

def candidates (q : ℚ) : List ℕ → Traced (List ℚ)
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | n::rest =>
      let value := convergent q n
      let tail := candidates q rest
      ⟨value.value::tail.value,[⟨.scan,[n.size]⟩]++value.events++tail.events++
        [⟨.cons,[(Code.ofRat value.value).bits]⟩]⟩

@[simp] theorem candidates_value (q : ℚ) (indices : List ℕ) :
    (candidates q indices).value = indices.map (rationalConvergent q) := by
  induction indices with
  | nil => rfl
  | cons n rest ih => simp [candidates,ih]

theorem candidates_count (q : ℚ) (indices : List ℕ) (F : ℕ) (bounds : ∀ n ∈ indices, n ≤ F) :
    (candidates q indices).events.length ≤ indices.length*(22*F+8)+1 := by
  induction indices with
  | nil => simp [candidates]
  | cons n rest ih =>
    have bound := bounds n (by simp)
    have tail := ih (fun n member => bounds n (by simp [member]))
    simp only [candidates,List.length_append,List.length_cons,List.length_nil,convergent_count]
    nlinarith

def accepted (lo hi : ℚ) (D : ℕ) (q : ℚ) : Traced Bool :=
  let lower := ratLe lo q
  if lower.value then
    let upper := ratLe q hi
    if upper.value then
      let result := decide (q.den ≤ D)
      ⟨result,lower.events++[⟨.branch,[1]⟩]++upper.events++[⟨.branch,[1]⟩,
        ⟨.natCompare,[q.den.size,D.size]⟩,⟨.branch,[1]⟩]⟩
    else ⟨false,lower.events++[⟨.branch,[1]⟩]++upper.events++[⟨.branch,[1]⟩]⟩
  else ⟨false,lower.events++[⟨.branch,[1]⟩]⟩

@[simp] theorem accepted_value (lo hi q : ℚ) (D : ℕ) :
    (accepted lo hi D q).value = decide (lo ≤ q ∧ q ≤ hi ∧ q.den ≤ D) := by
  unfold accepted
  simp only [ratLe,emit_value]
  by_cases lower : lo ≤ q <;> by_cases upper : q ≤ hi <;> simp [lower,upper]

theorem accepted_count (lo hi q : ℚ) (D : ℕ) : (accepted lo hi D q).events.length ≤ 6 := by
  dsimp only [accepted]
  split_ifs <;> simp [ratLe,emit,List.length_append]

def find (lo hi : ℚ) (D : ℕ) : List ℚ → Traced (Option ℚ)
  | [] => ⟨none,[⟨.branch,[1]⟩]⟩
  | q::rest =>
      let tested := accepted lo hi D q
      if tested.value then
        ⟨some q,[⟨.scan,[1]⟩,⟨.read,[(Code.ofRat q).bits]⟩]++tested.events++
          [⟨.branch,[1]⟩,⟨.cons,[(Code.ofRat q).bits]⟩]⟩
      else
        let tail := find lo hi D rest
        ⟨tail.value,[⟨.scan,[1]⟩,⟨.read,[(Code.ofRat q).bits]⟩]++tested.events++[⟨.branch,[1]⟩]++tail.events⟩

@[simp] theorem find_value (lo hi : ℚ) (D : ℕ) (values : List ℚ) :
    (find lo hi D values).value = values.find? (fun q => decide (lo ≤ q ∧ q ≤ hi ∧ q.den ≤ D)) := by
  induction values with
  | nil => rfl
  | cons q rest ih =>
    simp only [find,accepted_value,List.find?]
    cases tested : decide (lo ≤ q ∧ q ≤ hi ∧ q.den ≤ D) <;>
      simp only [tested,Bool.false_eq_true,ite_true,ite_false,ih]

theorem find_count (lo hi : ℚ) (D : ℕ) (values : List ℚ) :
    (find lo hi D values).events.length ≤ 10*values.length+1 := by
  induction values with
  | nil => simp [find]
  | cons q rest ih =>
    have test := accepted_count lo hi q D
    simp only [find]
    split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega

def reconstruct (lo hi : ℚ) (D : ℕ) : Traced (Option ℚ) :=
  let list := candidates lo (List.range (2*lo.den.size+1))
  let result := find lo hi D list.value
  ⟨result.value,list.events++result.events⟩

@[simp] theorem reconstruct_value (lo hi : ℚ) (D : ℕ) :
    (reconstruct lo hi D).value = PolynomialLP.reconstruct lo hi D := by
  simp [reconstruct,PolynomialLP.reconstruct,reconstructionCandidates]

theorem reconstruct_count (lo hi : ℚ) (D : ℕ) :
    (reconstruct lo hi D).events.length ≤
      (2*lo.den.size+1)*(44*lo.den.size+18)+2 := by
  have first := candidates_count lo (List.range (2*lo.den.size+1)) (2*lo.den.size)
    (fun i member => Nat.le_of_lt_succ (List.mem_range.mp member))
  have last := find_count lo hi D (candidates lo (List.range (2*lo.den.size+1))).value
  simp only [candidates_value,List.length_map,List.length_range] at first last
  simp only [reconstruct,List.length_append,candidates_value]
  nlinarith

theorem candidates_words (q : ℚ) (indices : List ℕ) (F B : ℕ)
    (input : (Code.ofRat q).Bounded B) (bounds : ∀ n ∈ indices, n ≤ F) :
    WordsWithin (wordBudget F B) (candidates q indices).events := by
  induction indices with
  | nil => simp [candidates,WordsWithin,wordBudget]
  | cons n rest ih =>
    have nbound := bounds n (by simp)
    have scanned := (convergent_words q n B input).mono
      (show wordBudget n B ≤ wordBudget F B by unfold wordBudget; nlinarith)
    have tail := ih (fun n member => bounds n (by simp [member]))
    have result_bits := convergent_bits q n B input
    have index_bits : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [candidates,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,convergent_value]
    repeat' apply And.intro
    all_goals first | exact scanned | exact tail | unfold wordBudget; nlinarith

theorem accepted_words (lo hi q : ℚ) (D K : ℕ) (positive : 1 ≤ K)
    (lower : (Code.ofRat lo).bits ≤ K) (upper : (Code.ofRat hi).bits ≤ K)
    (value : (Code.ofRat q).bits ≤ K) (denominator : D.size ≤ K) :
    WordsWithin K (accepted lo hi D q).events := by
  have den : q.den.size ≤ K := by
    simp only [Code.ofRat,Code.bits,Int.natAbs_natCast] at value
    omega
  dsimp only [accepted]
  split_ifs <;> simp only [ratLe,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals repeat' apply And.intro
  all_goals omega

theorem find_words (lo hi : ℚ) (D K : ℕ) (values : List ℚ) (positive : 1 ≤ K)
    (lower : (Code.ofRat lo).bits ≤ K) (upper : (Code.ofRat hi).bits ≤ K)
    (denominator : D.size ≤ K) (inputs : ∀ q ∈ values, (Code.ofRat q).bits ≤ K) :
    WordsWithin K (find lo hi D values).events := by
  induction values with
  | nil => simpa [find,WordsWithin] using positive
  | cons q rest ih =>
    have qbits := inputs q (by simp)
    have checked := accepted_words lo hi q D K positive lower upper qbits denominator
    have tail := ih (fun q member => inputs q (by simp [member]))
    simp only [find]
    split <;> simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals repeat' apply And.intro
    all_goals first | exact checked | exact tail | omega

theorem reconstruct_words (lo hi : ℚ) (D B : ℕ)
    (input : (Code.ofRat lo).Bounded B) (upper : (Code.ofRat hi).bits ≤ 2*B+2) :
    WordsWithin (wordBudget (2*lo.den.size) B+D.size+8) (reconstruct lo hi D).events := by
  let F := 2*lo.den.size
  let K := wordBudget F B+D.size+8
  have positive : 1 ≤ K := by dsimp [K,wordBudget]; omega
  have base := candidates_words lo (List.range (F+1)) F B input
    (fun n member => Nat.le_of_lt_succ (List.mem_range.mp member))
  have values : ∀ q ∈ (candidates lo (List.range (F+1))).value, (Code.ofRat q).bits ≤ K := by
    intro q member
    rw [candidates_value] at member
    obtain ⟨n,index_mem,rfl⟩ := List.mem_map.mp member
    have nb : n ≤ F := Nat.le_of_lt_succ (List.mem_range.mp index_mem)
    have bits := convergent_bits lo n B input
    dsimp [K,wordBudget]
    nlinarith
  have lower_bits := Code.bounded_bits input
  have find := find_words lo hi D K (candidates lo (List.range (F+1))).value positive
    (by dsimp [K,wordBudget]; nlinarith) (by dsimp [K,wordBudget]; nlinarith)
    (by dsimp [K]; omega) values
  exact (wordsWithin_append K _ _).mpr ⟨base.mono (show wordBudget F B ≤ K by dsimp [K]; omega),find⟩

theorem reconstruction_runtime (lo hi : ℚ) (D B : ℕ)
    (input : (Code.ofRat lo).Bounded B) (upper : (Code.ofRat hi).bits ≤ 2*B+2) :
    (reconstruct lo hi D).value = PolynomialLP.reconstruct lo hi D ∧
    (reconstruct lo hi D).events.length ≤ (2*B+1)*(44*B+18)+2 ∧
    WordsWithin (wordBudget (2*B) B+D.size+8) (reconstruct lo hi D).events := by
  have den : lo.den.size ≤ B := by
    apply Nat.size_le.mpr
    simpa only [Code.ofRat,Int.natAbs_natCast] using input.2
  refine ⟨reconstruct_value lo hi D,?_,?_⟩
  · exact (reconstruct_count lo hi D).trans (Nat.add_le_add_right
      (Nat.mul_le_mul (by omega) (by omega)) 2)
  · exact (reconstruct_words lo hi D B input upper).mono (by unfold wordBudget; nlinarith)

end BuyAtBulk.PolynomialLP.ReconstructionRuntime
