import BuyAtBulk.Computation.Runtime.CoreExecution
import BuyAtBulk.Computation.Rounding.Algorithm

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def zeroState (buying : Vector ℚ n) : Traced (StoredState.State input.graph) :=
  let flags := Weights.materialize (fun v : Fin n => do
    let q ← readRat buying v
    emit .ratCompare [(Code.ofRat q).bits,(Code.ofRat 0).bits] (decide (q=0))) (fun _ => 1)
  ⟨⟨flags.value,[],[]⟩,flags.events++[⟨.cons,[n.size]⟩]⟩

theorem zeroState_value (buying : Vector ℚ n) :
    StoredState.decode input.graph (zeroState input buying).value =
      Rounding.zeroState input.graph (Equiv.refl _) (fun v => buying[v.val]) := by
  have flags : StoredState.boughtSet (zeroState input buying).value.bought=Core.zeroBuyingNodes (Equiv.refl _) (fun v => buying[v.val]) := by
    ext v
    simp[zeroState,Weights.materialize,readRat,StoredState.mem_boughtSet,Core.mem_zeroBuyingNodes]
    by_cases zero : buying[v.val]=0 <;>simp_all
  exact congrArg (fun bought => (⟨bought,[],[]⟩ : RoundingState input.graph)) flags

def freeRoutes (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (state : StoredState.State input.graph) : List (Fin h) → Traced (Option (List (StoredBatch.Entry input source target)))
  | [] => emit .cons [1] (some [])
  | i::rest =>
    let route : Traced (Option (input.graph.Path source[i.val] target[i.val])) := AttachmentQueries.boughtRoute input physical state source[i.val] target[i.val] lengths[i.val]
    let prefixEvents : List Event := [⟨.scan,[i.val.size]⟩,⟨.read,[source[i.val].val.size]⟩,
      ⟨.read,[target[i.val].val.size]⟩,⟨.read,[(Code.ofRat lengths[i.val]).bits]⟩]++route.events++[⟨.branch,[1]⟩]
    show Traced (Option (List (StoredBatch.Entry input source target))) from
    match route.value with
    | none => ⟨none,prefixEvents⟩
    | some path =>
      let next : Traced (Option (List (StoredBatch.Entry input source target))) := freeRoutes physical source target lengths state rest
      show Traced (Option (List (StoredBatch.Entry input source target))) from
      match next.value with
      | none => ⟨none,prefixEvents++next.events++[(⟨.branch,[1]⟩ : Event)]⟩
      | some entries => ⟨some (⟨i,path⟩::entries),prefixEvents++next.events++[(⟨.branch,[1]⟩ : Event),⟨.cons,[i.val.size]⟩]⟩

theorem freeRoutes_value (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (state : StoredState.State input.graph) (order : List (Fin h)) :
    (freeRoutes input physical source target lengths state order).value=
      Rounding.freeRoutes input.graph (Equiv.refl _) (fun v => physical[v.val]) (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) (StoredState.decode input.graph state) order := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
    simp only[freeRoutes,Rounding.freeRoutes,←AttachmentQueries.boughtRoute_value]
    cases found : (AttachmentQueries.boughtRoute input physical state source[i.val] target[i.val] lengths[i.val]).value with
    | none => simp only[found]
    | some path =>
      simp only[found]
      rw[←ih]
      cases later : (freeRoutes input physical source target lengths state rest).value <;>simp[later]

theorem freeRoutes_count (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (state : StoredState.State input.graph) (order : List (Fin h)) :
    (freeRoutes input physical source target lengths state order).events.length ≤
      order.length*(AttachmentQueries.routeBudget n+12*n+8)+1 := by
  induction order with
  | nil => simp[freeRoutes,emit]
  | cons i rest ih =>
    have query := AttachmentQueries.boughtRoute_count input physical state source[i.val] target[i.val] lengths[i.val]
    simp only[freeRoutes]
    split
    · simp only[List.length_append,List.length_cons,List.length_nil]
      unfold AttachmentQueries.routeBudget at ih ⊢
      nlinarith
    · split <;>simp only[List.length_append,List.length_cons,List.length_nil] <;>unfold AttachmentQueries.routeBudget at ih ⊢ <;>nlinarith

theorem freeRoutes_words (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (state : StoredState.State input.graph) (order : List (Fin h)) (L : ℕ) (constant : 8 ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (StoredAttachment.wordBudget n 0 L+n+h+10) (freeRoutes input physical source target lengths state order).events := by
  let K := StoredAttachment.wordBudget n 0 L+n+h+10
  have one : 1 ≤ K := by dsimp[K];omega
  have ni : n ≤ K := by dsimp[K];omega
  have hi : h ≤ K := by dsimp[K];omega
  have scalar : L ≤ K := by dsimp[K,StoredAttachment.wordBudget];omega
  induction order with
  | nil => simpa[freeRoutes,emit,wordsWithin_cons] using one
  | cons i rest ih =>
    have query := (StoredServe.boughtRoute_words_uniform input physical state source[i.val] target[i.val] lengths[i.val]
      L 0 constant physical_width (lengths_width i)).mono
      (show StoredAttachment.wordBudget n 0 L ≤ K by dsimp[K];omega)
    have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : i.val.size ≤ i.val).trans (Nat.le_of_lt i.isLt)).trans hi
    have si := ((Nat.size_le.mpr Nat.lt_two_pow_self : source[i.val].val.size ≤ source[i.val].val).trans (Nat.le_of_lt source[i.val].isLt)).trans ni
    have ti := ((Nat.size_le.mpr Nat.lt_two_pow_self : target[i.val].val.size ≤ target[i.val].val).trans (Nat.le_of_lt target[i.val].isLt)).trans ni
    have li := (lengths_width i).trans scalar
    simp only[freeRoutes]
    split
    · simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop
    · split <;>simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] <;>aesop


theorem zeroState_count (buying : Vector ℚ n) : (zeroState input buying).events.length ≤ 4*n+2 := by
  have flags := Weights.materialize_count (fun v : Fin n => do
    let q ← readRat buying v
    emit .ratCompare [(Code.ofRat q).bits,(Code.ofRat 0).bits] (decide (q=0))) (fun _ => 1) 2 (by intro;rfl)
  simp only[zeroState,List.length_append,List.length_cons,List.length_nil]
  omega

theorem zeroState_words (buying : Vector ℚ n) (L : ℕ)
    (inputs : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L) :
    WordsWithin (n+L+5) (zeroState input buying).events := by
  let K := n+L+5
  have one : 1 ≤ K := by dsimp[K];omega
  have ni : n ≤ K := by dsimp[K];omega
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n).trans ni
  have flags := Weights.materialize_words (fun v : Fin n => do
    let q ← readRat buying v
    emit .ratCompare [(Code.ofRat q).bits,(Code.ofRat 0).bits] (decide (q=0))) (fun _ => 1) K ni (by
      intro v
      have vi := ((Nat.size_le.mpr Nat.lt_two_pow_self : v.val.size ≤ v.val).trans (Nat.le_of_lt v.isLt)).trans ni
      have qi := (inputs v).trans (show L ≤ K by dsimp[K];omega)
      have zero : (Code.ofRat 0).bits=3 := by decide
      simp only[Traced.bind_events,Traced.bind_value,readRat,emit_value,emit,zero,wordsWithin_append,wordsWithin_cons,
        wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      dsimp[K] at *
      aesop) (by intro;exact one)
  simpa only[zeroState,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using And.intro flags nn

end BuyAtBulk.Computation.Runtime.StoredRounding
