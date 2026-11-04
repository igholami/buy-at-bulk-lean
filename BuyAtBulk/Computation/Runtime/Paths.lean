import BuyAtBulk.Computation.Runtime.Primitive
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Explicit list and walk operations used by cycle erasure. Traces include
support construction, equality scans and the drop traversal itself. -/
namespace BuyAtBulk.Computation.Runtime.Paths
variable {n : ℕ} {G : SimpleGraph (Fin n)}

def support {u v : Fin n} : G.Walk u v → Traced (List (Fin n))
  | .nil => ⟨[u], [⟨.branch, [1]⟩, ⟨.cons, [u.val.size]⟩]⟩
  | .cons _ tail =>
      let result := support tail
      ⟨u :: result.value, [⟨.branch, [1]⟩] ++ result.events ++ [⟨.cons, [u.val.size]⟩]⟩

@[simp] theorem support_value {u v : Fin n} (walk : G.Walk u v) :
    (support walk).value = walk.support := by
  induction walk with
  | nil => rfl
  | cons edge tail ih => simp [support, ih]

theorem support_count {u v : Fin n} (walk : G.Walk u v) :
    (support walk).events.length = 2 * (walk.length + 1) := by
  induction walk with
  | nil => rfl
  | cons edge tail ih => simp [support, ih]; omega

def member (v : Fin n) : List (Fin n) → Traced Bool
  | [] => ⟨false, [⟨.branch, [1]⟩]⟩
  | u :: rest =>
      if u = v then
        ⟨true, [⟨.scan, [u.val.size]⟩, ⟨.branch, [u.val.size, v.val.size]⟩]⟩
      else
        let result := member v rest
        ⟨result.value, [⟨.scan, [u.val.size]⟩, ⟨.branch, [u.val.size, v.val.size]⟩] ++ result.events⟩

@[simp] theorem member_value (v : Fin n) (vertices : List (Fin n)) :
    (member v vertices).value = decide (v ∈ vertices) := by
  induction vertices with
  | nil => rfl
  | cons u rest ih =>
      by_cases same : u = v
      · subst u; simp [member]
      · simp [member, same, ih, Ne.symm same]

theorem member_count (v : Fin n) (vertices : List (Fin n)) :
    (member v vertices).events.length ≤ 2 * vertices.length + 1 := by
  induction vertices with
  | nil => rfl
  | cons u rest ih =>
      simp only [member]
      split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

def dropUntil {v w : Fin n} : (walk : G.Walk v w) → (u : Fin n) → u ∈ walk.support → Traced (G.Walk u w)
  | .nil, u, h =>
      ⟨(SimpleGraph.Walk.nil : G.Walk v v).copy (SimpleGraph.Walk.mem_support_nil_iff.mp h).symm rfl,
        [⟨.branch, [v.val.size, u.val.size]⟩]⟩
  | .cons edge tail, u, h =>
      if same : v = u then
        ⟨(SimpleGraph.Walk.cons edge tail).copy same rfl,
          [⟨.branch, [v.val.size, u.val.size]⟩]⟩
      else
        let result := dropUntil tail u (by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at h
          exact h.resolve_left (Ne.symm same))
        ⟨result.value, [⟨.branch, [v.val.size, u.val.size]⟩] ++ result.events⟩

theorem dropUntil_value {u v w : Fin n} (walk : G.Walk v w) (h : u ∈ walk.support) :
    (dropUntil walk u h).value = walk.dropUntil u h := by
  induction walk with
  | nil =>
      have same := SimpleGraph.Walk.mem_support_nil_iff.mp h
      subst u
      rfl
  | cons edge tail ih =>
      simp only [dropUntil, SimpleGraph.Walk.dropUntil]
      split
      · rename_i same
        subst u
        rfl
      · exact ih _

theorem dropUntil_count {u v w : Fin n} (walk : G.Walk v w) (h : u ∈ walk.support) :
    (dropUntil walk u h).events.length ≤ walk.length + 1 := by
  induction walk with
  | nil => rfl
  | cons edge tail ih =>
      simp only [dropUntil]
      split
      · simp
      · simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons]
        have bound := ih (by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at h
          exact h.resolve_left (by rename_i same; exact Ne.symm same))
        omega

def bypass {u v : Fin n} : G.Walk u v → Traced (G.Walk u v)
  | .nil => ⟨.nil, [⟨.branch, [1]⟩]⟩
  | .cons edge walk =>
      let tail := bypass walk
      let vertices := support tail.value
      let included := member u vertices.value
      let control := [⟨Operation.branch, [1]⟩] ++ tail.events ++ vertices.events ++ included.events
      if found : included.value = true then
        let result := dropUntil tail.value u (by
          have h := (member_value u vertices.value).symm.trans found
          have h' := of_decide_eq_true h
          simpa only [vertices, support_value] using h')
        ⟨result.value, control ++ [⟨.branch, [1]⟩] ++ result.events⟩
      else
        ⟨.cons edge tail.value, control ++ [⟨.branch, [1]⟩, ⟨.cons, [u.val.size]⟩]⟩

@[simp] theorem bypass_value {u v : Fin n} (walk : G.Walk u v) :
    (bypass walk).value = walk.bypass := by
  induction walk with
  | nil => rfl
  | cons edge walk ih =>
      simp only [bypass, support_value, member_value, ih, decide_eq_true_eq]
      rw [SimpleGraph.Walk.bypass]
      split
      · simp only [dropUntil_value]
      · rfl

theorem bypass_count {u v : Fin n} (walk : G.Walk u v) :
    (bypass walk).events.length ≤ 6 * (walk.length + 1) ^ 2 := by
  induction walk with
  | nil => simp [bypass]
  | @cons a b c edge walk ih =>
      have shortened : (bypass walk).value.length ≤ walk.length := by
        rw [bypass_value]
        exact walk.length_bypass_le_length
      have supported := support_count (bypass walk).value
      have members := member_count a (support (bypass walk).value).value
      simp only [support_value, SimpleGraph.Walk.length_support] at members
      simp only [bypass]
      split
      · rename_i found
        have dropped := dropUntil_count (u := a) (bypass walk).value (by
          have h := (member_value a (support (bypass walk).value).value).symm.trans found
          simpa only [support_value] using of_decide_eq_true h)
        simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons, support_value]
        nlinarith
      · simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons, support_value]
        nlinarith

def toPath {u v : Fin n} (walk : G.Walk u v) : Traced (G.Path u v) :=
  let result := bypass walk
  ⟨⟨result.value, by rw [bypass_value]; exact walk.bypass_isPath⟩, result.events⟩

@[simp] theorem toPath_value {u v : Fin n} (walk : G.Walk u v) :
    (toPath walk).value = walk.toPath := by
  apply Subtype.ext
  exact bypass_value walk

theorem toPath_count {u v : Fin n} (walk : G.Walk u v) :
    (toPath walk).events.length ≤ 6 * (walk.length + 1) ^ 2 := bypass_count walk

private theorem index_width (v : Fin n) : v.val.size ≤ n :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt)

theorem support_words {u v : Fin n} (walk : G.Walk u v) (K : ℕ)
    (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (support walk).events := by
  induction walk with
  | nil => simp [support, WordsWithin, one, (index_width _).trans indices]
  | @cons a b c edge tail ih =>
      have a_width := (index_width a).trans indices
      simp only [support, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_singleton, forall_eq]
      aesop

theorem member_words (v : Fin n) (vertices : List (Fin n)) (K : ℕ)
    (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (member v vertices).events := by
  have v_width := (index_width v).trans indices
  induction vertices with
  | nil => simp [member, WordsWithin, one]
  | cons u rest ih =>
      have u_width := (index_width u).trans indices
      simp only [member]
      split <;> simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop

theorem dropUntil_words {u v w : Fin n} (walk : G.Walk v w) (h : u ∈ walk.support) (K : ℕ)
    (indices : n ≤ K) : WordsWithin K (dropUntil walk u h).events := by
  have u_width := (index_width u).trans indices
  induction walk with
  | nil => simp [dropUntil, WordsWithin, (index_width _).trans indices, u_width]
  | @cons a b c edge tail ih =>
      have a_width := (index_width a).trans indices
      simp only [dropUntil]
      split
      · simp [WordsWithin, a_width, u_width]
      · have recursive := ih (by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at h
          exact h.resolve_left (by rename_i missing; exact Ne.symm missing))
        simpa only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true] using
          And.intro (And.intro a_width u_width) recursive

theorem bypass_words {u v : Fin n} (walk : G.Walk u v) (K : ℕ)
    (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (bypass walk).events := by
  induction walk with
  | nil => simp [bypass, WordsWithin, one]
  | @cons a b c edge walk ih =>
      have a_width := (index_width a).trans indices
      have supported := support_words (bypass walk).value K indices one
      have members := member_words a (support (bypass walk).value).value K indices one
      simp only [bypass]
      split
      · rename_i found
        have dropped := dropUntil_words (u := a) (bypass walk).value (by
          have h := (member_value a (support (bypass walk).value).value).symm.trans found
          simpa only [support_value] using of_decide_eq_true h) K indices
        simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq]
        aesop
      · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq]
        aesop

theorem toPath_words {u v : Fin n} (walk : G.Walk u v) (K : ℕ)
    (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (toPath walk).events :=
  bypass_words walk K indices one

def append {u v w : Fin n} : G.Walk u v → G.Walk v w → Traced (G.Walk u w)
  | .nil, right => ⟨right, [⟨.branch, [1]⟩]⟩
  | .cons edge tail, right =>
      let result := append tail right
      ⟨.cons edge result.value, [⟨.branch, [1]⟩] ++ result.events ++ [⟨.cons, [u.val.size]⟩]⟩

@[simp] theorem append_value {u v w : Fin n} (left : G.Walk u v) (right : G.Walk v w) :
    (append left right).value = left.append right := by
  induction left with
  | nil => rfl
  | cons edge tail ih => simp [append, ih]

theorem append_count {u v w : Fin n} (left : G.Walk u v) (right : G.Walk v w) :
    (append left right).events.length = 2 * left.length + 1 := by
  induction left with
  | nil => rfl
  | cons edge tail ih => simp [append, ih]; omega

theorem append_words {u v w : Fin n} (left : G.Walk u v) (right : G.Walk v w)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (append left right).events := by
  induction left with
  | nil => simp [append, WordsWithin, one]
  | @cons a b c edge tail ih =>
      have ai := (index_width a).trans indices
      simp only [append, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq]
      aesop

def reverseAux {u v w : Fin n} : G.Walk u v → G.Walk u w → Traced (G.Walk v w)
  | .nil, accumulated => ⟨accumulated, [⟨.branch, [1]⟩]⟩
  | .cons edge tail, accumulated =>
      let result := reverseAux tail (.cons edge.symm accumulated)
      ⟨result.value, [⟨.branch, [1]⟩, ⟨.cons, [u.val.size]⟩] ++ result.events⟩

@[simp] theorem reverseAux_value {u v w : Fin n} (walk : G.Walk u v) (accumulated : G.Walk u w) :
    (reverseAux walk accumulated).value = walk.reverseAux accumulated := by
  induction walk generalizing w with
  | nil => rfl
  | cons edge tail ih => simp [reverseAux, SimpleGraph.Walk.reverseAux, ih]

theorem reverseAux_count {u v w : Fin n} (walk : G.Walk u v) (accumulated : G.Walk u w) :
    (reverseAux walk accumulated).events.length = 2 * walk.length + 1 := by
  induction walk generalizing w with
  | nil => rfl
  | cons edge tail ih => simp [reverseAux, ih]; omega

theorem reverseAux_words {u v w : Fin n} (walk : G.Walk u v) (accumulated : G.Walk u w)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) : WordsWithin K (reverseAux walk accumulated).events := by
  induction walk generalizing w with
  | nil => simp [reverseAux, WordsWithin, one]
  | @cons a b c edge tail ih =>
      have ai := (index_width a).trans indices
      have recursive := ih (.cons edge.symm accumulated)
      simp only [reverseAux, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq]
      aesop

def reverse {u v : Fin n} (walk : G.Walk u v) : Traced (G.Walk v u) :=
  reverseAux walk .nil

@[simp] theorem reverse_value {u v : Fin n} (walk : G.Walk u v) :
    (reverse walk).value = walk.reverse := reverseAux_value walk .nil

theorem reverse_count {u v : Fin n} (walk : G.Walk u v) :
    (reverse walk).events.length = 2 * walk.length + 1 := reverseAux_count walk .nil

theorem reverse_words {u v : Fin n} (walk : G.Walk u v) (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (reverse walk).events := reverseAux_words walk .nil K indices one

end BuyAtBulk.Computation.Runtime.Paths
