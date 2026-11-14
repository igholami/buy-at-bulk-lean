import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- The deterministic script prefix before query k, including intervening returns. -/
def queryPrefix {d : ℕ} : ℕ → List (DFSSymbol d) → List (DFSSymbol d)
  | _, [] => []
  | k, none::ss => none::queryPrefix k ss
  | 0, some _::_ => []
  | k+1, some a::ss => some a::queryPrefix k ss

/-- The suffix beginning at query k. Returns before that query belong to the prefix. -/
def querySuffix {d : ℕ} : ℕ → List (DFSSymbol d) → List (DFSSymbol d)
  | _, [] => []
  | k, none::ss => querySuffix k ss
  | 0, some a::ss => some a::ss
  | k+1, some _::ss => querySuffix k ss

 theorem queryPrefix_append_suffix {d : ℕ} (k : ℕ) (script : List (DFSSymbol d)) :
    queryPrefix k script ++ querySuffix k script = script := by
  induction script generalizing k with
  | nil => simp [queryPrefix,querySuffix]
  | cons s ss ih =>
    cases s with
    | none => simpa [queryPrefix,querySuffix] using congrArg (List.cons none) (ih k)
    | some a => cases k <;> simp [queryPrefix,querySuffix,ih]

 theorem queryPrefix_queries {d : ℕ} (k : ℕ) (script : List (DFSSymbol d)) :
    ((queryPrefix k script).filter Option.isSome).length =
      min k (script.filter Option.isSome).length := by
  induction script generalizing k with
  | nil => simp [queryPrefix]
  | cons s ss ih =>
    cases s with
    | none => simpa [queryPrefix] using ih k
    | some a => cases k <;> simp [queryPrefix, ih, Nat.succ_min_succ]

 theorem querySuffix_starts_query {d : ℕ} (k : ℕ) (script : List (DFSSymbol d))
    (hk : k < (script.filter Option.isSome).length) :
    ∃ a ss, querySuffix k script = some a::ss := by
  induction script generalizing k with
  | nil => simp at hk
  | cons s ss ih =>
    cases s with
    | none => exact ih k (by simpa using hk)
    | some a =>
      cases k with
      | zero => exact ⟨a,ss,rfl⟩
      | succ k => exact ih k (by simpa using hk)

 theorem queryPrefix_add {d : ℕ} (k l : ℕ) (script : List (DFSSymbol d)) :
    queryPrefix (k+l) script = queryPrefix k script ++ queryPrefix l (querySuffix k script) := by
  induction script generalizing k l with
  | nil => simp [queryPrefix,querySuffix]
  | cons s ss ih =>
    cases s with
    | none => simp [queryPrefix,querySuffix,ih]
    | some a => cases k <;> simp [queryPrefix,querySuffix,ih,Nat.succ_add]

 theorem queryPrefix_step {d : ℕ} (k : ℕ) (script : List (DFSSymbol d))
    (a : Fin d × Bool) (ss : List (DFSSymbol d))
    (hs : querySuffix k script = some a::ss) :
    queryPrefix (k+1) script = queryPrefix k script ++ some a::queryPrefix 0 ss := by
  rw [queryPrefix_add,hs]
  rfl

/-- Successful complete scripts have a successful prefix at every query boundary. -/
 theorem dfsReplay_queryPrefix (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (st : DFSState H q) (run : dfsReplay H q d ports π root script = some st) (k : ℕ) :
    ∃ before : DFSState H q,
      dfsReplay H q d ports π root (queryPrefix k script) = some before := by
  unfold dfsReplay at run ⊢
  rw [← queryPrefix_append_suffix k script, List.foldlM_append] at run
  cases hp : (queryPrefix k script).foldlM (dfsStep H q d ports π)
      ⟨[root],{root},∅,0⟩ with
  | none => simp [hp] at run
  | some before => exact ⟨before,rfl⟩

end BuyAtBulk.EdgeOnlyGap.ProofA
