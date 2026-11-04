import BuyAtBulk.Computation.Core.Rows
import BuyAtBulk.UpperBound.ExecutionState
import BuyAtBulk.Computation.HelperChoose

/-! Data-only executable helper selection and initialization. Stored row values
and explicit schedules feed the rational conditional-expectation program;
no LP paths/flows are read by this computation. -/
namespace BuyAtBulk.Computation.Core
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n h ratio : ℕ} (G : SimpleGraph V)
    (numbering : V ≃ Fin n)

def vertexOrder : List V := (List.finRange n).map numbering.symm

def helperRepetitions (h : ℕ) : ℕ := Nat.clog 2 (8 * h)
def helperAlpha (h : ℕ) : ℚ := 128 * helperRepetitions h

def heavyVertices (opening : V → ℚ) (h : ℕ) : List V :=
  (vertexOrder numbering).filter fun v => decide (1 ≤ helperAlpha h * opening v)

def helperProbability (opening : V → ℚ) (h : ℕ) (v : V) : ℚ :=
  if 1 ≤ helperAlpha h * opening v then 0 else helperAlpha h * opening v

def storedToll (database : RowDatabase h ratio n) (raw : RawRow h ratio) (v : V) : ℚ :=
  (getRow database raw).toll[(numbering v).val]

def helperFactor (database : RowDatabase h ratio n) (raw : RawRow h ratio) (v : V) : ℚ :=
  1 - storedToll numbering database raw v / (2 * (getRow database raw).radius)

def helperAmplitude (opening : V → ℚ) (database : RowDatabase h ratio n) (raw : RawRow h ratio) : ℚ :=
  if ((heavyVertices numbering opening h).map fun v => opening v * storedToll numbering database raw v).sum <
      3 * (getRow database raw).radius / 8 then (2 : ℚ) ^ (16 * helperRepetitions h) else 0

def helperFixedCost (buying opening : V → ℚ) (h : ℕ) : ℚ :=
  ((heavyVertices numbering opening h).map buying).sum

def chooseHelper (buying opening : V → ℚ) (budget : ℚ) (database : RowDatabase h ratio n) : List V × ℕ :=
  HelperExpressions.chooseScheduled buying (helperProbability opening h) (helperFactor numbering database)
    (helperAmplitude numbering opening database) (helperFixedCost numbering buying opening h)
    (4 * helperAlpha h * budget) (includedRows database) [] (vertexOrder numbering)

def helperNodes (buying opening : V → ℚ) (budget : ℚ) (database : RowDatabase h ratio n) : Finset V :=
  (heavyVertices numbering opening h).toFinset ∪ (chooseHelper numbering buying opening budget database).1.toFinset

def zeroBuyingNodes (buying : V → ℚ) : Finset V :=
  ((vertexOrder numbering).filter fun v => decide (buying v = 0)).toFinset

def initialState (buying opening : V → ℚ) (budget : ℚ) (database : RowDatabase h ratio n) (seed : Finset V) : RoundingState G :=
  { bought := seed ∪ helperNodes numbering buying opening budget database ∪ zeroBuyingNodes numbering buying
    centers := []
    edges := [] }

@[simp] theorem mem_vertexOrder (v : V) : v ∈ vertexOrder numbering := by
  unfold vertexOrder
  apply List.mem_map.mpr
  exact ⟨numbering v, by simp, numbering.symm_apply_apply v⟩

theorem vertexOrder_nodup : (vertexOrder numbering).Nodup :=
  (List.nodup_finRange n).map numbering.symm.injective

theorem heavyVertices_nodup (opening : V → ℚ) (h : ℕ) : (heavyVertices numbering opening h).Nodup :=
  (vertexOrder_nodup numbering).filter _

@[simp] theorem mem_heavyVertices (opening : V → ℚ) (h : ℕ) (v : V) :
    v ∈ heavyVertices numbering opening h ↔ 1 ≤ helperAlpha h * opening v := by
  simp only [heavyVertices, List.mem_filter, mem_vertexOrder, true_and, decide_eq_true_eq]

@[simp] theorem mem_zeroBuyingNodes (buying : V → ℚ) (v : V) :
    v ∈ zeroBuyingNodes numbering buying ↔ buying v = 0 := by
  simp only [zeroBuyingNodes, List.mem_toFinset, List.mem_filter, mem_vertexOrder, true_and, decide_eq_true_eq]

/-- Reindexing an explicit row list changes no estimator expression. -/
theorem potential_mapRows {R S : Type} (buying probability : V → ℚ) (factor : S → V → ℚ)
    (amplitude : S → ℚ) (fixedCost normalization : ℚ) (rows : List R) (index : R → S)
    (selected remaining : List V) :
    HelperExpressions.potential buying probability factor amplitude fixedCost normalization (rows.map index) selected remaining =
      HelperExpressions.potential buying probability (fun r => factor (index r)) (fun r => amplitude (index r))
        fixedCost normalization rows selected remaining := by
  simp only [HelperExpressions.potential, List.map_map, Function.comp_def]

/-- Both actual selections and their work counters are invariant under a
row-index map when all numerical fields are pulled back along that map. -/
theorem chooseScheduled_mapRows {R S : Type} (buying probability : V → ℚ) (factor : S → V → ℚ)
    (amplitude : S → ℚ) (fixedCost normalization : ℚ) (rows : List R) (index : R → S)
    (selected remaining : List V) :
    HelperExpressions.chooseScheduled buying probability factor amplitude fixedCost normalization (rows.map index) selected remaining =
      HelperExpressions.chooseScheduled buying probability (fun r => factor (index r)) (fun r => amplitude (index r))
        fixedCost normalization rows selected remaining := by
  induction remaining generalizing selected with
  | nil => simp only [HelperExpressions.chooseScheduled]
  | cons v remaining ih =>
    simp only [HelperExpressions.chooseScheduled, potential_mapRows, ih]

end BuyAtBulk.Computation.Core
