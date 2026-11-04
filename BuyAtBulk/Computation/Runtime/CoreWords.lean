import BuyAtBulk.Computation.Runtime.Core

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def helperInputBudget (n h L : ℕ) := L+rowScalarBudget h L+rowTollBudget n h L+8

theorem nodeWords_mono (n h L : ℕ) {m M : ℕ} (bounded : m ≤ M) :
    MaterializedHelper.nodeWords n h m L ≤ MaterializedHelper.nodeWords n h M L := by
  dsimp only[MaterializedHelper.nodeWords,MaterializedHelper.tableWords]
  gcongr


def coreWords (n h L : ℕ) := databaseWordBudget n h L+
  (StoredServe.logarithmWordBudget h L+3*h+10)+(maximumRows h+3*h+6)+
  MaterializedHelper.nodeWords n h (maximumRows h) (helperInputBudget n h L)+executionWords n h L+100

theorem run_words (buying physical opening : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio)
    (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L)
    (ratio_width : ratio.size ≤ L) (r_width : r.size ≤ L) :
    WordsWithin (coreWords n h L) (run input buying physical opening budget allowance source target active ratio r seed ratio_ge).events := by
  let K := coreWords n h L
  let A := helperInputBudget n h L
  let database := (materializeRows input buying physical budget allowance source target ratio ratio_ge).value
  let included := (includedRows database ratio_ge).value
  let cached := (rowsVector included).value
  let helper := MaterializedHelper.nodes buying opening budget database cached.2
  have LA : L ≤ A := by dsimp[A,helperInputBudget];omega
  have radii : ∀ raw : Core.RawRow h ratio, (Code.ofRat (Core.getRow database raw).radius).bits ≤ A := by
    intro raw
    have actual := (materializeRow_runtime input buying physical budget allowance source target ratio ratio_ge raw L constant
      buying_width physical_width budget_width allowance_width ratio_width).2.1
    dsimp only[database]
    rw[materializeRows_value,Core.getRow_materializeRows,←materializeRow_value]
    exact actual.trans (by dsimp[A,helperInputBudget];omega)
  have tolls : ∀ raw : Core.RawRow h ratio, ∀ v : Fin n, (Code.ofRat (Core.getRow database raw).toll[v.val]).bits ≤ A := by
    intro raw v
    have actual := (materializeRow_runtime input buying physical budget allowance source target ratio ratio_ge raw L constant
      buying_width physical_width budget_width allowance_width ratio_width).2.2 v
    dsimp only[database]
    rw[materializeRows_value,Core.getRow_materializeRows,←materializeRow_value]
    exact actual.trans (by dsimp[A,helperInputBudget];omega)
  have database_words := (materializeRows_words input buying physical budget allowance source target ratio ratio_ge L constant
    buying_width physical_width budget_width allowance_width ratio_width).mono
    (show databaseWordBudget n h L ≤ K by dsimp[K,coreWords];omega)
  have inclusion_words := (includedRows_words database L ratio_ge ratio_width).mono
    (show StoredServe.logarithmWordBudget h L+3*h+10 ≤ K by dsimp[K,coreWords];omega)
  have row_bound : included.length ≤ maximumRows h := includedRows_length_bound database ratio_ge
  have count_bound : cached.1 ≤ maximumRows h := (rowsVector_length included).trans_le row_bound
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  have cache_words := (rowsVector_words included).mono
    (show included.length+h+UpperBound.gridDepth h ratio+5 ≤ K by dsimp[K,coreWords];omega)
  have helper_words := (MaterializedHelper.nodes_words buying opening budget database cached.2 A (by omega) ratio_ge
    (fun v => (buying_width v).trans LA) (fun v => (opening_width v).trans LA) (budget_width.trans LA) radii tolls).mono
    ((nodeWords_mono n h A count_bound).trans (show MaterializedHelper.nodeWords n h (maximumRows h) A ≤ K by dsimp[K,coreWords,A];omega))
  have executed_words := (execute_words input buying physical budget allowance source target active ratio r seed helper.value L constant ratio_ge
    buying_width physical_width budget_width allowance_width ratio_width r_width).mono
    (show executionWords n h L ≤ K by dsimp[K,coreWords];omega)
  simp only[run,Traced.bind_events,Traced.bind_value,wordsWithin_append]
  exact ⟨database_words,inclusion_words,cache_words,helper_words,executed_words⟩

end BuyAtBulk.Computation.Runtime.StoredCore
