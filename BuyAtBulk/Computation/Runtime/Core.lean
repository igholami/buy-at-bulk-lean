import BuyAtBulk.Computation.Runtime.CoreExecution
import BuyAtBulk.Computation.Runtime.CoreHelperInput
import BuyAtBulk.Computation.Runtime.CoreDatabaseWords
import BuyAtBulk.Computation.Runtime.HelperNodesWords
import BuyAtBulk.Computation.Runtime.Schedule
import BuyAtBulk.Computation.Core.Algorithm
import Mathlib.Tactic.GCongr

/-! Complete stored core: original rows, actual inclusion/cache, coefficient
construction and conditional expectations, Boolean initialization, stable
request sort, parameter arithmetic, and every served stored route. -/
namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def run (buying physical opening : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n)
    (ratio_ge : 2 ≤ ratio) : Traced (Option (StoredState.State input.graph × List (StoredBatch.Entry input source target))) := do
  let database ← materializeRows input buying physical budget allowance source target ratio ratio_ge
  let included ← includedRows database ratio_ge
  let cached ← rowsVector included
  let helper ← MaterializedHelper.nodes buying opening budget database cached.2
  execute input buying physical budget allowance source target active ratio r seed helper

theorem run_value (buying physical opening : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) :
    StoredBatch.decodeOption input source target (run input buying physical opening budget allowance source target active ratio r seed ratio_ge).value=
      Computation.Core.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) (fun v => opening[v.val]) budget
        (fun i => allowance[i.val]) (fun i => source[i.val]) (fun i => target[i.val]) (StoredState.boughtSet active) ratio r (StoredState.boughtSet seed) := by
  let database := (materializeRows input buying physical budget allowance source target ratio ratio_ge).value
  let included := (includedRows database ratio_ge).value
  let cached := (rowsVector included).value
  have image : (List.finRange cached.1).map (fun i => cached.2[i.val])=Computation.Core.includedRows database :=
    (rowsVector_image included).trans (includedRows_value database ratio_ge)
  have helper := MaterializedHelper.nodes_source buying opening budget database cached.2 image
  simp only[run,Traced.bind_value]
  rw[execute_value (ratio_ge:=ratio_ge)]
  simp only[Computation.Core.run,Computation.Core.initialState]
  rw[←materializeRows_value input buying physical budget allowance source target ratio ratio_ge]
  rw[helper]


def maximumRows (h : ℕ) := 4*h*(h+1)

theorem includedRows_length_bound {ratio : ℕ} (database : Core.RowDatabase h ratio n) (ratio_ge : 2 ≤ ratio) :
    (includedRows database ratio_ge).value.length ≤ maximumRows h := by
  rw[includedRows_value]
  exact Runtime.row_schedule_polynomial database ratio_ge

theorem nodeCount_mono (n h : ℕ) {m M : ℕ} (bounded : m ≤ M) :
    MaterializedHelper.nodeCount n h m ≤ MaterializedHelper.nodeCount n h M := by
  unfold MaterializedHelper.nodeCount MaterializedHelper.tableCount
  gcongr


def coreCount (n h : ℕ) := databaseCount n h+(rawRowsCount h+8*(2*h*(2*h+2))+1)+
  (8*maximumRows h+3)+MaterializedHelper.nodeCount n h (maximumRows h)+executionCount n h (2*n)

theorem run_count (buying physical opening : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) :
    (run input buying physical opening budget allowance source target active ratio r seed ratio_ge).events.length ≤ coreCount n h := by
  let database := (materializeRows input buying physical budget allowance source target ratio ratio_ge).value
  let included := (includedRows database ratio_ge).value
  let cached := (rowsVector included).value
  let helper := MaterializedHelper.nodes buying opening budget database cached.2
  have database_count := materializeRows_count input buying physical budget allowance source target ratio ratio_ge
  have included_count := includedRows_count database ratio_ge
  have cache_count := rowsVector_count included
  have rows_bound : cached.1 ≤ maximumRows h := (rowsVector_length included).trans_le (includedRows_length_bound database ratio_ge)
  have cache_bound : included.length ≤ maximumRows h := includedRows_length_bound database ratio_ge
  have helper_count := (MaterializedHelper.nodes_count buying opening budget database cached.2).trans (nodeCount_mono n h rows_bound)
  have helper_length : helper.value.length ≤ 2*n := MaterializedHelper.nodes_length buying opening budget database cached.2
  have executed := execute_count input buying physical budget allowance source target active ratio r seed helper.value ratio_ge
  have execution_mono : executionCount n h helper.value.length ≤ executionCount n h (2*n) := by
    unfold executionCount
    gcongr
  have executed_bound := executed.trans execution_mono
  simp only[run,Traced.bind_events,Traced.bind_value,List.length_append]
  unfold coreCount
  dsimp only[database,included,cached,helper] at included_count cache_count helper_count executed_bound cache_bound
  omega

end BuyAtBulk.Computation.Runtime.StoredCore
