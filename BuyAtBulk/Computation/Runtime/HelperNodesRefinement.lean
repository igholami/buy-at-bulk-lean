import BuyAtBulk.Computation.Runtime.HelperNodes

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio m : ℕ}

theorem selection_eq (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m)
    (rowImage : (List.finRange m).map (fun r => rows[r.val])=Core.includedRows database) :
    (HelperEvaluation.original (SourceCoefficients.tables buying opening budget database rows).tables [] (List.finRange n)).1=
      (Core.chooseHelper (Equiv.refl _) (fun v => buying[v.val]) (fun v => opening[v.val]) budget database).1 := by
  have mapped := Core.chooseScheduled_mapRows (fun v : Fin n => buying[v.val])
    (Core.helperProbability (fun v : Fin n => opening[v.val]) h)
    (Core.helperFactor (Equiv.refl (Fin n)) database)
    (Core.helperAmplitude (Equiv.refl (Fin n)) (fun v => opening[v.val]) database)
    (Core.helperFixedCost (Equiv.refl (Fin n)) (fun v => buying[v.val]) (fun v => opening[v.val]) h)
    (4*Core.helperAlpha h*budget) (List.finRange m) (fun r => rows[r.val]) [] (List.finRange n)
  rw [rowImage] at mapped
  simpa [HelperEvaluation.original,HelperConstruction.StoredTables.tables,SourceCoefficients.tables,
    Core.chooseHelper,Core.vertexOrder] using congrArg Prod.fst mapped.symm

theorem nodes_source (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m)
    (rowImage : (List.finRange m).map (fun r => rows[r.val])=Core.includedRows database) :
    (nodes buying opening budget database rows).value.toFinset=
      Core.helperNodes (Equiv.refl _) (fun v => buying[v.val]) (fun v => opening[v.val]) budget database := by
  rw [nodes_value,List.toFinset_append,selection_eq buying opening budget database rows rowImage]
  rfl

def nodeCount (n h m : ℕ) := tableCount n h m+(40*h+19)*n+14*(n*(24*(m+1)*(n+1)+2))+2

theorem nodes_count (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    (nodes buying opening budget database rows).events.length≤nodeCount n h m := by
  have table := tables_count buying opening budget database rows
  have heavy := CoefficientPipeline.heavyScan_count opening h (List.finRange n)
  have chosen := CachedHelper.choose_polynomial (SourceCoefficients.tables buying opening budget database rows) [] (List.finRange n)
  have length : (CoefficientPipeline.heavyScan opening h (List.finRange n)).value.length≤n := by
    rw [CoefficientPipeline.heavyScan_value]
    simpa using List.length_filter_le (fun v : Fin n => decide (1≤Core.helperAlpha h*opening[v.val])) (List.finRange n)
  simp only [List.length_finRange,List.length_nil,Nat.zero_add] at heavy chosen
  simp only [nodes,Traced.bind_events,Traced.bind_value,RawBridge.trace_count,RawBridge.trace_value,
    tables_value,indexList_value,indexList_count,List.length_append,appendNodes_count]
  dsimp only [nodeCount]
  nlinarith

end BuyAtBulk.Computation.Runtime.MaterializedHelper
