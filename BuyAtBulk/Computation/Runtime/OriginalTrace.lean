import BuyAtBulk.Computation.Runtime.OriginalProgram
import BuyAtBulk.Computation.Runtime.OriginalSolveTrace

/-! The fully closed original computation trace. It executes initialization,
cached reduction, the concrete LP frontend/optimizer, rounding and projection. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Original
variable {n resources requests : ℕ} (tables : BuyAtBulk.Computation.StoredOriginal.Tables n resources requests)

def sourceTrace : Traced (Except (Fin requests) (Option (StoredOriginalOutput tables))) :=
  let initialized := initializeCheckedTrace tables
  match initialized.value with
  | .error i=>⟨.error i,initialized.events++[⟨.branch,[1]⟩,⟨.write,[i.val.size]⟩]⟩
  | .ok _=>
    let prepared := cachedBuffers tables
    let solved := solvePreparedTrace tables prepared.value
    match solved.value with
    | none=>⟨.ok none,initialized.events++[⟨.branch,[1]⟩]++prepared.events++solved.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
    | some point=>
      let rounded := roundPrepared tables prepared.value rfl point
      ⟨.ok rounded.value,initialized.events++[⟨.branch,[1]⟩]++prepared.events++solved.events++[⟨.branch,[1]⟩]++rounded.events++[⟨.write,[1]⟩]⟩

theorem sourceTrace_value : (sourceTrace tables).value=sourceRun tables := by
  unfold sourceTrace
  dsimp only
  rw [initializeCheckedTrace_value]
  unfold sourceRun
  cases initialized : BuyAtBulk.Computation.StoredOriginal.initializeChecked tables with
  | error i=>rfl
  | ok fractional=>
    dsimp only
    rw [solvePreparedTrace_value]
    cases solved : solvePrepared tables (cachedBuffers tables).value <;> rfl

theorem sourceTrace_correct : SourceSpec tables (sourceTrace tables).value := by
  rw [sourceTrace_value]
  exact sourceRun_correct tables

def closedTrace : Traced (Except (Fin requests) (StoredOriginalOutput tables)) :=
  let result := sourceTrace tables
  match returned : result.value with
  | .error i=>⟨.error i,result.events++[⟨.branch,[1]⟩,⟨.write,[i.val.size]⟩]⟩
  | .ok output=>
    have present : output.isSome := by
      have correct := sourceTrace_correct tables
      rw [returned] at correct
      cases output with
      | none=>exact False.elim correct
      | some value=>rfl
    ⟨.ok (output.get present),result.events++[⟨.branch,[1]⟩,⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩

theorem closedTrace_map : (closedTrace tables).value.map some=(sourceTrace tables).value := by
  unfold closedTrace
  dsimp only
  split
  · rename_i i returned
    exact returned.symm
  · rename_i output returned
    have correct := sourceTrace_correct tables
    rw [returned] at correct
    cases output with
    | none=>exact False.elim correct
    | some value=>exact returned.symm

private theorem map_some_injective {α β : Type} : Function.Injective (@Except.map α β (Option β) some) := by
  intro a b same
  cases a <;> cases b <;> simp_all [Except.map]

theorem closedTrace_value : (closedTrace tables).value=closedRun tables := by
  apply map_some_injective
  rw [closedTrace_map,sourceTrace_value,closedRun_map]

theorem closedTrace_correct : ClosedSpec tables (closedTrace tables).value := by
  rw [closedTrace_value]
  exact closedRun_correct tables

end BuyAtBulk.Computation.Runtime.Original
