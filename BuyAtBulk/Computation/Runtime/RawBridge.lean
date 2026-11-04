import BuyAtBulk.Computation.Runtime.Expression
import BuyAtBulk.Computation.Runtime.Primitive

/-! The helper's concrete signed-integer instruction trace in the common
closed operation vocabulary. This conversion preserves every operation and
records the signed binary width of every actual integer operand/result. -/
namespace BuyAtBulk.Computation.Runtime.RawBridge

def operation : RawExpression.Operation → Runtime.Operation
  | .read => .read
  | .write => .write
  | .add => .intAdd
  | .mul => .intMul
  | .neg => .intNeg
  | .equal | .less | .le => .intCompare
  | .branch => .branch
  | .dispatch => .scan
  | .pair => .cons

def event (source : RawExpression.Event) : Runtime.Event :=
  ⟨operation source.operation,source.values.map fun z => z.natAbs.size+1⟩

def trace {α : Type} (result : RawExpression.Result α) : Traced α :=
  ⟨result.value,result.events.map event⟩

@[simp] theorem trace_value {α : Type} (result : RawExpression.Result α) :
    (trace result).value=result.value := rfl

@[simp] theorem trace_count {α : Type} (result : RawExpression.Result α) :
    (trace result).events.length=result.events.length := List.length_map _

theorem trace_words {α : Type} (result : RawExpression.Result α) (B : ℕ)
    (bounded : RawExpression.EventsBounded result.events B) :
    WordsWithin (B+1) (trace result).events := by
  intro entry member word present
  change entry∈result.events.map event at member
  obtain ⟨source,sourcePresent,rfl⟩ := List.mem_map.mp member
  change word∈source.values.map (fun z => z.natAbs.size+1) at present
  obtain ⟨z,valuePresent,rfl⟩ := List.mem_map.mp present
  exact Nat.add_le_add_right (Nat.size_le.mpr (bounded source sourcePresent z valuePresent)) 1

end BuyAtBulk.Computation.Runtime.RawBridge
