import BuyAtBulk.Computation.Runtime.CoreOutputSize
import BuyAtBulk.Computation.Runtime.GraphTransport

namespace BuyAtBulk.Computation.Runtime.StoredRounding
variable {n h : ℕ}

def resultLength {G : SimpleGraph (Fin n)} {source target : Fin h → Fin n} : StoredResult G source target → ℕ
  | none => 0
  | some result => result.2.length

@[simp] theorem transport_length {G H : SimpleGraph (Fin n)} {source target target' : Fin h → Fin n}
    (graph_eq : G=H) (target_eq : target=target') (result : StoredResult G source target) :
    resultLength (transportResult graph_eq target_eq result)=resultLength result := by
  cases graph_eq
  cases target_eq
  rfl

end BuyAtBulk.Computation.Runtime.StoredRounding

namespace BuyAtBulk.Computation.Runtime.StoredCore
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem run_output_bound (buying physical opening : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) :
    StoredRounding.resultLength (run input buying physical opening budget allowance source target active ratio r seed ratio_ge).value ≤ h := by
  cases returned : (run input buying physical opening budget allowance source target active ratio r seed ratio_ge).value with
  | none => simp[StoredRounding.resultLength]
  | some result =>
    rcases result with ⟨after,entries⟩
    exact run_output_length input buying physical opening budget allowance source target active ratio r seed ratio_ge after entries returned

end BuyAtBulk.Computation.Runtime.StoredCore
