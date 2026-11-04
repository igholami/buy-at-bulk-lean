import BuyAtBulk.Computation.Runtime.ZeroPhase
import BuyAtBulk.Computation.Runtime.CoreOutputBound

namespace BuyAtBulk.Computation.Runtime.StoredRounding
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem freeRoutes_length (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (state : StoredState.State input.graph) (order : List (Fin h)) :
    ∀ entries, (freeRoutes input physical source target lengths state order).value=some entries → entries.length=order.length := by
  induction order with
  | nil => intro entries result;simpa [freeRoutes,emit] using result.symm
  | cons i rest ih =>
    intro entries result
    simp only[freeRoutes] at result
    split at result
    · contradiction
    · split at result
      · contradiction
      · rename_i path found tail later
        have equal := Option.some.inj result
        subst entries
        simp only[List.length_cons,ih tail later]

theorem zeroRaw_output_bound (buying physical opening : Vector ℚ n)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    resultLength (zeroRaw input buying physical opening source target lengths).value ≤ h := by
  simp only[zeroRaw]
  split
  · simp only[transport_length]
    have length := StoredCore.requestOrder_length (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value
    cases routes : (freeRoutes (zeroInput input physical).value (constantVector n (0 : ℚ) 3).value
      source (zeroTarget source target lengths).value (constantVector h (0 : ℚ) 3).value
      (zeroState (zeroInput input physical).value buying).value
      (StoredCore.requestOrder (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value).value).value with
    | none => simp[resultLength]
    | some entries =>
      simp only[Option.map_some,resultLength]
      exact (freeRoutes_length _ _ _ _ _ _ _ _ routes).trans_le length
  · simp only[transport_length]
    exact StoredCore.run_output_bound _ _ _ _ _ _ _ _ _ _ _ _ _

theorem zeroRun_output_bound (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    resultLength (zeroRun input buying physical opening budget source target lengths).value ≤ h := by
  have raw := zeroRaw_output_bound input buying physical opening source target lengths
  simp only[zeroRun]
  split
  · simp[resultLength]
  · split
    · simp[resultLength]
    · rename_i state entries result
      simpa only[result,resultLength] using raw

end BuyAtBulk.Computation.Runtime.StoredRounding
