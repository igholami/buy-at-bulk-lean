import BuyAtBulk.Computation.Serve.Algorithm

/-! The two computed attachment calls implement all three main reuse outcomes.
No existential totality oracle is used to choose either call's output. -/
namespace BuyAtBulk.Computation.Serve
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem reuseArms_refines (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ) (allowance_pos : 0 < allowance) (ratio_pos : 0 < (ratio : ℚ))
    (s t : V) (reachable : Nonempty (G.Path s t)) (state first assigned : RoundingState G)
    (u v : V) (sarm : G.Path s u) (tarm : G.Path t v) (middle : G.Path u v)
    (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
    (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
    (above : cutoff budget h ratio < gridScale budget ratio choice.index)
    (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s state first false u sarm)
    (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned false v tarm)
    (middle_bought : middle.val.support.toFinset ⊆ assigned.bought)
    (middle_short : NodeMetric.walkWeight G physical middle.val ≤ threshold)
    (scale_nonneg : 0 ≤ gridScale budget ratio choice.index / (ratio : ℚ))
    (deadline : (gridScale budget ratio choice.index / (ratio : ℚ)) / (ratio : ℚ) ^ gridDepth h ratio ≤ cutoff budget h ratio) :
    ServeExec G buying physical budget allowance h ratio threshold s t reachable state
      (reuseArms G numbering buying physical budget allowance h ratio threshold (gridScale budget ratio choice.index)
        s t u v sarm tarm middle assigned).1
      (reuseArms G numbering buying physical budget allowance h ratio threshold (gridScale budget ratio choice.index)
        s t u v sarm tarm middle assigned).2 := by
  obtain ⟨afterS, outcomeS, computedS, attachS, _, _⟩ := Attachment.connectEndpoint_correct G numbering buying physical
    buying_nonneg physical_nonneg allowance (cutoff budget h ratio) ratio threshold allowance_pos ratio_pos s t
    (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) scale_nonneg s u sarm assigned deadline
  cases outcomeS with
  | completed completed =>
    simpa only [reuseArms, computedS] using
      ServeExec.completed_first state first assigned afterS u v sarm tarm middle completed not_bought choice above
        assignS assignT middle_bought middle_short attachS
  | arm returnedS =>
    obtain ⟨final, outcomeT, computedT, attachT, _, _⟩ := Attachment.connectEndpoint_correct G numbering buying physical
      buying_nonneg physical_nonneg allowance (cutoff budget h ratio) ratio threshold allowance_pos ratio_pos s t
      (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) scale_nonneg t v tarm afterS deadline
    cases outcomeT with
    | completed completed =>
      simpa only [reuseArms, computedS, computedT] using
        ServeExec.completed_second state first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above
          assignS assignT middle_bought middle_short attachS attachT
    | arm returnedT =>
      simpa only [reuseArms, computedS, computedT] using
        ServeExec.reused state first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above
          assignS assignT middle_bought middle_short attachS attachT

end BuyAtBulk.Computation.Serve
