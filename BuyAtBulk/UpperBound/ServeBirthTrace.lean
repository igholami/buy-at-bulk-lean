import BuyAtBulk.UpperBound.ServeExecution
import BuyAtBulk.UpperBound.CenterAssignmentBirthTrace
import BuyAtBulk.UpperBound.RequestBirthMetadata

/-! Every actual center birth of a served request is logged with its original
mate, physical allowance, common-grid scale, and genuine pre-birth state. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace ServeExec

theorem birth_trace {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {threshold : ℚ} {s t : V} {reachable : Nonempty (G.Path s t)}
    {before after : RoundingState G} {route : G.Path s t}
    (budget_pos : 0 < budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (execution : ServeExec G buying physical budget allowance h ratio threshold s t reachable before after route) :
    ∃ events, BirthTrace G buying physical before events after ∧ RequestBirthMetadata budget allowance h ratio s t events := by
  have ratio_pos : 0 < ratio := by omega
  induction execution with
  | already_bought => exact ⟨[], BirthTrace.refl _, by simp [RequestBirthMetadata]⟩
  | no_eligible route not_bought empty shortest =>
    exact ⟨[], BirthTrace.progress (NoBirthProgress.buyPath G before route) (BirthTrace.refl _), by simp [RequestBirthMetadata]⟩
  | cheap not_bought choice small =>
    exact ⟨[], BirthTrace.progress (NoBirthProgress.buyPath G before choice.mainPath) (BirthTrace.refl _), by simp [RequestBirthMetadata]⟩
  | purchase first assigned u v sarm tarm bornS bornT not_bought choice above assignS assignT must_buy =>
    have pair_far := mainChoice_mate_far G buying physical before budget allowance h ratio s t reachable budget_pos ratio_pos choice
    have first_pair_far : ¬ HasShortMixedRoute G buying physical first allowance (gridScale budget ratio choice.index) s t
        (gridScale budget ratio choice.index / 16) := by
      intro near
      exact pair_far ((shortMixedRoute_bought_eq G buying physical before first assignS.bought_eq allowance _ s t _).mpr near)
    have second_mate_far : ¬ HasShortMixedRoute G buying physical first allowance (gridScale budget ratio choice.index) t s
        (gridScale budget ratio choice.index / 16) := by
      intro near
      exact first_pair_far ((shortMixedRoute_symm buying physical first allowance _ s t _).mpr near)
    obtain ⟨eventsS, traceS, metadataS⟩ := CenterAssignment.birth_trace G assignS t pair_far
    obtain ⟨eventsT, traceT, metadataT⟩ := CenterAssignment.birth_trace G assignT s second_mate_far
    have index_lt : choice.index < gridDepth h ratio :=
      active_scale_depth_lt budget h ratio choice.index budget_pos.le h_pos ratio_ge above
    have metaS := RequestBirthMetadata.of_assignment index_lt (show EndpointPair s t s t from Or.inl ⟨rfl, rfl⟩) metadataS
    have metaT := RequestBirthMetadata.of_assignment index_lt (show EndpointPair s t t s from Or.inr ⟨rfl, rfl⟩) metadataT
    have progress := NoBirthProgress.trans G (NoBirthProgress.buyPath G assigned sarm)
      (NoBirthProgress.trans G (NoBirthProgress.buyPath G (buyPath G assigned sarm) choice.mainPath)
        (NoBirthProgress.trans G (NoBirthProgress.buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm)
          (NoBirthProgress.recordEdge G (buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm)
            ((sarm.val.reverse.append choice.mainPath.val).append tarm.val).toPath (gridScale budget ratio choice.index))))
    refine ⟨eventsS ++ eventsT, ?_, RequestBirthMetadata.append metaS metaT⟩
    have trace := BirthTrace.append G (BirthTrace.append G traceS traceT) (BirthTrace.progress progress (BirthTrace.refl _))
    simpa only [List.append_nil] using trace
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    obtain ⟨events, trace, metadata⟩ := AttachmentExec.birth_trace attachS t (Or.inl ⟨rfl, rfl⟩)
    have assigned_eq : assigned = before := assignT.existing_eq.trans assignS.existing_eq
    rw [assigned_eq] at trace
    exact ⟨events, trace, RequestBirthMetadata.of_attachment budget_pos.le h_pos ratio_ge (Or.inl ⟨rfl, rfl⟩) metadata⟩
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    obtain ⟨eventsS, traceS, metadataS⟩ := AttachmentExec.birth_trace attachS t (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨eventsT, traceT, metadataT⟩ := AttachmentExec.birth_trace attachT s (Or.inr ⟨rfl, rfl⟩)
    have trace := BirthTrace.append G traceS traceT
    have assigned_eq : assigned = before := assignT.existing_eq.trans assignS.existing_eq
    rw [assigned_eq] at trace
    have metaS := RequestBirthMetadata.of_attachment budget_pos.le h_pos ratio_ge (show EndpointPair s t s t from Or.inl ⟨rfl, rfl⟩) metadataS
    have metaT := RequestBirthMetadata.of_attachment budget_pos.le h_pos ratio_ge (show EndpointPair s t t s from Or.inr ⟨rfl, rfl⟩) metadataT
    exact ⟨eventsS ++ eventsT, trace, RequestBirthMetadata.append metaS metaT⟩
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    obtain ⟨eventsS, traceS, metadataS⟩ := AttachmentExec.birth_trace attachS t (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨eventsT, traceT, metadataT⟩ := AttachmentExec.birth_trace attachT s (Or.inr ⟨rfl, rfl⟩)
    have trace := BirthTrace.append G traceS traceT
    have assigned_eq : assigned = before := assignT.existing_eq.trans assignS.existing_eq
    rw [assigned_eq] at trace
    have metaS := RequestBirthMetadata.of_attachment budget_pos.le h_pos ratio_ge (show EndpointPair s t s t from Or.inl ⟨rfl, rfl⟩) metadataS
    have metaT := RequestBirthMetadata.of_attachment budget_pos.le h_pos ratio_ge (show EndpointPair s t t s from Or.inr ⟨rfl, rfl⟩) metadataT
    exact ⟨eventsS ++ eventsT, trace, RequestBirthMetadata.append metaS metaT⟩

end ServeExec
end BuyAtBulk.UpperBound
