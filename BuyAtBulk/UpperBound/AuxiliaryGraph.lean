import BuyAtBulk.UpperBound.AuxiliaryGraph.TraceGirth
import BuyAtBulk.UpperBound.AuxiliaryGraph.Counts
import BuyAtBulk.UpperBound.AuxiliaryGraph.NoLoops

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Every final stored edge comes from an actual logged insertion. -/
theorem final_edge_event {physical : V → ℚ} {Q : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = [])
    (edge : AuxiliaryEdge G) (member : edge ∈ after.edges) :
    ∃ event ∈ events, event.edge = edge := by
  rw [AuxiliaryTrace.edge_list G trace, empty, List.append_nil] at member
  simp only [List.mem_reverse] at member
  exact List.mem_map.mp member

/-- The logged insertion count at each scale equals the final stored-record
count, since unlogged progress inserts no edges and the initial log is empty. -/
theorem event_count_scale {physical : V → ℚ} {Q : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = [])
    (scale : ℚ) : (events.filter fun event => event.edge.scale = scale).length =
      (after.edges.filter fun edge => edge.scale = scale).length := by
  have hmap : ((events.map AuxiliaryEvent.edge).filter fun edge => edge.scale = scale).length =
      (events.filter fun event => event.edge.scale = scale).length := by
    clear trace
    induction events with
    | nil => rfl
    | cons event tail ih =>
      by_cases he : event.edge.scale = scale <;> simp [he, ih]
  rw [AuxiliaryTrace.edge_list G trace, empty, List.append_nil,
    List.filter_reverse, List.length_reverse]
  exact hmap.symm

/-- Eligibility of each actual final auxiliary endpoint follows from its
insertion guard and monotonic center records along the execution trace. -/
theorem final_edges_eligible {physical : V → ℚ} {Q : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = []) :
    EdgesEligible G after := by
  intro edge member
  obtain ⟨event, hevent, rfl⟩ := final_edge_event trace empty edge member
  have guard := AuxiliaryTrace.guards G trace event hevent
  have stateSuffix := AuxiliaryTrace.event_suffix G trace event hevent
  exact ⟨eligible_of_records_sublist event.after.centers after.centers stateSuffix.2 _ _ guard.2.2.2.1,
    eligible_of_records_sublist event.after.centers after.centers stateSuffix.2 _ _ guard.2.2.2.2.1⟩

/-- Source auxiliary graph girth, birth-count vertex bound, and actual paid
insertion bound, derived from the physical chronological execution trace.
The event nonloop side condition is proved by the branch extraction theorems;
no simplicity, girth, or edge-count conclusion is assumed here. -/
theorem trace_auxiliary_bound {physical buying : V → ℚ}
    (physical_nonneg : ∀ v, 0 ≤ physical v) {Q ratio : ℚ} {r h : ℕ}
    (hr : 1 ≤ r) (hQ : 6 * (r : ℚ) ≤ Q)
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = [])
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (bounds : ∀ event ∈ events, AuxiliaryBounds G buying physical ratio event)
    (distinct : ∀ event ∈ events, event.edge.source ≠ event.edge.target)
    (centers_bound : after.centers.length ≤ 2 * h) :
    ∀ scale : ℚ,
      Girth.HighGirth (activeGraph after.edges scale) r ∧
      (activeVertices after.edges scale).card ≤
        min (2 * h) (after.centers.filter fun record => scale ≤ record.birthScale).length ∧
      (after.edges.filter fun edge => edge.scale = scale).length =
        Nat.card (activeGraph after.edges scale).edgeSet ∧
      ((after.edges.filter fun edge => edge.scale = scale).length : ℝ) ≤
        (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) *
          ((after.centers.filter fun record => scale ≤ record.birthScale).length : ℝ) := by
  obtain ⟨girth, nodup⟩ := trace_highGirth_nodup physical_nonneg hr hQ trace empty sorted bounds distinct
  have eligible := final_edges_eligible trace empty
  have edgeDistinct : ∀ edge ∈ after.edges, edge.source ≠ edge.target := by
    intro edge member
    obtain ⟨event, hevent, rfl⟩ := final_edge_event trace empty edge member
    exact distinct event hevent
  intro scale
  classical
  have hbirths := active_card_le_births after eligible scale
  have htotal : (activeVertices after.edges scale).card ≤ 2 * h :=
    hbirths.trans ((List.length_filter_le _ _).trans centers_bound)
  have hactive : Girth.HighGirth (activeGraph after.edges scale) r :=
    Girth.highGirth_induce (girth scale) (activeVertices after.edges scale : Set V)
  have hcount := paid_count_eq_edges after.edges scale edgeDistinct (nodup scale)
  refine ⟨hactive, le_min htotal hbirths, hcount, ?_⟩
  rw [hcount]
  apply auxiliary_edge_count (activeGraph after.edges scale) hr hactive
  · simpa only [activeGraph_vertices_card] using htotal
  · simpa only [activeGraph_vertices_card] using hbirths

/-- Direct source form with nonloops derived from free center records and the
initial purchase of all zero-buying nodes, rather than assumed for the log. -/
theorem trace_paid_bound_of_free {physical buying : V → ℚ}
    (physical_nonneg : ∀ v, 0 ≤ physical v) {Q ratio : ℚ} {r h : ℕ}
    (hr : 1 ≤ r) (hQ : 6 * (r : ℚ) ≤ Q)
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = [])
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (bounds : ∀ event ∈ events, AuxiliaryBounds G buying physical ratio event)
    (births : BirthEdgesNonloop G events)
    (zero_bought : ∀ v, buying v = 0 → v ∈ before.bought)
    (centers_free : ∀ record ∈ after.centers,
      buying record.endpoint = 0 ∧ physical record.endpoint = 0)
    (centers_bound : after.centers.length ≤ 2 * h) :
    ∀ scale : ℚ, ((after.edges.filter fun edge => edge.scale = scale).length : ℝ) ≤
      (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) *
        ((after.centers.filter fun record => scale ≤ record.birthScale).length : ℝ) := by
  have Q_nonneg : 0 ≤ Q := (show (0 : ℚ) ≤ 6 * (r : ℚ) by positivity).trans hQ
  have distinct := trace_nonloops trace births zero_bought centers_free Q_nonneg
    (fun event he => (bounds event he).1.le)
  intro scale
  exact (trace_auxiliary_bound physical_nonneg hr hQ trace empty sorted bounds distinct centers_bound scale).2.2.2

end BuyAtBulk.UpperBound.AuxiliaryGraph
