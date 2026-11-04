import BuyAtBulk.UpperBound.MainChoice
import BuyAtBulk.UpperBound.InheritedArm

/-! Endpoint assignment in Algorithm `alg:main`. Both endpoints are assigned
before any path is bought. A new endpoint record has a zero-cost nil arm. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

inductive CenterAssignment (buying physical : V → ℚ) (allowance scale : ℚ) (z : V) :
    RoundingState G → RoundingState G → Bool → (center : V) → G.Path z center → Prop where
  | existing (state : RoundingState G) (center : V) (arm : G.Path z center)
      (eligible : EligibleCenter state.centers center scale)
      (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance scale) arm)
      (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
        arm.val ≤ scale / 8) :
      CenterAssignment buying physical allowance scale z state state false center arm
  | birth (state : RoundingState G)
      (separated : ¬ ∃ center, NearEligibleCenter G buying physical state allowance scale z center) :
      CenterAssignment buying physical allowance scale z state (recordBirth G state z scale) true z SimpleGraph.Path.nil

namespace CenterAssignment

theorem bought_eq {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm) :
    after.bought = before.bought := by cases assignment <;> rfl

theorem edges_eq {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm) :
    after.edges = before.edges := by cases assignment <;> rfl

theorem birth_details {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after true center arm) :
    center = z ∧ after = recordBirth G before z scale ∧
      ¬ ∃ v, NearEligibleCenter G buying physical before allowance scale z v := by
  cases assignment with
  | birth separated => exact ⟨rfl, rfl, separated⟩

theorem centers_preserved {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm) :
    before.centers.Sublist after.centers := by
  cases assignment
  · exact List.Sublist.refl _
  · exact List.sublist_cons_self _ _

theorem at_most_one_birth {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm) :
    after.centers.length ≤ before.centers.length + 1 := by
  cases assignment <;> simp [recordBirth]

theorem existing_eq {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after false center arm) :
    after = before := by cases assignment; rfl

theorem eligible_after {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm) :
    EligibleCenter after.centers center scale := by
  cases assignment with
  | existing => assumption
  | birth => exact eligible_of_birth _ _ _

theorem arm_short {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm)
    (terminal_buying : buying z = 0) (terminal_physical : physical z = 0) (scale_nonneg : 0 ≤ scale) :
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical before allowance scale) arm.val ≤ scale / 8 := by
  cases assignment with
  | existing => assumption
  | birth =>
    simp [NodeMetric.walkWeight, SimpleGraph.Path.nil, mixedNodeWeight, terminal_buying, terminal_physical,
      div_nonneg scale_nonneg (by norm_num : (0:ℚ) ≤ 8)]

theorem physical_arm_bound {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (allowance_pos : 0 < allowance) (scale_pos : 0 < scale)
    (terminal_buying : buying z = 0) (terminal_physical : physical z = 0) :
    NodeMetric.walkWeight G physical arm.val ≤ allowance / 8 := by
  exact near_arm_physical_bound G buying physical buying_nonneg before allowance scale allowance_pos scale_pos arm
    (CenterAssignment.arm_short G assignment terminal_buying terminal_physical scale_pos.le)

theorem assignment_total (buying physical : V → ℚ) (allowance scale : ℚ) (z : V)
    (state : RoundingState G) :
    ∃ final born center arm, CenterAssignment G buying physical allowance scale z state final born center arm := by
  classical
  by_cases nearby : ∃ center, NearEligibleCenter G buying physical state allowance scale z center
  · obtain ⟨center, eligible, candidate, candidate_short⟩ := nearby
    obtain ⟨arm, shortest, no_longer⟩ := exists_shortest_no_longer G
      (mixedNodeWeight G buying physical state allowance scale) candidate
    exact ⟨_, _, _, _, CenterAssignment.existing state center arm eligible shortest (no_longer.trans candidate_short)⟩
  · exact ⟨_, _, _, _, CenterAssignment.birth state nearby⟩

end CenterAssignment
end BuyAtBulk.UpperBound
