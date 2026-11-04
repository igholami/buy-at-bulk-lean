import BuyAtBulk.Computation.Runtime.OriginalRoundPrepared
import BuyAtBulk.Computation.Runtime.OriginalInitialization
import BuyAtBulk.UpperBound.Optimization.Factors

/-! Graph-only original program: actual connectivity initialization, cached
node reduction, exact stored LP solve, optimized rounding and typed projection. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal BuyAtBulk.UpperBound
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def sourceRun : Except (Fin requests) (Option (StoredOriginalOutput tables)) :=
  match initializeChecked tables with
  | .error i=>.error i
  | .ok _=>
    let prepared := (cachedBuffers tables).value
    match solvePrepared tables prepared with
    | none=>.ok none
    | some point=>.ok (roundPrepared tables prepared rfl point).value

def SourceSpec : Except (Fin requests) (Option (StoredOriginalOutput tables))→Prop
  | .error i=>
    ¬Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) ∧
      ¬Nonempty (OriginalPipeline.OriginalFractional tables.graphData)
  | .ok none=>False
  | .ok (some output)=>
    (output.routes.map fun e=>e.1).Perm (List.finRange requests) ∧
    (∀ e∈output.routes,∀ a,OriginalPipeline.usesResource tables.graphData e.1 e.2 a=true → output.bought[a.val]=true) ∧
    ∀ fractional : OriginalPipeline.OriginalFractional tables.graphData,
      ((outputBuying tables output+outputRental tables output : ℚ) : ℝ) ≤
        2500000000*Statements.optimizedFactor requests*
          (OriginalPipeline.buyingBudget tables.graphData fractional+OriginalPipeline.rentalBudget tables.graphData fractional)

theorem sourceRun_correct : SourceSpec tables (sourceRun tables) := by
  cases initialized : initializeChecked tables with
  | error i=>
    have correct := initializeChecked_correct tables
    simp only [initialized] at correct
    simpa only [sourceRun,initialized,SourceSpec] using And.intro correct.1 correct.2.1
  | ok fractional=>
    let prepared := (cachedBuffers tables).value
    obtain ⟨point,solved,optimal,matching,coordinates,_,minimal⟩ := solvePrepared_correct tables prepared rfl fractional
    obtain ⟨output,rounded,buying,rental,indices,support⟩ := roundPrepared_correct tables prepared rfl optimal matching point coordinates
    have returned : sourceRun tables=.ok (some output) := by
      simp only [sourceRun,initialized]
      change (match solvePrepared tables prepared with
        | none=>Except.ok none
        | some point=>Except.ok (roundPrepared tables prepared rfl point).value)=_
      rw [solved]
      dsimp only
      rw [rounded]
    rw [returned]
    refine ⟨indices,support,?_⟩
    intro original
    have Bnonneg : (0 : ℚ) ≤ optimal.buyingBudget :=
      Finset.sum_nonneg (fun v _=>mul_nonneg (optimal.buying_nonneg v) (optimal.opening_bounds v).1)
    have Rnonneg : (0 : ℚ) ≤ optimal.rentalBudget := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (optimal.demand_pos i).le
      exact Finset.sum_nonneg (fun v _=>mul_nonneg (optimal.physical_nonneg v) (optimal.node_nonneg i v))
    have Breal : (0 : ℝ) ≤ optimal.buyingBudget := by exact_mod_cast Bnonneg
    have Rreal : (0 : ℝ) ≤ optimal.rentalBudget := by exact_mod_cast Rnonneg
    have factors := Optimization.optimized_parameter_bounds requests
    have Bbound : (outputBuying tables output : ℝ) ≤
        2500000000*Statements.optimizedFactor requests*(optimal.buyingBudget : ℝ) := calc
      _ ≤ 500000*Statements.buyingFactor requests (Optimization.scaleRatio requests) (Optimization.r requests)*optimal.buyingBudget := buying
      _ ≤ 500000*(5000*Statements.optimizedFactor requests)*(optimal.buyingBudget : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left factors.1 (by norm_num)) Breal
      _ = _ := by ring
    have Rbound : (outputRental tables output : ℝ) ≤
        2500000000*Statements.optimizedFactor requests*(optimal.rentalBudget : ℝ) := calc
      _ ≤ 500000*((Optimization.r requests : ℝ)*Statements.gridLevels requests (Optimization.scaleRatio requests))*optimal.rentalBudget := rental
      _ ≤ 500000*(5000*Statements.optimizedFactor requests)*(optimal.rentalBudget : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left factors.2 (by norm_num)) Rreal
      _ = _ := by ring
    have compare : ((optimal.buyingBudget+optimal.rentalBudget : ℚ) : ℝ) ≤
        (OriginalPipeline.buyingBudget tables.graphData original+OriginalPipeline.rentalBudget tables.graphData original) := by
      exact_mod_cast minimal original
    have nonnegative : 0 ≤ Statements.optimizedFactor requests := by
      have bound := Optimization.q_squared_le_optimizedFactor requests
      nlinarith [sq_nonneg (Optimization.q requests : ℝ)]
    calc
      _ = (outputBuying tables output : ℝ)+(outputRental tables output : ℝ) := by push_cast;rfl
      _ ≤ 2500000000*Statements.optimizedFactor requests*(optimal.buyingBudget : ℝ)+
          2500000000*Statements.optimizedFactor requests*(optimal.rentalBudget : ℝ) := add_le_add Bbound Rbound
      _ = 2500000000*Statements.optimizedFactor requests*((optimal.buyingBudget+optimal.rentalBudget : ℚ) : ℝ) := by push_cast;ring
      _ ≤ _ := mul_le_mul_of_nonneg_left compare (by positivity)

/-- Public graph-only interface: a genuine disconnected index or a fully
computed original routing. The internal `none` state has been proved impossible. -/
def closedRun : Except (Fin requests) (StoredOriginalOutput tables) :=
  match returned : sourceRun tables with
  | .error i=>.error i
  | .ok result=>
    have present : result.isSome := by
      have correct := sourceRun_correct tables
      rw [returned] at correct
      cases result with
      | none=>exact False.elim correct
      | some output=>rfl
    .ok (result.get present)

theorem closedRun_map : (closedRun tables).map some=sourceRun tables := by
  unfold closedRun
  split
  · rename_i i returned
    exact returned.symm
  · rename_i result returned
    have correct := sourceRun_correct tables
    rw [returned] at correct
    cases result with
    | none=>exact False.elim correct
    | some output=>exact returned.symm

def ClosedSpec (result : Except (Fin requests) (StoredOriginalOutput tables)) : Prop :=
  SourceSpec tables (result.map some)

theorem closedRun_correct : ClosedSpec tables (closedRun tables) := by
  rw [ClosedSpec,closedRun_map]
  exact sourceRun_correct tables

end BuyAtBulk.Computation.Runtime.Original
