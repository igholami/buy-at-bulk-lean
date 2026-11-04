import BuyAtBulk.Computation.Runtime.OriginalProgram

/-! The computed graph-only output is an approximation to every integral
purchased network with supported original routes. Singleton path measures give
the precise natural-LP relaxation, preserving both original resource budgets. -/
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.Computation.StoredOriginal
variable {n resources requests : ℕ} (tables : Tables n resources requests)

structure IntegralInput where
  bought : Vector Bool resources
  route : ∀ i : Fin requests, tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)
  supported : ∀ i a, OriginalPipeline.usesResource tables.graphData i (route i) a=true → bought[a.val]=true

namespace IntegralInput
variable {tables}

def buying (input : IntegralInput tables) : ℚ :=
  ∑ a : Fin resources, if input.bought[a.val] then tables.buying[a.val] else 0

def rental (input : IntegralInput tables) : ℚ :=
  ∑ i : Fin requests, tables.demand[i.val]*OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length i (input.route i)

def fractional (input : IntegralInput tables) : OriginalPipeline.OriginalFractional tables.graphData where
  opening a := if input.bought[a.val] then 1 else 0
  paths i := [(1,input.route i)]
  opening_bounds a := by cases input.bought[a.val] <;> norm_num
  nonneg i entry member := by simp only [List.mem_singleton] at member; subst entry; norm_num
  unit i := by simp
  capacity i a := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    by_cases used : OriginalPipeline.usesResource tables.graphData i (input.route i) a=true
    · simp [used,input.supported i a used]
    · simp only [used,ite_false]
      cases input.bought[a.val] <;> norm_num

@[simp] theorem fractional_buying (input : IntegralInput tables) :
    OriginalPipeline.buyingBudget tables.graphData input.fractional=input.buying := by
  simp only [OriginalPipeline.buyingBudget,fractional,buying]
  apply Finset.sum_congr rfl
  intro a _
  cases input.bought[a.val] <;> simp [Tables.graphData]

@[simp] theorem fractional_rental (input : IntegralInput tables) :
    OriginalPipeline.rentalBudget tables.graphData input.fractional=input.rental := by
  simp [OriginalPipeline.rentalBudget,OriginalPipeline.fractionalLength,fractional,rental,Tables.graphData]

end IntegralInput

/-- Approximation to every integral graph solution, for the actual computed
original routing and resource flags. The program takes only graph tables. -/
theorem closedRun_integral (output : StoredOriginalOutput tables)
    (returned : closedRun tables=.ok output) (input : IntegralInput tables) :
    ((outputBuying tables output+outputRental tables output : ℚ) : ℝ) ≤
      2500000000*Statements.optimizedFactor requests*(input.buying+input.rental) := by
  have correct := closedRun_correct tables
  rw [returned] at correct
  change SourceSpec tables (.ok (some output)) at correct
  have bound := correct.2.2 input.fractional
  simpa only [IntegralInput.fractional_buying,IntegralInput.fractional_rental] using bound

/-- A reported disconnected request rules out every integral bought network. -/
theorem closedRun_error_no_integral (i : Fin requests) (returned : closedRun tables=.error i) :
    ¬Nonempty (IntegralInput tables) := by
  have correct := closedRun_correct tables
  rw [returned] at correct
  change SourceSpec tables (.error i) at correct
  rintro ⟨input⟩
  exact correct.2 ⟨input.fractional⟩

/-- The graph-only approximation guarantee against every integral comparator. -/
def IntegralGraphApproximationTarget : Prop :=
  ∀ (n resources requests : ℕ) (tables : Tables n resources requests),
    (∀ (output : StoredOriginalOutput tables), closedRun tables=.ok output →
      ∀ input : IntegralInput tables,
      ((outputBuying tables output+outputRental tables output : ℚ) : ℝ) ≤
        2500000000*Statements.optimizedFactor requests*(input.buying+input.rental)) ∧
    (∀ i : Fin requests, closedRun tables=.error i → ¬Nonempty (IntegralInput tables))

theorem integral_graph_approximation : IntegralGraphApproximationTarget := by
  intro n resources requests tables
  exact ⟨closedRun_integral tables,closedRun_error_no_integral tables⟩

end BuyAtBulk.Computation.Runtime.Original
