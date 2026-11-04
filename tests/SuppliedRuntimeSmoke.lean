import BuyAtBulk.Computation.Runtime.SuppliedRounding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Original supplied-LP regression cases use an explicit repeated weighted
path list, rather than precomputed rounding metadata or an optimization oracle. -/
namespace SuppliedRuntimeSmoke
open BuyAtBulk.Computation BuyAtBulk.Computation.StoredOriginal BuyAtBulk.Computation.Runtime

def tables (pathBuying pathLength : ℕ) : Tables 3 3 1 where
  adjacency := #v[#v[false,true,false],#v[true,false,false],#v[false,false,false]]
  symmetric := by decide
  loopless := by decide
  source := #v[0]
  target := #v[1]
  location := #v[Sum.inl 0,Sum.inl 1,Sum.inl 2]
  location_injective := by decide
  location_valid := by intro a; fin_cases a <;> trivial
  buying := #v[0,(pathBuying : ℚ),1]
  length := #v[0,(pathLength : ℚ),1]
  demand := #v[1]
  buying_nonneg := by intro a; fin_cases a <;> simp
  length_nonneg := by intro a; fin_cases a <;> simp
  demand_pos := by decide

def path (b l : ℕ) : (tables b l).graphData.graph.Path 0 1 :=
  ⟨.cons (by rfl) .nil, .mk' (by change ([0,1] : List (Fin 3)).Nodup; decide)⟩

def fractional (b l : ℕ) : Fractional (tables b l) where
  opening := #v[1,1,1]
  entries := [⟨0, (1/3 : ℚ), path b l⟩, ⟨0, (2/3 : ℚ), path b l⟩]
  opening_bounds := by decide
  nonneg := by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num
  unit := by
    intro i
    have same : i = 0 := Subsingleton.elim _ _
    subst i
    norm_num [selectPaths, List.filterMap_cons]
  capacity := by
    intro i a
    have same : i = 0 := Subsingleton.elim _ _
    subst i
    fin_cases a <;> norm_num [selectPaths, List.filterMap_cons, OriginalPipeline.usesResource, tables, path,
      Tables.graphData, SimpleGraph.Walk.support, Fin.ext_iff] <;> split_ifs <;> norm_num

/- The audited counterexample: original B=1 but restricted B0=0. -/
/-- info: some ([true, true, false], [0], 0, 0) -/
#guard_msgs in
#eval ((Supplied.run (tables 0 0) (fractional 0 0) 8 1 (by decide)).value.map fun output =>
  (output.bought.toList, output.routes.map (fun e => e.1.val),
   Original.outputBuying (tables 0 0) output, Original.outputRental (tables 0 0) output))

/- Positive restricted budget: the required paid node is purchased; the
positive-physical isolated resource is excluded from the zero phase. -/
/-- info: some ([true, true, false], [0], 1, 0) -/
#guard_msgs in
#eval ((Supplied.run (tables 1 0) (fractional 1 0) 32 7 (by decide)).value.map fun output =>
  (output.bought.toList, output.routes.map (fun e => e.1.val),
   Original.outputBuying (tables 1 0) output, Original.outputRental (tables 1 0) output))

/- Positive-rental metadata from two fractional weights, with arbitrary
parameters unrelated to the optimized choice. -/
/-- info: true -/
#guard_msgs in
#eval match (Supplied.run (tables 1 2) (fractional 1 2) 32 7 (by decide)).value with
  | none => false
  | some output => output.bought[0] && output.bought[1] &&
      (output.routes.map (fun (e : (tables 1 2).graphData.TaggedPath) => e.1.val) == [0]) &&
      (Original.outputBuying (tables 1 2) output ≤ 2) &&
      (Original.outputRental (tables 1 2) output == 2)

end SuppliedRuntimeSmoke
