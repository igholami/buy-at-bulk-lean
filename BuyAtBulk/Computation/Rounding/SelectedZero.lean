import BuyAtBulk.Computation.Rounding.ZeroPhase
import BuyAtBulk.Computation.Rounding.Accounting

/-! Lemma 6.2 for an arbitrary selected subset, with original h normalization.
The executable adapter retains the verified zero-phase purchases and filters
its actual routes to the requested subset. Empty subsets buy nothing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def selectEntries (source target : Fin h → V) (selected : Finset (Fin h))
    (entries : List (Batch.RouteEntry G source target)) : List (Batch.RouteEntry G source target) :=
  entries.filter fun entry => entry.1 ∈ selected

/-- A subset adapter for the already verified zero phase. Its buying guarantee
uses the original h, even when selected is empty or is a strict subset. -/
def selectedZeroRun (buying physical opening : V → ℚ) (budget : ℚ)
    (source target : Fin h → V) (lengths : Fin h → ℚ) (selected : Finset (Fin h)) :
    Option (Output G source target) :=
  if selected = ∅ then some ⟨∅,[]⟩ else
  if budget = 0 then
    (freeRoutes G numbering physical source target lengths (zeroState G numbering buying) (List.finRange h)).map
      fun entries => ⟨(zeroState G numbering buying).bought,selectEntries G source target selected entries⟩
  else
    (zeroRun G numbering buying physical opening budget source target lengths).map
      fun result => ⟨result.1.bought,selectEntries G source target selected
        (projectZeroEntries G physical source target lengths result.2)⟩

private theorem selectEntries_indices (source target : Fin h → V) (selected : Finset (Fin h))
    (entries : List (Batch.RouteEntry G source target)) :
    (selectEntries G source target selected entries).map (fun entry => entry.1) =
      (entries.map (fun entry => entry.1)).filter (fun i => i ∈ selected) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [selectEntries] at ih
    by_cases mem : entry.1 ∈ selected <;> simp [selectEntries, mem, ih]

private theorem selected_indices {order : List (Fin h)} (selected : Finset (Fin h))
    (unique : order.Nodup) (present : ∀ i ∈ selected,i ∈ order) :
    (order.filter (fun i => i ∈ selected)).Nodup ∧
      (order.filter (fun i => i ∈ selected)).toFinset=selected := by
  refine ⟨unique.filter _,?_⟩
  ext i
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun member=>member.2,fun member=>⟨present i member,member⟩⟩

def SelectedZeroOutput (lp : NodeLP G h) (selected : Finset (Fin h))
    (output : Output G lp.source lp.target) : Prop :=
  (nodeBuying lp.buying output.bought : ℝ) ≤ 490000 * binaryDepth h * lp.buyingBudget ∧
  (output.routes.map fun entry=>entry.1).Nodup ∧
  (output.routes.map fun entry=>entry.1).toFinset=selected ∧
  ∀ entry∈output.routes,entry.2.val.support.toFinset ⊆ output.bought ∧
    NodeMetric.walkWeight G lp.physical entry.2.val=0

/-- Computed arbitrary-subset zero-length rounding, including h=0 and B=0.
No runtime bound or path-selection oracle is a premise. -/
theorem selectedZeroRun_correct (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i,lengths i=lp.fractionalLength i) (selected : Finset (Fin h))
    (zero : ∀ i∈selected,lp.fractionalLength i=0) :
    ∃ output,selectedZeroRun G numbering lp.buying lp.physical lp.opening lp.buyingBudget
      lp.source lp.target lengths selected=some output ∧ SelectedZeroOutput G lp selected output := by
  by_cases empty : selected=∅
  · refine ⟨⟨∅,[]⟩,by simp [selectedZeroRun,empty],?_,by simp,by simp[empty],by simp⟩
    have budget_nonneg : (0 : ℝ) ≤ lp.buyingBudget := by exact_mod_cast lp.buyingBudget_nonneg
    simp only [nodeBuying,Finset.notMem_empty,ite_false,Finset.sum_const_zero,Rat.cast_zero]
    positivity
  by_cases free : lp.buyingBudget=0
  · obtain ⟨entries,computed,indices,bounds⟩ := zero_budget_routes numbering lp free lengths metadata
    let output : Output G lp.source lp.target :=
      ⟨(zeroState G numbering lp.buying).bought,selectEntries G lp.source lp.target selected entries⟩
    have selectedFacts := selected_indices selected (List.nodup_finRange h)
      (fun i _ => List.mem_finRange i)
    refine ⟨output,by simp only [selectedZeroRun,if_neg empty,if_pos free,computed,Option.map_some];rfl,?_,?_,?_,?_⟩
    · change (nodeBuying lp.buying (zeroState G numbering lp.buying).bought : ℝ) ≤ _
      rw [zeroState_buying numbering,free]
      simp
    · simpa only [output,selectEntries_indices,indices] using selectedFacts.1
    · simpa only [output,selectEntries_indices,indices] using selectedFacts.2
    · intro entry member
      have mem := List.mem_filter.mp member
      obtain ⟨supported,bounded⟩ := bounds entry mem.1
      have sel : entry.1∈selected := of_decide_eq_true mem.2
      refine ⟨supported,le_antisymm ?_ ?_⟩
      · simpa only [zero entry.1 sel] using bounded
      · exact Finset.sum_nonneg fun v _=>lp.physical_nonneg v
  · obtain ⟨i,member⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have hh : 0<h := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have positive : 0<lp.buyingBudget := lt_of_le_of_ne lp.buyingBudget_nonneg (Ne.symm free)
    obtain ⟨after,entries,computed,buying,indices,supported,bounds⟩ :=
      zero_phase_correct numbering lp lengths metadata hh positive
    have all_zero : ∀ entry∈entries,lengths entry.1=0 := by
      intro entry mem
      have present : entry.1∈entries.map (fun e=>e.1) := List.mem_map.mpr ⟨entry,mem,rfl⟩
      rw [indices,CoreRun.mem_requestOrder] at present
      exact (Finset.mem_filter.mp present).2
    have projected := projectZeroEntries_indices lp.physical lp.source lp.target lengths entries all_zero
    have present : ∀ i∈selected,i∈CoreRun.requestOrder (zeroActive lengths) (fun _=>1) := by
      intro i mem
      rw [CoreRun.mem_requestOrder]
      simp only [zeroActive,Finset.mem_filter,Finset.mem_univ,true_and,metadata i,zero i mem]
    have selectedFacts := selected_indices selected
      (CoreRun.requestOrder_nodup (zeroActive lengths) (fun _=>1)) present
    let output : Output G lp.source lp.target :=
      ⟨after.bought,selectEntries G lp.source lp.target selected
        (projectZeroEntries G lp.physical lp.source lp.target lengths entries)⟩
    refine ⟨output,by simp only [selectedZeroRun,if_neg empty,if_neg free,computed,Option.map_some];rfl,
      buying,?_,?_,?_⟩
    · simpa only [output,selectEntries_indices,projected,indices] using selectedFacts.1
    · simpa only [output,selectEntries_indices,projected,indices] using selectedFacts.2
    · intro entry mem
      have result := bounds entry (List.mem_filter.mp mem).1
      exact ⟨result.1,result.2.1⟩

/-- The selected actual routes have exactly zero rental cost, for every demand. -/
theorem SelectedZeroOutput.rental_zero (lp : NodeLP G h) (selected : Finset (Fin h))
    (output : Output G lp.source lp.target) (cert : SelectedZeroOutput G lp selected output) :
    rentalCost lp.physical lp.demand output.routes = 0 := by
  rw [rentalCost_eq]
  apply List.sum_eq_zero
  intro q mem
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp mem
  rw [(cert.2.2.2 entry member).2, mul_zero]

/-- Literal support-on-zero-paths form of the paper's subset lemma. -/
theorem selected_zero_rounding (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i,lengths i=lp.fractionalLength i) (selected : Finset (Fin h))
    (supported_zero : ∀ i∈selected,∀ path : G.Path (lp.source i) (lp.target i),
      0<lp.flow i path → NodeMetric.walkWeight G lp.physical path.val=0) :
    ∃ output,selectedZeroRun G numbering lp.buying lp.physical lp.opening lp.buyingBudget
      lp.source lp.target lengths selected=some output ∧ SelectedZeroOutput G lp selected output := by
  apply selectedZeroRun_correct G numbering lp lengths metadata selected
  intro i mem
  apply Finset.sum_eq_zero
  intro path _
  by_cases positive : 0<lp.flow i path
  · rw [supported_zero i mem path positive,zero_mul]
  · have zero : lp.flow i path=0 := le_antisymm (le_of_not_gt positive) (lp.flow_nonneg i path)
    rw [zero,mul_zero]

/-- Uniform original-h, arbitrary-subset version of Lemma 6.2. -/
def SelectedZeroRoundingTarget : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (n h : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n) (lp : NodeLP G h) (lengths : Fin h → ℚ),
    (∀ i,lengths i=lp.fractionalLength i) → ∀ selected : Finset (Fin h),
    (∀ i∈selected,∀ path : G.Path (lp.source i) (lp.target i),
      0<lp.flow i path → NodeMetric.walkWeight G lp.physical path.val=0) →
    ∃ output,selectedZeroRun G numbering lp.buying lp.physical lp.opening lp.buyingBudget
      lp.source lp.target lengths selected=some output ∧ SelectedZeroOutput G lp selected output

theorem selected_zero_rounding_target : SelectedZeroRoundingTarget := by
  intro V _ _ n h G _ numbering lp lengths metadata selected supported_zero
  exact selected_zero_rounding G numbering lp lengths metadata selected supported_zero

end BuyAtBulk.Computation.Rounding
