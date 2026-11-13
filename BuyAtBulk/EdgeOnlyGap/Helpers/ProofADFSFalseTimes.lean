import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSQueryPrefix
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSCounts

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Query indices, rather than symbol positions, at which the fixed script prescribes
an already discovered vertex. Return symbols do not advance the index. -/
def falseTimes {d : ℕ} : List (DFSSymbol d) → Finset ℕ
  | [] => ∅
  | none::ss => falseTimes ss
  | some (_,flag)::ss =>
    if flag then (falseTimes ss).image Nat.succ else insert 0 ((falseTimes ss).image Nat.succ)

 theorem falseTimes_card {d : ℕ} (script : List (DFSSymbol d)) :
    (falseTimes script).card = (script.filter surplusSymbol).length := by
  induction script with
  | nil => simp [falseTimes]
  | cons s ss ih =>
    cases s with
    | none => simpa [falseTimes,surplusSymbol] using ih
    | some a =>
      rcases a with ⟨p,flag⟩
      cases flag <;> simp [falseTimes,surplusSymbol,Finset.card_image_of_injective,
        Nat.succ_injective,ih,List.filter_cons]

 theorem falseTimes_spec {d : ℕ} (script : List (DFSSymbol d)) :
    ∀ k ∈ falseTimes script,
      k < (script.filter Option.isSome).length ∧
      ∃ p ss, querySuffix k script = some (p,false)::ss := by
  induction script with
  | nil => simp [falseTimes]
  | cons s ss ih =>
    cases s with
    | none => simpa [falseTimes,querySuffix] using ih
    | some a =>
      rcases a with ⟨p,flag⟩
      intro k hk
      cases flag with
      | false =>
        simp only [falseTimes, Bool.false_eq_true, ↓reduceIte,Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact ⟨by simp, p,ss,rfl⟩
        · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
          obtain ⟨hbound,p',ss',hs⟩ := ih j hj
          exact ⟨by simpa using Nat.succ_lt_succ hbound,p',ss',hs⟩
      | true =>
        simp only [falseTimes,↓reduceIte] at hk
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨hbound,p',ss',hs⟩ := ih j hj
        exact ⟨by simpa using Nat.succ_lt_succ hbound,p',ss',hs⟩

end BuyAtBulk.EdgeOnlyGap.ProofA
