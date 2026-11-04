import BuyAtBulk.Computation.Attachment.Queries

/-! Fixed tie order for nearby centers: scan the actual record list from its
head, skip records below the requested scale, and choose the first qualifying
shortest route. Promotions remain distinct records. -/
namespace BuyAtBulk.Computation.Attachment
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def nearRecord (weight : V → ℚ) (scale : ℚ) (z : V) :
    List (CenterRecord (V)) → Option (Σ v, G.Path z v)
  | [] => none
  | record :: rest =>
    if scale ≤ record.birthScale then
      match shortRoute G numbering weight z record.endpoint (scale / 8) with
      | some path => some ⟨record.endpoint, path⟩
      | none => nearRecord weight scale z rest
    else nearRecord weight scale z rest

theorem nearRecord_some (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    (scale : ℚ) (z : V) (records : List (CenterRecord (V))) (result : Σ v, G.Path z v)
    (returned : nearRecord G numbering weight scale z records = some result) :
    EligibleCenter records result.1 scale ∧ IsShortest G weight result.2 ∧
      NodeMetric.walkWeight G weight result.2.val ≤ scale / 8 := by
  induction records with
  | nil => simp [nearRecord] at returned
  | cons record rest ih =>
    simp only [nearRecord] at returned
    split at returned
    · rename_i high
      split at returned
      · rename_i path computed
        have same := Option.some.inj returned
        subst result
        have facts := shortRoute_some G numbering weight nonneg path computed
        exact ⟨⟨record, List.mem_cons_self, rfl, high⟩, facts⟩
      · obtain ⟨eligible, shortest, short⟩ := ih returned
        exact ⟨eligibility_persists rest record result.1 scale eligible, shortest, short⟩
    · obtain ⟨eligible, shortest, short⟩ := ih returned
      exact ⟨eligibility_persists rest record result.1 scale eligible, shortest, short⟩

theorem nearRecord_none (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    (scale : ℚ) (z : V) (records : List (CenterRecord (V)))
    (missing : nearRecord G numbering weight scale z records = none) :
    ¬ ∃ v, EligibleCenter records v scale ∧
      ∃ path : G.Path z v, NodeMetric.walkWeight G weight path.val ≤ scale / 8 := by
  induction records with
  | nil => simp [EligibleCenter]
  | cons record rest ih =>
    intro witness
    obtain ⟨v, ⟨chosen, member, endpoint, high⟩, path, short⟩ := witness
    simp only [nearRecord] at missing
    split at missing
    · rename_i record_high
      split at missing
      · contradiction
      · rename_i absent
        rcases List.mem_cons.mp member with same | old
        · subst chosen
          subst v
          exact (shortRoute_none_iff G numbering weight nonneg z record.endpoint (scale / 8)).mp absent ⟨path, short⟩
        · exact ih missing ⟨v, ⟨chosen, old, endpoint, high⟩, path, short⟩
    · rename_i record_low
      rcases List.mem_cons.mp member with same | old
      · subst chosen
        exact record_low high
      · exact ih missing ⟨v, ⟨chosen, old, endpoint, high⟩, path, short⟩

end BuyAtBulk.Computation.Attachment
