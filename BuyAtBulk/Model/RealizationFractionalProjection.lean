import BuyAtBulk.Model.RealizationTransport

/-! Complete graph-path flows project back to arbitrary original path codes.
Path completeness supplies each code; finite fiber sums preserve all marginals. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.RealizationTransport
variable (I : Instance) (realization : I.GraphRealization)

/-- Completeness yields a legal original code with exactly the graph resources. -/
theorem projection_code_exists (i : Fin I.requestCount)
    (q : Fin (graphData I realization).toInstance.pathCount)
    (allowed : (graphData I realization).toInstance.allowed i q = true) :
    ∃ p, I.allowed i p = true ∧ I.uses p = (graphData I realization).toInstance.uses q := by
  let D := graphData I realization
  obtain ⟨walk, simple, resource⟩ := D.realization.path_sound i q allowed
  obtain ⟨p, hp, huses⟩ := realization.path_complete i walk simple
  refine ⟨p, hp, ?_⟩
  rw [huses, resource]
  rfl

def fractionalProjectCode (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (i : Fin I.requestCount) (q : Fin (graphData I realization).toInstance.pathCount) :
    Fin I.pathCount := by
  classical
  exact if hq : (graphData I realization).toInstance.allowed i q = true then
    (projection_code_exists I realization i q hq).choose
  else (positive_allowed_path I seed hseed i).choose

theorem fractionalProjectCode_allowed (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (i : Fin I.requestCount) (q : Fin (graphData I realization).toInstance.pathCount) :
    I.allowed i (fractionalProjectCode I realization seed hseed i q) = true := by
  classical
  unfold fractionalProjectCode
  split_ifs with hq
  · exact (projection_code_exists I realization i q hq).choose_spec.1
  · exact (positive_allowed_path I seed hseed i).choose_spec.1

theorem fractionalProjectCode_uses (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (i : Fin I.requestCount) (q : Fin (graphData I realization).toInstance.pathCount)
    (hq : (graphData I realization).toInstance.allowed i q = true) :
    I.uses (fractionalProjectCode I realization seed hseed i q) =
      (graphData I realization).toInstance.uses q := by
  classical
  simp only [fractionalProjectCode, dite_eq_left hq]
  exact (projection_code_exists I realization i q hq).choose_spec.2

def projectFractional (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (g : (graphData I realization).toInstance.FractionalSolution) : I.FractionalSolution where
  opening := g.opening
  flow i := NodeReduction.pushflow (fractionalProjectCode I realization seed hseed i) (g.flow i)

theorem projectFractional_weighted (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (g : (graphData I realization).toInstance.FractionalSolution)
    (hg : (graphData I realization).toInstance.Feasible g) (i : Fin I.requestCount)
    (weight : Fin I.pathCount → ℚ) (weight' : Fin (graphData I realization).toInstance.pathCount → ℚ)
    (hweight : ∀ q, (graphData I realization).toInstance.allowed i q = true →
      weight (fractionalProjectCode I realization seed hseed i q) = weight' q) :
    (∑ p, weight p * (projectFractional I realization seed hseed g).flow i p) =
      ∑ q, weight' q * g.flow i q := by
  have hw := NodeReduction.weighted_pushflow
    (fractionalProjectCode I realization seed hseed i) (g.flow i) weight
  apply hw.trans
  apply Finset.sum_congr rfl
  intro q _
  cases hq : (graphData I realization).toInstance.allowed i q with
  | false => simp [hg.2.2.1 i q hq]
  | true => rw [hweight q hq]

theorem projectFractional_resourceFlow (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (g : (graphData I realization).toInstance.FractionalSolution)
    (hg : (graphData I realization).toInstance.Feasible g) (i : Fin I.requestCount)
    (a : Fin I.resourceCount) :
    I.resourceFlow (projectFractional I realization seed hseed g) i a =
      (graphData I realization).toInstance.resourceFlow g i a := by
  classical
  have hw := projectFractional_weighted I realization seed hseed g hg i
    (fun p => if a ∈ I.uses p then 1 else 0)
    (fun q => if a ∈ (graphData I realization).toInstance.uses q then 1 else 0)
    (by intro q hq; rw [fractionalProjectCode_uses I realization seed hseed i q hq])
  simpa only [Instance.resourceFlow, ite_mul, one_mul, zero_mul] using hw

theorem projectFractional_feasible (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (g : (graphData I realization).toInstance.FractionalSolution)
    (hg : (graphData I realization).toInstance.Feasible g) :
    I.Feasible (projectFractional I realization seed hseed g) := by
  classical
  refine ⟨hg.1, ?_, ?_, ?_, ?_⟩
  · intro i p
    change 0 ≤ ∑ q, if fractionalProjectCode I realization seed hseed i q = p then g.flow i q else 0
    apply Finset.sum_nonneg
    intro q _
    split_ifs
    · exact hg.2.1 i q
    · exact le_rfl
  · intro i p hp
    change (∑ q, if fractionalProjectCode I realization seed hseed i q = p then g.flow i q else 0) = 0
    apply Finset.sum_eq_zero
    intro q _
    split_ifs with heq
    · have ha := fractionalProjectCode_allowed I realization seed hseed i q
      rw [heq, hp] at ha
      cases ha
    · rfl
  · intro i
    have hw := NodeReduction.weighted_pushflow
      (fractionalProjectCode I realization seed hseed i) (g.flow i) (fun _ => (1 : ℚ))
    simpa only [one_mul, projectFractional, hg.2.2.2.1 i] using hw
  · intro i a
    rw [projectFractional_resourceFlow I realization seed hseed g hg]
    exact hg.2.2.2.2 i a

@[simp] theorem projectFractional_buyingCost (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (g : (graphData I realization).toInstance.FractionalSolution) :
    I.buyingCost (projectFractional I realization seed hseed g) =
      (graphData I realization).toInstance.buyingCost g := rfl

theorem projectFractional_rentalCost (seed : I.FractionalSolution) (hseed : I.Feasible seed)
    (g : (graphData I realization).toInstance.FractionalSolution)
    (hg : (graphData I realization).toInstance.Feasible g) :
    I.rentalCost (projectFractional I realization seed hseed g) =
      (graphData I realization).toInstance.rentalCost g := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply projectFractional_weighted I realization seed hseed g hg i I.pathLength
    (graphData I realization).toInstance.pathLength
  intro q hq
  unfold Instance.pathLength
  rw [fractionalProjectCode_uses I realization seed hseed i q hq]

end BuyAtBulk.RealizationTransport
