import BuyAtBulk.Computation.FlowDecomposition.Encoding

/-! Instrumented extraction traces are equivalent to the actual program.
All residual matrices, remaining masses and bottlenecks retain one common
integer denominator, and stay in the unit interval on compact LP input. -/
namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def extractTraced (source target : V) : ℕ → FlowMatrix n → ℚ →
    Option (WeightedPaths G source target) × List (FlowMatrix n × ℚ)
  | 0, matrix, mass => (extract G numbering source target 0 matrix mass, [(matrix, mass)])
  | fuel + 1, matrix, mass =>
      if mass = 0 then (some [], [(matrix, mass)]) else
        match positivePath G numbering (decodedFlow numbering matrix) source target with
        | none => (none, [(matrix, mass)])
        | some path =>
            let amount := bottleneck G (decodedFlow numbering matrix) mass path
            let recursive := extractTraced source target fuel (subtract G numbering matrix amount path) (mass - amount)
            (recursive.1.map (fun rest => (amount, path) :: rest), (matrix, mass) :: recursive.2)

theorem extractTraced_value (source target : V) (fuel : ℕ) :
    ∀ matrix mass, (extractTraced G numbering source target fuel matrix mass).1 = extract G numbering source target fuel matrix mass := by
  induction fuel with
  | zero => intro matrix mass; rfl
  | succ fuel ih =>
    intro matrix mass
    simp only [extractTraced, extract]
    split
    · rfl
    · cases found : positivePath G numbering (decodedFlow numbering matrix) source target with
      | none => simp only [found]
      | some path => simp only [found, ih]

structure StateValid (source target : V) (D : ℕ) (matrix : FlowMatrix n) (mass : ℚ) : Prop where
  mass_nonneg : 0 ≤ mass
  mass_le_one : mass ≤ 1
  mass_den : HasDenominator D mass
  coordinate_nonneg : ∀ u v, 0 ≤ decodedFlow numbering matrix u v
  coordinate_le_one : ∀ u v, decodedFlow numbering matrix u v ≤ 1
  coordinate_den : ∀ u v, HasDenominator D (decodedFlow numbering matrix u v)
  nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0
  balance : ∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
    mass * ((if source = v then 1 else 0) - (if target = v then 1 else 0))

theorem state_after_subtract (source target : V) (D : ℕ) (matrix : FlowMatrix n) (mass : ℚ)
    (valid : StateValid G numbering source target D matrix mass) (mass_ne_zero : mass ≠ 0)
    (path : G.Path source target) (found : positivePath G numbering (decodedFlow numbering matrix) source target = some path) :
    StateValid G numbering source target D (subtract G numbering matrix (bottleneck G (decodedFlow numbering matrix) mass path) path)
      (mass - bottleneck G (decodedFlow numbering matrix) mass path) := by
  let amount := bottleneck G (decodedFlow numbering matrix) mass path
  have positive := positivePath_some G numbering (decodedFlow numbering matrix) source target path found
  have mass_pos : 0 < mass := lt_of_le_of_ne valid.mass_nonneg (Ne.symm mass_ne_zero)
  obtain ⟨amount_pos, amount_le, residual_nonneg, _⟩ :=
    bottleneck_spec G path (decodedFlow numbering matrix) positive valid.coordinate_nonneg mass mass_pos
  have amount_den := bottleneck_denominator G (decodedFlow numbering matrix) mass path D valid.mass_den valid.coordinate_den
  refine ⟨sub_nonneg.mpr amount_le, ?_, sub_denominator D _ _ valid.mass_den amount_den,
    ?_, ?_, subtract_denominator G numbering matrix amount path D amount_den valid.coordinate_den, ?_, ?_⟩
  · linarith [valid.mass_le_one]
  · intro u v
    rw [subtract_flow]
    exact residual_nonneg u v
  · intro u v
    rw [subtract_flow]
    have removed := mul_nonneg amount_pos.le (transportVisits_nonneg path.val u v)
    linarith [valid.coordinate_le_one u v]
  · intro u v missing
    rw [subtract_flow, valid.nonedge u v missing, transportVisits_nonedge _ u v missing, mul_zero, sub_zero]
  · have equation := subtract_path_balance path (decodedFlow numbering matrix) mass amount (by
      intro v
      by_cases hs : source = v <;> by_cases ht : target = v <;> simpa [hs, ht] using valid.balance v)
    intro v
    simp only [subtract_flow]
    by_cases hs : source = v <;> by_cases ht : target = v <;> simpa [hs, ht] using equation v

theorem trace_valid (source target : V) (D : ℕ) (fuel : ℕ) :
    ∀ matrix mass, StateValid G numbering source target D matrix mass →
      ∀ state ∈ (extractTraced G numbering source target fuel matrix mass).2,
        StateValid G numbering source target D state.1 state.2 := by
  induction fuel with
  | zero =>
    intro matrix mass valid state member
    have same : state = (matrix, mass) := by simpa [extractTraced] using member
    subst state
    exact valid
  | succ fuel ih =>
    intro matrix mass valid state member
    simp only [extractTraced] at member
    split at member
    · have same : state = (matrix, mass) := by simpa using member
      subst state
      exact valid
    · rename_i mass_ne_zero
      split at member
      · have same : state = (matrix, mass) := by simpa using member
        subst state
        exact valid
      · rename_i path found
        rcases List.mem_cons.mp member with same | later
        · subst state
          exact valid
        · exact ih _ _ (state_after_subtract G numbering source target D matrix mass valid mass_ne_zero path found) state later

/-- Every normalized residual coordinate and remaining mass has a word bound
linear in the denominator part of the original encoded compact-flow input. -/
theorem decompose_trace_bits (matrix : FlowMatrix n) (source target : V)
    (nonneg : ∀ u v, 0 ≤ decodedFlow numbering matrix u v) (le_one : ∀ u v, decodedFlow numbering matrix u v ≤ 1)
    (nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0)
    (balance : ∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
      (if source = v then 1 else 0) - (if target = v then 1 else 0)) :
    ∀ state ∈ (extractTraced G numbering source target (n * n + 1) matrix 1).2,
      (Rational.Code.ofRat state.2).bits ≤ 2 * denominatorInputBits matrix + 4 ∧
      ∀ u v, (Rational.Code.ofRat (decodedFlow numbering state.1 u v)).bits ≤ 2 * denominatorInputBits matrix + 4 := by
  have initial : StateValid G numbering source target (commonDenominator matrix) matrix 1 :=
    ⟨by norm_num, le_rfl, by change (1 : ℕ) ∣ commonDenominator matrix; exact one_dvd _,
      nonneg, le_one, decoded_coordinate_denominator numbering matrix, nonedge, by simpa only [one_mul] using balance⟩
  intro state member
  have invariant := trace_valid G numbering source target (commonDenominator matrix) (n * n + 1) matrix 1 initial state member
  have input_size := commonDenominator_bits matrix
  constructor
  · have bound := unit_bits_bound state.2 _ (commonDenominator_pos matrix)
      invariant.mass_den invariant.mass_nonneg invariant.mass_le_one
    omega
  · intro u v
    have bound := unit_bits_bound (decodedFlow numbering state.1 u v) _ (commonDenominator_pos matrix)
      (invariant.coordinate_den u v) (invariant.coordinate_nonneg u v) (invariant.coordinate_le_one u v)
    omega

/-- All actual residual states have exact natural capacities and masses
at the single input-derived scale D, each between zero and D. -/
theorem decompose_trace_scaled (matrix : FlowMatrix n) (source target : V)
    (nonneg : ∀ u v, 0 ≤ decodedFlow numbering matrix u v) (le_one : ∀ u v, decodedFlow numbering matrix u v ≤ 1)
    (nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0)
    (balance : ∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
      (if source = v then 1 else 0) - (if target = v then 1 else 0)) :
    ∀ state ∈ (extractTraced G numbering source target (n * n + 1) matrix 1).2,
      scaledNumerator (commonDenominator matrix) state.2 ≤ commonDenominator matrix ∧
      (scaledNumerator (commonDenominator matrix) state.2 : ℚ) / commonDenominator matrix = state.2 ∧
      ∀ u v,
        scaledNumerator (commonDenominator matrix) (decodedFlow numbering state.1 u v) ≤ commonDenominator matrix ∧
        (scaledNumerator (commonDenominator matrix) (decodedFlow numbering state.1 u v) : ℚ) / commonDenominator matrix =
          decodedFlow numbering state.1 u v := by
  have initial : StateValid G numbering source target (commonDenominator matrix) matrix 1 :=
    ⟨by norm_num, le_rfl, by change (1 : ℕ) ∣ commonDenominator matrix; exact one_dvd _,
      nonneg, le_one, decoded_coordinate_denominator numbering matrix, nonedge, by simpa only [one_mul] using balance⟩
  intro state member
  have invariant := trace_valid G numbering source target (commonDenominator matrix) (n * n + 1) matrix 1 initial state member
  refine ⟨scaledNumerator_le _ _ (commonDenominator_pos matrix) invariant.mass_den invariant.mass_nonneg invariant.mass_le_one,
    scaledNumerator_value _ _ (commonDenominator_pos matrix) invariant.mass_den invariant.mass_nonneg, ?_⟩
  intro u v
  exact ⟨scaledNumerator_le _ _ (commonDenominator_pos matrix) (invariant.coordinate_den u v)
      (invariant.coordinate_nonneg u v) (invariant.coordinate_le_one u v),
    scaledNumerator_value _ _ (commonDenominator_pos matrix) (invariant.coordinate_den u v) (invariant.coordinate_nonneg u v)⟩

end BuyAtBulk.Computation.FlowDecomposition
