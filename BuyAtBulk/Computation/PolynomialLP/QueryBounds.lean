import BuyAtBulk.Computation.PolynomialLP.CoordinateOptimization

/-! Uniform encodings for stored face and objective queries. Fixed face
coordinates inherit the original vertex bound, rather than recursively
re-estimating determinants of every appended system. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational
variable {n m : ℕ}

structure CellBits (input : Stored (n:=n) (m:=m)) (L : ℕ) : Prop where
  coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits≤L
  bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits≤L
  objective : ∀ j : Fin n, (Code.ofRat input.objective[j.val]).bits≤L

theorem CellBits.addCut {input : Stored (n:=n) (m:=m)} {L : ℕ} (cells : CellBits input L)
    (row : Vector ℚ n) (bound : ℚ)
    (rowbits : ∀ j : Fin n, (Code.ofRat row[j.val]).bits≤L)
    (scalar : (Code.ofRat bound).bits≤L) : CellBits (input.addCut row bound) L := by
  constructor
  · intro i
    apply Fin.lastCases (motive:=fun i => ∀ j : Fin n,
      (Code.ofRat (input.addCut row bound).coefficients[i.val][j.val]).bits≤L) _ _ i
    · intro j; simpa [Stored.addCut] using rowbits j
    · intro i j; simpa [Stored.addCut] using cells.coefficients i j
  · intro i
    apply Fin.lastCases (motive:=fun i => (Code.ofRat (input.addCut row bound).bounds[i.val]).bits≤L) _ _ i
    · simpa [Stored.addCut] using scalar
    · intro i; simpa [Stored.addCut] using cells.bounds i
  · exact cells.objective

theorem CellBits.fix {input : Stored (n:=n) (m:=m)} {L : ℕ} (cells : CellBits input L)
    (row : Vector ℚ n) (value : ℚ)
    (rowbits : ∀ j : Fin n, (Code.ofRat row[j.val]).bits≤L)
    (scalar : (Code.ofRat value).bits≤L) : CellBits (input.fix row value) L := by
  have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
  apply (cells.addCut row value rowbits scalar).addCut (row.map (-·)) (-value)
  · intro j
    simpa [negative] using rowbits j
  · simpa [negative] using scalar

theorem CellBits.withObjective {input : Stored (n:=n) (m:=m)} {L : ℕ} (cells : CellBits input L)
    (objective : Vector ℚ n) (objectivebits : ∀ j : Fin n, (Code.ofRat objective[j.val]).bits≤L) :
    CellBits (input.withObjective objective) L := ⟨cells.coefficients,cells.bounds,objectivebits⟩

theorem coordinateObjective_bits (i j : Fin n) : (Code.ofRat (coordinateObjective i)[j.val]).bits≤4 := by
  simp only [coordinateObjective,Vector.getElem_ofFn]
  split_ifs <;> decide

theorem recover_coordinate_bound {m₀ : ℕ} (original : Stored (n:=n) (m:=m₀)) (K : ℕ)
    (cube : original.problem.InUnitCube)
    (words : ∀ x, original.problem.Feasible x → original.problem.Vertex x →
      ∀ j, (Code.ofRat (x j)).bits≤K)
    (input : Stored (n:=n) (m:=m))
    (subset : ∀ x, input.problem.Feasible x → original.problem.Feasible x)
    (vertices : ∀ x, input.problem.Feasible x → input.problem.Vertex x → original.problem.Vertex x)
    (inhabited : ∃ x, input.problem.Feasible x) (i : Fin n) (value : ℚ)
    (computed : recoverValue (input.withObjective (coordinateObjective i)) K=some value) :
    (Code.ofRat value).bits≤K := by
  let current := input.withObjective (coordinateObjective i)
  obtain ⟨q,returned,x,hx,hv,equality,_⟩ := recoverValue_correct current K
    (fun y hy => cube y (subset y hy)) inhabited
    (fun y hy vy => words y (subset y hy) (vertices y hy vy))
  have same : q=value := Option.some.inj (returned.symm.trans computed)
  have coordinate : x i=value := by
    change rowForm (coordinateObjective i) x=q at equality
    simpa only [coordinateObjective_value,same] using equality
  rw [← coordinate]
  exact words x (subset x hx) (vertices x hx hv) i

end BuyAtBulk.PolynomialLP
