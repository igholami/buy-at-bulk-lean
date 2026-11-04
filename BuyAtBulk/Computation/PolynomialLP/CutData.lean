import BuyAtBulk.Computation.PolynomialLP.Separation
import BuyAtBulk.Computation.PolynomialLP.OptimalFaces

/-! Actual stored constraint extension for exact objective and coordinate
queries. Appending constraints preserves the original bounded domain. -/
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

def Stored.addCut (input : Stored (n := n) (m := m)) (row : Vector ℚ n) (bound : ℚ) :
    Stored (n := n) (m := m+1) where
  coefficients := input.coefficients.push row
  bounds := input.bounds.push bound
  objective := input.objective

theorem Stored.addCut_feasible (input : Stored (n := n) (m := m)) (row : Vector ℚ n)
    (bound : ℚ) (x : Fin n → ℚ) :
    (input.addCut row bound).problem.Feasible x ↔ input.problem.Feasible x ∧ rowForm row x ≤ bound := by
  constructor
  · intro feasible
    constructor
    · intro i
      have old := feasible i.castSucc
      simpa [Stored.problem,Stored.addCut] using old
    · have last := feasible (Fin.last m)
      simpa only [Stored.problem,Stored.addCut,Fin.val_last,Vector.getElem_push_eq] using last
  · rintro ⟨old,last⟩ i
    apply Fin.lastCases (motive:=fun i => (input.addCut row bound).problem.row i x ≤ (input.addCut row bound).problem.bound i) _ _ i
    · simpa only [Stored.problem,Stored.addCut,Fin.val_last,Vector.getElem_push_eq] using last
    · intro i
      simpa [Stored.problem,Stored.addCut] using old i

theorem Stored.addCut_in_cube (input : Stored (n := n) (m := m)) (row : Vector ℚ n)
    (bound : ℚ) (cube : input.problem.InUnitCube) : (input.addCut row bound).problem.InUnitCube := by
  intro x feasible
  exact cube x ((input.addCut_feasible row bound x).mp feasible).1

def Stored.withObjective (input : Stored (n := n) (m := m)) (objective : Vector ℚ n) :
    Stored (n := n) (m := m) := {input with objective := objective}

theorem Stored.withObjective_feasible (input : Stored (n := n) (m := m))
    (objective : Vector ℚ n) (x : Fin n → ℚ) :
    (input.withObjective objective).problem.Feasible x ↔ input.problem.Feasible x := Iff.rfl

theorem Stored.withObjective_vertex (input : Stored (n := n) (m := m))
    (objective : Vector ℚ n) (x : Fin n → ℚ) :
    (input.withObjective objective).problem.Vertex x ↔ input.problem.Vertex x := Iff.rfl

def Stored.fix (input : Stored (n := n) (m := m)) (row : Vector ℚ n) (value : ℚ) :
    Stored (n := n) (m := m+1+1) :=
  (input.addCut row value).addCut (row.map (-·)) (-value)

theorem rowForm_neg (row : Vector ℚ n) (x : Fin n → ℚ) :
    rowForm (row.map (-·)) x = -(rowForm row x) := by
  simp only [rowForm_apply,Vector.getElem_map,neg_mul,Finset.sum_neg_distrib]

theorem Stored.fix_feasible (input : Stored (n := n) (m := m)) (row : Vector ℚ n)
    (value : ℚ) (x : Fin n → ℚ) :
    (input.fix row value).problem.Feasible x ↔ input.problem.Feasible x ∧ rowForm row x = value := by
  rw [Stored.fix,Stored.addCut_feasible,Stored.addCut_feasible,rowForm_neg]
  constructor <;> intro h
  · exact ⟨h.1.1,by linarith [h.1.2,h.2]⟩
  · exact ⟨⟨h.1,h.2.le⟩,by rw [h.2]⟩

theorem Stored.fix_in_cube (input : Stored (n := n) (m := m)) (row : Vector ℚ n)
    (value : ℚ) (cube : input.problem.InUnitCube) : (input.fix row value).problem.InUnitCube := by
  intro x feasible
  exact cube x ((input.fix_feasible row value x).mp feasible).1

/-- The query itself is a concrete stored LP. The supplied Boolean procedure
is the feasibility algorithm to be instantiated after its independent proof. -/
def below (oracle : {m : ℕ} → Stored (n := n) (m := m) → Bool)
    (input : Stored (n := n) (m := m)) (threshold : ℚ) : Bool :=
  oracle (input.addCut input.objective threshold)

theorem below_correct
    (oracle : {m : ℕ} → Stored (n := n) (m := m) → Bool)
    (oracle_correct : ∀ {m} (input : Stored (n := n) (m := m)), input.problem.InUnitCube →
      (oracle input = true ↔ ∃ x, input.problem.Feasible x))
    (input : Stored (n := n) (m := m)) (cube : input.problem.InUnitCube)
    (optimum : Fin n → ℚ) (feasible : input.problem.Feasible optimum)
    (minimal : ∀ x, input.problem.Feasible x → input.problem.objective optimum ≤ input.problem.objective x)
    (threshold : ℚ) : below oracle input threshold = true ↔ input.problem.objective optimum ≤ threshold := by
  rw [below,oracle_correct _ (input.addCut_in_cube _ _ cube)]
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨original,bounded⟩ := (input.addCut_feasible _ _ x).mp hx
    exact (minimal x original).trans bounded
  · intro bounded
    exact ⟨optimum,(input.addCut_feasible _ _ optimum).mpr ⟨feasible,bounded⟩⟩

def Stored.extend {k : ℕ} (input : Stored (n := n) (m := m))
    (rows : Vector (Vector ℚ n) k) (bounds : Vector ℚ k) : Stored (n := n) (m := m+k) where
  coefficients := input.coefficients++rows
  bounds := input.bounds++bounds
  objective := input.objective

theorem Stored.extend_feasible {k : ℕ} (input : Stored (n := n) (m := m))
    (rows : Vector (Vector ℚ n) k) (bounds : Vector ℚ k) (x : Fin n → ℚ) :
    (input.extend rows bounds).problem.Feasible x ↔
      input.problem.Feasible x ∧ ∀ i : Fin k, rowForm rows[i.val] x ≤ bounds[i.val] := by
  constructor
  · intro feasible
    constructor
    · intro i
      have original := feasible (Fin.castAdd k i)
      simpa [Stored.extend,Stored.problem] using original
    · intro i
      have added := feasible (Fin.natAdd m i)
      simpa [Stored.extend,Stored.problem] using added
  · rintro ⟨original,added⟩ i
    apply Fin.addCases (motive:=fun i => (input.extend rows bounds).problem.row i x ≤
      (input.extend rows bounds).problem.bound i) _ _ i
    · intro i
      simpa [Stored.extend,Stored.problem] using original i
    · intro i
      simpa [Stored.extend,Stored.problem] using added i

def coordinateRows (n : ℕ) (sign : ℚ) : Vector (Vector ℚ n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i=j then sign else 0

theorem coordinateRows_value (sign : ℚ) (i : Fin n) (x : Fin n → ℚ) :
    rowForm (coordinateRows n sign)[i.val] x = sign*x i := by
  simp [rowForm_apply,coordinateRows,ite_mul]

def Stored.boxed (input : Stored (n := n) (m := m)) : Stored (n := n) (m := m+(n+n)) :=
  input.extend (coordinateRows n 1++coordinateRows n (-1))
    (Vector.replicate n (1 : ℚ)++Vector.replicate n (0 : ℚ))

theorem Stored.boxed_feasible (input : Stored (n := n) (m := m)) (x : Fin n → ℚ) :
    input.boxed.problem.Feasible x ↔ input.problem.Feasible x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  rw [Stored.boxed,Stored.extend_feasible]
  constructor
  · rintro ⟨original,box⟩
    refine ⟨original,?_⟩
    intro j
    have upper := box (Fin.castAdd n j)
    have lower := box (Fin.natAdd n j)
    simp [coordinateRows,ite_mul] at upper lower
    exact ⟨by linarith,upper⟩
  · rintro ⟨original,box⟩
    refine ⟨original,?_⟩
    intro i
    apply Fin.addCases (motive:=fun i =>
      rowForm (coordinateRows n 1++coordinateRows n (-1))[i.val] x ≤
        (Vector.replicate n (1 : ℚ)++Vector.replicate n (0 : ℚ))[i.val]) _ _ i
    · intro j
      simpa [coordinateRows,ite_mul] using (box j).2
    · intro j
      have lower : -(x j) ≤ 0 := by linarith [(box j).1]
      simpa [coordinateRows,ite_mul] using lower

theorem Stored.boxed_in_cube (input : Stored (n := n) (m := m)) : input.boxed.problem.InUnitCube := by
  intro x feasible
  exact (input.boxed_feasible x).mp feasible |>.2

/-- The unrestricted box-oracle interface discharges the bounded-query
interface used in objective bisection; boundedness is a proved consequence of
source constraints, never an optimizer certificate. -/
theorem below_boxed_correct
    (oracle : {m : ℕ} → Stored (n := n) (m := m) → Bool)
    (oracle_correct : ∀ {m} (input : Stored (n := n) (m := m)),
      oracle input = true ↔ ∃ x, input.problem.Feasible x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (input : Stored (n := n) (m := m)) (cube : input.problem.InUnitCube)
    (optimum : Fin n → ℚ) (feasible : input.problem.Feasible optimum)
    (minimal : ∀ x, input.problem.Feasible x → input.problem.objective optimum ≤ input.problem.objective x)
    (threshold : ℚ) : below oracle input threshold = true ↔ input.problem.objective optimum ≤ threshold := by
  apply below_correct oracle _ input cube optimum feasible minimal threshold
  intro k problem bounded
  rw [oracle_correct]
  exact ⟨fun ⟨x,hx,_⟩ => ⟨x,hx⟩,fun ⟨x,hx⟩ => ⟨x,hx,bounded x hx⟩⟩

end BuyAtBulk.PolynomialLP
