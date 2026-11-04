import BuyAtBulk.Computation.Runtime.Numerical
import BuyAtBulk.Computation.Runtime.HelperConstruction
import BuyAtBulk.Computation.Core.Initialization

/-! Derive helper coefficient encoding from the actual opening/buying vectors,
stored fixed-row tolls/radii, and budget. No factor-encoding hypothesis is used.
The prior row-materialization stage must supply the stated table word bound. -/
namespace BuyAtBulk.Computation.Runtime.SourceCoefficients
open Rational BuyAtBulk.UpperBound
open HelperConstruction (StoredTables)
variable {n h ratio m : ℕ}

theorem natCast_bits (a : ℕ) : (Code.ofRat (a : ℚ)).bits = a.size+3 := by
  simp [Code.ofRat, Code.bits]
theorem powerTwo_bits (k : ℕ) : (Code.ofRat ((2 : ℚ)^k)).bits = k+4 := by
  have equal : (2 : ℚ)^k = ((2^k : ℕ) : ℚ) := by norm_cast
  rw [equal]
  simp [Code.ofRat, Code.bits, Nat.size_pow]
theorem neg_bits (q : ℚ) : (Code.ofRat (-q)).bits = (Code.ofRat q).bits := by
  simp [Code.ofRat, Code.bits]

def tables (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) : StoredTables n m where
  rowOrder := List.finRange m
  rowOrder_eq := rfl
  buying := buying
  probability := Vector.ofFn fun v => Core.helperProbability (fun v => opening[v.val]) h v
  factor := Vector.ofFn fun r => Vector.ofFn fun v => Core.helperFactor (Equiv.refl _) database rows[r.val] v
  amplitude := Vector.ofFn fun r => Core.helperAmplitude (Equiv.refl _) (fun v => opening[v.val]) database rows[r.val]
  fixedCost := Core.helperFixedCost (Equiv.refl _) (fun v => buying[v.val]) (fun v => opening[v.val]) h
  normalization := 4*Core.helperAlpha h*budget

def budget (n h L : ℕ) : ℕ := 4096*h+(16*n+64)*L+256

theorem alpha_bits (h : ℕ) : (Code.ofRat (Core.helperAlpha h)).bits ≤ 1024*h+3 := by
  have logarithm := helperRepetitions_bound h
  have equal : Core.helperAlpha h = ((128*Nat.clog 2 (8*h) : ℕ) : ℚ) := by
    simp [Core.helperAlpha, Core.helperRepetitions]
  rw [equal, natCast_bits]
  have size : (128*Nat.clog 2 (8*h)).size ≤ 128*Nat.clog 2 (8*h) :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem probability_bits (opening : Vector ℚ n) (v : Fin n) (L : ℕ)
    (input : (Code.ofRat opening[v.val]).bits+1 ≤ L) :
    (Code.ofRat (Core.helperProbability (fun v => opening[v.val]) h v)).bits+1 ≤ 2048*h+2*L+14 := by
  unfold Core.helperProbability
  split
  · norm_num [Code.ofRat, Code.bits]
  · have product := normalized_mul_bits (Core.helperAlpha h) opening[v.val]
    have alpha := alpha_bits h
    change (Code.ofRat (Core.helperAlpha h*opening[v.val])).bits+1 ≤ _
    omega

theorem factor_bits (database : Core.RowDatabase h ratio n) (row : Core.RawRow h ratio) (v : Fin n)
    (L : ℕ) (toll : (Code.ofRat (Core.getRow database row).toll[v.val]).bits+1 ≤ L)
    (radius : (Code.ofRat (Core.getRow database row).radius).bits+1 ≤ L) :
    (Code.ofRat (Core.helperFactor (Equiv.refl _) database row v)).bits+1 ≤ 12*L+105 := by
  have first := normalized_mul_bits 2 (Core.getRow database row).radius
  have quotient := normalized_div_bits (Core.getRow database row).toll[v.val] (2*(Core.getRow database row).radius)
  have negative := neg_bits ((Core.getRow database row).toll[v.val]/(2*(Core.getRow database row).radius))
  have result := normalized_add_bits 1 (-((Core.getRow database row).toll[v.val]/(2*(Core.getRow database row).radius)))
  rw [show (Code.ofRat 2).bits = 5 by decide] at first
  rw [show (Code.ofRat 1).bits = 4 by decide, negative] at result
  simp only [Core.helperFactor, Core.storedToll, Equiv.refl_apply, sub_eq_add_neg]
  omega

theorem amplitude_bits (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (row : Core.RawRow h ratio) :
    (Code.ofRat (Core.helperAmplitude (Equiv.refl _) (fun v => opening[v.val]) database row)).bits+1 ≤ 128*h+5 := by
  unfold Core.helperAmplitude
  split
  · rw [powerTwo_bits]
    have logarithm := helperRepetitions_bound h
    simp only [Core.helperRepetitions]
    omega
  · norm_num [Code.ofRat, Code.bits]

theorem heavy_length (opening : Vector ℚ n) :
    (Core.heavyVertices (Equiv.refl _) (fun v => opening[v.val]) h).length ≤ n := by
  exact (List.length_filter_le _ _).trans_eq (by simp [Core.vertexOrder])

theorem fixedCost_bits (buying opening : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits+1 ≤ L) :
    (Code.ofRat (Core.helperFixedCost (Equiv.refl _) (fun v => buying[v.val]) (fun v => opening[v.val]) h)).bits+1 ≤
      (4*n+2)*L+3 := by
  have encoded := HelperExpressions.sum_rat_bits
    ((Core.heavyVertices (Equiv.refl _) (fun v => opening[v.val]) h).map fun v => buying[v.val]) L constant
    (by intro q member; obtain ⟨v, _, rfl⟩ := List.mem_map.mp member; exact inputs v)
  simp only [List.length_map] at encoded
  have length := heavy_length (h := h) opening
  change (Code.ofRat _).bits+1 ≤ _
  change (Code.ofRat (Core.helperFixedCost (Equiv.refl _) (fun v => buying[v.val]) (fun v => opening[v.val]) h)).bits ≤ _ at encoded
  nlinarith

theorem normalization_bits (B : ℚ) (L : ℕ) (input : (Code.ofRat B).bits+1 ≤ L) :
    (Code.ofRat (4*Core.helperAlpha h*B)).bits+1 ≤ 4096*h+2*L+61 := by
  have alpha := alpha_bits h
  have first := normalized_mul_bits 4 (Core.helperAlpha h)
  have second := normalized_mul_bits (4*Core.helperAlpha h) B
  rw [show (Code.ofRat 4).bits = 6 by decide] at first
  omega

/-- Every coefficient table leaf has a polynomial input-derived encoding,
including light-row amplitudes, fixed buying cost and normalization. -/
theorem coefficients_bounded (buying opening : Vector ℚ n) (B : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m)
    (L : ℕ) (constant : 5 ≤ L)
    (buy : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits+1 ≤ L)
    (openings : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits+1 ≤ L)
    (Bbits : (Code.ofRat B).bits+1 ≤ L)
    (radii : ∀ row, (Code.ofRat (Core.getRow database row).radius).bits+1 ≤ L)
    (tolls : ∀ row (v : Fin n), (Code.ofRat (Core.getRow database row).toll[v.val]).bits+1 ≤ L) :
    HelperEvaluation.CoefficientsBounded (tables buying opening B database rows).tables (budget n h L) := by
  constructor
  · unfold budget; omega
  · intro v
    simpa [tables, StoredTables.tables] using (buy v).trans (show L ≤ budget n h L by unfold budget; nlinarith)
  · intro v
    have bound := probability_bits (h := h) opening v L (openings v)
    simp only [tables, StoredTables.tables, Vector.getElem_ofFn]
    exact bound.trans (by unfold budget; nlinarith)
  · intro r _ v
    have bound := factor_bits database rows[r.val] v L (tolls _ _) (radii _)
    simp only [tables, StoredTables.tables, Vector.getElem_ofFn]
    exact bound.trans (by unfold budget; nlinarith)
  · intro r _
    have bound := amplitude_bits opening database rows[r.val]
    simp only [tables, StoredTables.tables, Vector.getElem_ofFn]
    exact bound.trans (by unfold budget; nlinarith)
  · exact (fixedCost_bits (h := h) buying opening L constant buy).trans (by unfold budget; nlinarith)
  · exact (normalization_bits (h := h) B L Bbits).trans (by unfold budget; nlinarith)

end BuyAtBulk.Computation.Runtime.SourceCoefficients
