import BuyAtBulk.Computation.Runtime.CoreWords

/-! Equality transports change only proof/type indices, retaining every
stored Boolean, scalar and walk label. They execute no graph oracle. -/
namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
variable {n h : ℕ}

abbrev StoredResult (G : SimpleGraph (Fin n)) (source target : Fin h → Fin n) :=
  Option (StoredState.State G × List (Σ i : Fin h,G.Path (source i) (target i)))
abbrev SemanticResult (G : SimpleGraph (Fin n)) (source target : Fin h → Fin n) :=
  Option (RoundingState G × List (Σ i : Fin h,G.Path (source i) (target i)))

def decodeResult (G : SimpleGraph (Fin n)) (source target : Fin h → Fin n) : StoredResult G source target → SemanticResult G source target :=
  Option.map fun result => (StoredState.decode G result.1,result.2)

def transportResult {G H : SimpleGraph (Fin n)} {source target target' : Fin h → Fin n}
    (graph_eq : G=H) (target_eq : target=target') : StoredResult G source target → StoredResult H source target' :=
  cast (by cases graph_eq;cases target_eq;rfl)

def transportSemantic {G H : SimpleGraph (Fin n)} {source target target' : Fin h → Fin n}
    (graph_eq : G=H) (target_eq : target=target') : SemanticResult G source target → SemanticResult H source target' :=
  cast (by cases graph_eq;cases target_eq;rfl)

theorem decode_transport {G H : SimpleGraph (Fin n)} {source target target' : Fin h → Fin n}
    (graph_eq : G=H) (target_eq : target=target') (result : StoredResult G source target) :
    decodeResult H source target' (transportResult graph_eq target_eq result)=
      transportSemantic graph_eq target_eq (decodeResult G source target result) := by
  cases graph_eq
  cases target_eq
  rfl

theorem core_transport {G H : SimpleGraph (Fin n)} [leftDec : DecidableRel G.Adj] [rightDec : DecidableRel H.Adj]
    (graph_eq : G=H) {source target target' : Fin h → Fin n} (target_eq : target=target')
    (buying physical opening : Fin n → ℚ) (budget : ℚ) (allowance : Fin h → ℚ)
    (active : Finset (Fin h)) (ratio r : ℕ) (seed : Finset (Fin n)) :
    transportSemantic graph_eq target_eq
      (Computation.Core.run G (Equiv.refl _) buying physical opening budget allowance source target active ratio r seed)=
      Computation.Core.run H (Equiv.refl _) buying physical opening budget allowance source target' active ratio r seed := by
  cases graph_eq
  cases target_eq
  cases Subsingleton.elim leftDec rightDec
  rfl

end BuyAtBulk.Computation.Runtime.StoredRounding
