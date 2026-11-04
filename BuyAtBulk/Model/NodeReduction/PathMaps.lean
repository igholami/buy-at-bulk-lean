import BuyAtBulk.Model.NodeReduction.EndpointEmbedding
import BuyAtBulk.Model.NodeReduction.EndpointProjection

namespace BuyAtBulk.NodeReduction

/-- Map every indexed original simple path to its full leaf-to-leaf subdivision. -/
noncomputable def liftCode (D : GraphData) (p : Fin D.toInstance.pathCount) :
    Fin (reduced D).toInstance.pathCount :=
  (reduced D).encode (D.decode p).1 (liftPath D (D.decode p).1 (D.decode p).2)

/-- Project every indexed transformed simple path; completeness is supplied
by the graph compression theorem, not assumed as a path-list hypothesis. -/
noncomputable def projectCode (D : GraphData) (p : Fin (reduced D).toInstance.pathCount) :
    Fin D.toInstance.pathCount :=
  D.encode ((reduced D).decode p).1
    (projectPath D ((reduced D).decode p).1 ((reduced D).decode p).2)

theorem liftCode_allowed (D : GraphData) (i : Fin D.requestCount) (p : Fin D.toInstance.pathCount) :
    (reduced D).toInstance.allowed i (liftCode D p) = D.toInstance.allowed i p := by
  classical
  simp [liftCode]

theorem projectCode_allowed (D : GraphData) (i : Fin D.requestCount)
    (p : Fin (reduced D).toInstance.pathCount) :
    D.toInstance.allowed i (projectCode D p) = (reduced D).toInstance.allowed i p := by
  classical
  simp [projectCode]

theorem liftCode_uses (D : GraphData) (p : Fin D.toInstance.pathCount) :
    (reduced D).toInstance.uses (liftCode D p) = D.toInstance.uses p := by
  unfold liftCode
  exact ((reduced D).uses_encode _ _).trans (liftPath_resources D _ _)

theorem projectCode_uses (D : GraphData) (p : Fin (reduced D).toInstance.pathCount) :
    D.toInstance.uses (projectCode D p) = (reduced D).toInstance.uses p := by
  unfold projectCode
  exact (D.uses_encode _ _).trans (projectPath_resources D _ _)

end BuyAtBulk.NodeReduction
