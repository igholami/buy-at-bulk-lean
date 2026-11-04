import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Tactic.NormNum

namespace BuyAtBulk.UpperBound.Girth
open SimpleGraph

/-- No cycle has length at most twice the exploration depth. This includes
acyclic graphs without assigning them a finite girth. -/
def HighGirth {V : Type} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → 2 * r < p.length

/-- The two-branch collision argument: short simple paths with common
endpoints coincide, since otherwise their union contains a short cycle. -/
theorem short_path_unique {V : Type} {G : SimpleGraph V} {r : ℕ}
    (hg : HighGirth G r) {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (hl : p.length + q.length ≤ 2 * r) : p = q := by
  by_contra hne
  obtain ⟨w, _, _, cycle, hcycle, hlength⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hg w cycle hcycle
  omega

/-- Among the neighbors of the end of a short simple path, only its parent
can already occur on the path. This is the exact `degree - 1` branching fact. -/
theorem neighbor_mem_support_eq_parent {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ} (hr : 1 ≤ r) (hg : HighGirth G r)
    {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : p.length < r)
    (hadj : G.Adj v w) (hw : w ∈ p.support) : w = p.penultimate := by
  have hwrev : w ∈ p.reverse.support := by simpa using hw
  let q := p.reverse.takeUntil w hwrev
  have hq : q.IsPath := hp.reverse.takeUntil hwrev
  have hlenq : q.length ≤ p.length := by
    simpa [q] using p.reverse.length_takeUntil_le_length hwrev
  have heq : q = hadj.toWalk := short_path_unique hg q hadj.toWalk hq
    (SimpleGraph.Walk.IsPath.mk' (by simp [hadj.ne])) (by simp; omega)
  have hsnd := congrArg SimpleGraph.Walk.snd heq
  have htake : q.snd = p.penultimate := by
    rw [show q = p.reverse.takeUntil w hwrev from rfl,
      SimpleGraph.Walk.snd_takeUntil hadj.ne.symm,
      SimpleGraph.Walk.snd_reverse]
  simpa [htake] using hsnd.symm

end BuyAtBulk.UpperBound.Girth
