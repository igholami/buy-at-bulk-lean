import BuyAtBulk.UpperBound.ServeExecution

/-! Structural main-program conclusions from its actual branch execution:
old purchases persist, the request obtains a bought physical route, and no
request creates more than two center records (including promotions). -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace ServeExec

theorem bought_mono {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {threshold : ℚ} {s t : V} {reachable : Nonempty (G.Path s t)}
    {before after : RoundingState G} {route : G.Path s t}
    (execution : ServeExec G buying physical budget allowance h ratio threshold s t reachable before after route) :
    before.bought ⊆ after.bought := by
  induction execution with
  | already_bought => exact Finset.Subset.refl _
  | no_eligible => exact bought_subset_buyPath _ _ _
  | cheap => exact bought_subset_buyPath _ _ _
  | purchase first assigned u v sarm tarm bornS bornT not_bought choice above assignS assignT must_buy =>
    have steps := (bought_subset_buyPath G assigned sarm).trans
      ((bought_subset_buyPath G (buyPath G assigned sarm) choice.mainPath).trans
        (bought_subset_buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm))
    simpa only [recordEdge, assignT.bought_eq, assignS.bought_eq] using steps
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    simpa only [assignT.bought_eq, assignS.bought_eq] using attachS.bought_mono
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    simpa only [assignT.bought_eq, assignS.bought_eq] using attachS.bought_mono.trans attachT.bought_mono
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    simpa only [assignT.bought_eq, assignS.bought_eq] using attachS.bought_mono.trans attachT.bought_mono

theorem at_most_two_births {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {threshold : ℚ} {s t : V} {reachable : Nonempty (G.Path s t)}
    {before after : RoundingState G} {route : G.Path s t}
    (execution : ServeExec G buying physical budget allowance h ratio threshold s t reachable before after route) :
    after.centers.length ≤ before.centers.length + 2 := by
  induction execution with
  | already_bought => omega
  | no_eligible => simp [buyPath]
  | cheap => simp [buyPath]
  | purchase first assigned u v sarm tarm bornS bornT not_bought choice above assignS assignT must_buy =>
    have hs := assignS.at_most_one_birth
    have ht := assignT.at_most_one_birth
    dsimp [recordEdge, buyPath]
    omega
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    have count := attachS.at_most_one_birth
    rw [assignT.existing_eq, assignS.existing_eq] at count
    omega
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    have hs := attachS.at_most_one_birth
    have ht := attachT.at_most_one_birth
    rw [assignT.existing_eq, assignS.existing_eq] at hs
    omega
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    have hs := attachS.at_most_one_birth
    have ht := attachT.at_most_one_birth
    rw [assignT.existing_eq, assignS.existing_eq] at hs
    omega

theorem route_bought {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {threshold : ℚ} {s t : V} {reachable : Nonempty (G.Path s t)}
    {before after : RoundingState G} {route : G.Path s t}
    (execution : ServeExec G buying physical budget allowance h ratio threshold s t reachable before after route) :
    route.val.support.toFinset ⊆ after.bought := by
  induction execution with
  | already_bought route shortest _ => exact shortest.1
  | no_eligible => exact path_bought_buyPath _ _ _
  | cheap => exact path_bought_buyPath _ _ _
  | purchase => exact (path_bought_buyPath _ _ _).trans (bought_subset_buyPath _ _ _)
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    exact attachS.outcome_bought
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    exact attachT.outcome_bought
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    have s_bought : returnedS.val.support.toFinset ⊆ final.bought :=
      attachS.outcome_bought.trans attachT.bought_mono
    have middle_bought : middle.val.support.toFinset ⊆ final.bought :=
      mb.trans (attachS.bought_mono.trans attachT.bought_mono)
    have t_bought : returnedT.val.support.toFinset ⊆ final.bought := attachT.outcome_bought
    intro x hx
    have hx' : x ∈ ((returnedS.val.append middle.val).append returnedT.val.reverse).toPath.val.support := by
      simpa only [List.mem_toFinset] using hx
    have original := ((returnedS.val.append middle.val).append returnedT.val.reverse).support_toPath_subset_support hx'
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at original
    rcases original with (hs | hm) | ht
    · exact s_bought (by simpa only [List.mem_toFinset] using hs)
    · exact middle_bought (by simpa only [List.mem_toFinset] using hm)
    · exact t_bought (by simpa only [List.mem_toFinset] using ht)

end ServeExec
end BuyAtBulk.UpperBound
