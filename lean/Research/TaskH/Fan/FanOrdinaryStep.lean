import Research.TaskH.Fan.EqualNeighborhoodRecursion
import Research.TaskH.Fan.FourCycleComponentBranch

/-! All actual ordinary two-connected cases, with explicit root orientation and strict-card IH. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem fan_ordinary_oriented_step [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hdeg : NonrootDegreeAtLeast G x y 3)
    (horient : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : HasTwoPaths G x y := by
  classical
  by_contra hbad
  obtain ⟨a, b, c, hxa, hxb, hxc, hab, hac, hbc, exa, eab, ebc, ecx, hy⟩ :=
    counterexample_oriented_rootFour G x y hG hxy hno hdeg hbad horient ih
  exact hbad (fourCycle_component_induction_branch G x a b c y hG hdeg
    hxa hxb hxc hab hac hbc exa eab ebc ecx hy ih)

theorem fan_ordinary_vertex_step [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hdeg : NonrootDegreeAtLeast G x y 3)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : HasTwoPaths G x y := by
  rcases le_total (G.neighborSet x).ncard (G.neighborSet y).ncard with h | h
  · exact fan_ordinary_oriented_step G x y hG hxy hno hdeg h ih
  · have hdeg' : NonrootDegreeAtLeast G y x 3 := fun v hvy hvx => hdeg v hvx hvy
    have hno' : ¬G.Adj y x := fun e => hno e.symm
    exact hasTwoPaths_reverse
      (fan_ordinary_oriented_step G y x hG hxy.symm hno' hdeg' h ih)

#print axioms fan_ordinary_oriented_step
#print axioms fan_ordinary_vertex_step
end TaskH.Fan
