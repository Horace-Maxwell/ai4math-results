import Research.TaskH.Six.SixFiveCliquePairBudget

/-!
Every outside point has at most one neighbor in an actual five-clique.
This is a proved consequence of the original equality graph's noncomplete
branch, using the actual two-hook clone family and its incidence budget.
The final five-group closed-neighborhood packing is a subsequent obligation.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem critical_five_clique_outside_hooks_le_one
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420)
    (hn10 : 10 ≤ Fintype.card V) (hn37 : Fintype.card V ≤ 37)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (fiveCliqueHooks G q y).card ≤ 1 := by
  classical
  by_contra hlarge
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (fiveCliqueHooks G q y).card)
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_five_pair_reindex a b hab
  let p := q ∘ ρ
  have hp : Function.Injective p := hq.comp ρ.injective
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique (ρ i) (ρ j) (ρ.injective.ne hij)
  have hyp : ∀ i, y ≠ p i := fun i => hy (ρ i)
  have hmem : ∀ i : Fin 5, i ∈ fiveCliqueHooks G q y ↔ G.Adj y (q i) := by
    intro i
    simp only [fiveCliqueHooks, Finset.mem_filter, Finset.mem_univ, true_and]
  have hy0 : G.Adj y (p 0) := by
    simpa only [p, Function.comp_apply, hρ0] using (hmem a).mp ha
  have hy1 : G.Adj y (p 1) := by
    simpa only [p, Function.comp_apply, hρ1] using (hmem b).mp hb
  exact critical_five_clique_no_two_hooks hcrit hs hr hc hn10 hn37 hdegree
    p hp hpclique y hyp hy0 hy1

theorem equality_five_clique_outside_hooks_le_one (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (fiveCliqueHooks G q y).card ≤ 1 := by
  have hs : ShortSixCycles G := equality_shortSixCycles hcrit hc
  have hr : RainbowSixCycles G := equality_rainbowSixCycles hcrit hc
  have hb := critical_noncomplete_bounds hcrit hs hr hc hnot
  have hn13 := critical_card_ge_thirteen hcrit hs hr hc hnot
  exact critical_five_clique_outside_hooks_le_one hcrit hs hr hc (by omega) hb.2.1
    (fun x => (hb.2.2 x).1) q hq hclique y hy

end TaskH.Six

#print axioms TaskH.Six.critical_five_clique_outside_hooks_le_one
#print axioms TaskH.Six.equality_five_clique_outside_hooks_le_one
