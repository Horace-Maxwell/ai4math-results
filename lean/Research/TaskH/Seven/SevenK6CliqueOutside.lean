import Research.TaskH.Seven.SevenK6CliquePairBudget
import Research.TaskH.Seven.SevenIndependentBounds

/-!
Every outside point has at most one neighbor in an actual six-clique.
This is a proved consequence of the original equality graph's noncomplete
branch, using the actual two-hook clone family and its incidence budget.
The final six-group closed-neighborhood packing is a subsequent obligation.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem critical_six_clique_outside_hooks_le_one
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hc : modCycleCount 7 G = 2880)
    (hn11 : 11 ≤ Fintype.card V) (hn51 : Fintype.card V ≤ 51)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (sixCliqueHooks G q y).card ≤ 1 := by
  classical
  by_contra hlarge
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (sixCliqueHooks G q y).card)
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_six_pair_reindex a b hab
  let p := q ∘ ρ
  have hp : Function.Injective p := hq.comp ρ.injective
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique (ρ i) (ρ j) (ρ.injective.ne hij)
  have hyp : ∀ i, y ≠ p i := fun i => hy (ρ i)
  have hmem : ∀ i : Fin 6, i ∈ sixCliqueHooks G q y ↔ G.Adj y (q i) := by
    intro i
    simp only [sixCliqueHooks, Finset.mem_filter, Finset.mem_univ, true_and]
  have hy0 : G.Adj y (p 0) := by
    simpa only [p, Function.comp_apply, hρ0] using (hmem a).mp ha
  have hy1 : G.Adj y (p 1) := by
    simpa only [p, Function.comp_apply, hρ1] using (hmem b).mp hb
  exact critical_six_clique_no_two_hooks hcrit hs hr hc hn11 hn51 hdegree
    p hp hpclique y hyp hy0 hy1

theorem equality_six_clique_outside_hooks_le_one (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hnot : ¬ IsCompleteOfOrder G 8)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (sixCliqueHooks G q y).card ≤ 1 := by
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn9 := noncomplete_card_ge_nine hcrit hs hr hnot
  have hd : ∀ x : V, 8 ≤ G.degree x := fun x => noncomplete_degree_ge_eight hcrit hs hr hnot x
  have hn15 := critical_six_clique_card_ge_fifteen hcrit hs hr hc hn9 hd q hq hclique
  have hn51 := critical_card_le_fifty_one hcrit hs hr hn9 hc
  exact critical_six_clique_outside_hooks_le_one hcrit hs hr hc (by omega) hn51
    hd q hq hclique y hy

end TaskH.Seven

#print axioms TaskH.Seven.critical_six_clique_outside_hooks_le_one
#print axioms TaskH.Seven.equality_six_clique_outside_hooks_le_one
