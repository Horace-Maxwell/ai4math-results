import Research.TaskH.Six.SixFiveCliqueReindex
import Research.TaskH.Six.SixFiveCliqueBudget
import Research.TaskH.Six.SixRootPathOrder

/-!
Three hooks from an outside point into an actual five-clique force all
outside attachments to its six-point set to be singletons. The actual
six-set incidence budget then contradicts the original count 420.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem critical_five_clique_no_three_hooks
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420) (hn : 8 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hya : G.Adj y (q a)) (hyb : G.Adj y (q b)) (hyc : G.Adj y (q c)) : False := by
  apply critical_no_sparse_six_set hcrit hs hc (fiveCliqueSixSet q y)
    (fiveCliqueSixSet_card q hq y hy)
  intro z hz
  exact critical_five_clique_three_hooks_outside_small hcrit hr hn q hq hclique y hy
    a b c hab hac hbc hya hyb hyc z (Finset.mem_compl.mp hz)

theorem critical_five_clique_hooks_card_le_two
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420) (hn : 8 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (fiveCliqueHooks G q y).card ≤ 2 := by
  classical
  let T : Finset (Fin 5) := Finset.univ.filter (fun i => G.Adj y (q i))
  have hT : fiveCliqueHooks G q y = T := by
    ext i
    simp only [fiveCliqueHooks, T, Finset.mem_filter]
  by_contra hlarge
  have hTlarge : 2 < T.card := by
    rw [← hT]
    omega
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hTlarge
  exact critical_five_clique_no_three_hooks hcrit hs hr hc hn q hq hclique y hy
    a b c hab hac hbc (Finset.mem_filter.mp ha).2
    (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc').2

theorem equality_five_clique_hooks_card_le_two (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (fiveCliqueHooks G q y).card ≤ 2 :=
  critical_five_clique_hooks_card_le_two hcrit (equality_shortSixCycles hcrit hc)
    (equality_rainbowSixCycles hcrit hc) hc
    (noncomplete_card_ge_eight hcrit (equality_shortSixCycles hcrit hc)
      (equality_rainbowSixCycles hcrit hc) hnot) q hq hclique y hy

end TaskH.Six

#print axioms TaskH.Six.critical_five_clique_no_three_hooks
#print axioms TaskH.Six.critical_five_clique_hooks_card_le_two
#print axioms TaskH.Six.equality_five_clique_hooks_card_le_two
