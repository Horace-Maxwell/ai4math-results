import Research.TaskH.Seven.SevenK6CliqueReindex
import Research.TaskH.Seven.SevenK6CliqueBudget
import Research.TaskH.Seven.SevenEqualityBasics

/-!
Three hooks from an outside point into an actual six-clique force all
outside attachments to its seven-point set to be singletons. The actual
seven-set incidence budget then contradicts the original count 2880.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem critical_six_clique_no_three_hooks
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hc : modCycleCount 7 G = 2880) (hn : 9 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hya : G.Adj y (q a)) (hyb : G.Adj y (q b)) (hyc : G.Adj y (q c)) : False := by
  apply critical_no_sparse_seven_set hcrit hs hc (sixCliqueSevenSet q y)
    (sixCliqueSevenSet_card q hq y hy)
  intro z hz
  exact critical_six_clique_three_hooks_outside_small hcrit hr hn q hq hclique y hy
    a b c hab hac hbc hya hyb hyc z (Finset.mem_compl.mp hz)

theorem critical_six_clique_hooks_card_le_two
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hc : modCycleCount 7 G = 2880) (hn : 9 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (sixCliqueHooks G q y).card ≤ 2 := by
  classical
  let T : Finset (Fin 6) := Finset.univ.filter (fun i => G.Adj y (q i))
  have hT : sixCliqueHooks G q y = T := by
    ext i
    simp only [sixCliqueHooks, T, Finset.mem_filter]
  by_contra hlarge
  have hTlarge : 2 < T.card := by
    rw [← hT]
    omega
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hTlarge
  exact critical_six_clique_no_three_hooks hcrit hs hr hc hn q hq hclique y hy
    a b c hab hac hbc (Finset.mem_filter.mp ha).2
    (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc').2

theorem equality_six_clique_hooks_card_le_two (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hnot : ¬ IsCompleteOfOrder G 8)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) : (sixCliqueHooks G q y).card ≤ 2 :=
  critical_six_clique_hooks_card_le_two hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) hc
    (noncomplete_card_ge_nine hcrit (equality_shortSevenCycles hcrit hc)
      (equality_rainbowSevenCycles hcrit hc) hnot) q hq hclique y hy

end TaskH.Seven

#print axioms TaskH.Seven.critical_six_clique_no_three_hooks
#print axioms TaskH.Seven.critical_six_clique_hooks_card_le_two
#print axioms TaskH.Seven.equality_six_clique_hooks_card_le_two
