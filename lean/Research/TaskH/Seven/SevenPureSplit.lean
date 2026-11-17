import Research.TaskH.Seven.SevenCommonFour

/-! All actual deleted colorings at an original degree12 root are pure split.
Every positive common-count branch was discharged on actual graph objects. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_degreeTwelve_commonColors_empty
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.commonColors = ∅ := by
  rcases equality_degreeTwelve_commonColors_empty_or_four_or_five hcrit hc hnot v c hv F
    with hzero | hfour | hfive
  · exact hzero
  · exact (equality_degreeTwelve_commonColors_card_ne_four hcrit hc hnot v c hv F hfour).elim
  · exact (equality_degreeTwelve_commonColors_card_ne_five hcrit hc hnot v c hv F hfive).elim

theorem equality_degreeTwelve_pureSplit
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.IsPureSplit :=
  (F.pureSplit_iff_commonColors_empty hcrit hc hnot hv).mpr
    (equality_degreeTwelve_commonColors_empty hcrit hc hnot v c hv F)

theorem equality_degree_twelve_all_colorings_pure_split
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) (hv : G.degree v = 12) :
    ∀ (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
      (F : DegreeTwelveFrame G v c), F.IsPureSplit := by
  intro c F
  exact equality_degreeTwelve_pureSplit hcrit hc hnot v c hv F

end TaskH.Seven
#print axioms TaskH.Seven.equality_degreeTwelve_commonColors_empty
#print axioms TaskH.Seven.equality_degreeTwelve_pureSplit
#print axioms TaskH.Seven.equality_degree_twelve_all_colorings_pure_split
