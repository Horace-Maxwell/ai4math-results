import Research.TaskH.Seven.SevenLocalCommonColors

/-! Original degree12 deleted colorings have common-color count0,4 or5.
The two remaining positive cases are explicit and are not called pure split. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_degreeTwelve_commonColors_empty_or_four_or_five
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) :
    F.commonColors = ∅ ∨ F.commonColors.card = 4 ∨ F.commonColors.card = 5 := by
  have hle : F.commonColors.card ≤ 5 := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ F.commonColors)
  have h1 : F.commonColors.card ≠ 1 := by
    intro h
    exact equality_degreeTwelve_commonColors_not_one_or_two hcrit hc hnot v c hv F (Or.inl h)
  have h2 : F.commonColors.card ≠ 2 := by
    intro h
    exact equality_degreeTwelve_commonColors_not_one_or_two hcrit hc hnot v c hv F (Or.inr h)
  have h3 := equality_degreeTwelve_commonColors_card_ne_three hcrit hc hnot v c hv F
  by_cases h0 : F.commonColors.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp h0)
  · have hh : F.commonColors.card = 4 ∨ F.commonColors.card = 5 := by omega
    exact Or.inr hh

end TaskH.Seven
#print axioms TaskH.Seven.equality_degreeTwelve_commonColors_empty_or_four_or_five
