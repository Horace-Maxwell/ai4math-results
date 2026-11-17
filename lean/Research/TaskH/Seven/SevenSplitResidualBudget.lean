import Research.TaskH.Seven.SevenSplitCenterOutside

/-! The actual four-pool union occupies at least26 of the at most33 outside
vertices. The only allowed own-pool intersections have cardinal at most one;
unclassified outside vertices remain in the actual residual definition. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem four_pool_union_card_ge_twenty_six {A : Type u}
    (S T X Y : Finset A)
    (hST : Disjoint S T) (hSY : Disjoint S Y)
    (hTX : Disjoint T X) (hXY : Disjoint X Y)
    (hSX : (S ∩ X).card ≤ 1) (hTY : (T ∩ Y).card ≤ 1)
    (hS : 6 ≤ S.card) (hT : 6 ≤ T.card) (hX : 8 ≤ X.card) (hY : 8 ≤ Y.card) :
    26 ≤ (S ∪ T ∪ X ∪ Y).card := by
  classical
  have hdis : Disjoint (S ∪ X) (T ∪ Y) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    rcases Finset.mem_union.mp hz with hzS | hzX
    · rcases Finset.mem_union.mp hw with hwT | hwY
      · exact Finset.disjoint_left.mp hST hzS hwT
      · exact Finset.disjoint_left.mp hSY hzS hwY
    · rcases Finset.mem_union.mp hw with hwT | hwY
      · exact Finset.disjoint_left.mp hTX hwT hzX
      · exact Finset.disjoint_left.mp hXY hzX hwY
  have h0 := Finset.card_union_add_card_inter S X
  have h1 := Finset.card_union_add_card_inter T Y
  have hcard := Finset.card_union_of_disjoint hdis
  have he : S ∪ T ∪ X ∪ Y = (S ∪ X) ∪ (T ∪ Y) := by
    ext z
    simp only [Finset.mem_union]
    tauto
  rw [he, hcard]
  omega

theorem DegreeTwelveFrame.pureSplit_residualPool_card_le_seven
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : F.residualPool.card ≤ 7 := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hST := equality_degreeTwelve_centerPools_disjoint hcrit hc hnot hv F hF
  have hSY := F.pureSplit_centerPool_zero_disjoint_B hr hF
  have hTX := F.pureSplit_centerPool_one_disjoint_A hr hF
  have hXY := F.pureSplit_splitPools_disjoint hr hF
  have hSX := F.pureSplit_own_A_pool_card_le_one hcrit hc hnot hv hF
  have hTY := F.pureSplit_own_B_pool_card_le_one hcrit hc hnot hv hF
  have hS := F.pureSplit_centerPool_zero_card_ge_six hcrit hc hnot hv hF
  have hT := F.pureSplit_centerPool_one_card_ge_six hcrit hc hnot hv hF
  have hX := F.pureSplit_splitPoolA_card_ge_eight hcrit hc hnot hF
  have hY := F.pureSplit_splitPoolB_card_ge_eight hcrit hc hnot hF
  let U := F.centerPool 0 ∪ F.centerPool 1 ∪ F.splitPoolA ∪ F.splitPoolB
  have hU : 26 ≤ U.card := four_pool_union_card_ge_twenty_six
    (F.centerPool 0) (F.centerPool 1) F.splitPoolA F.splitPoolB
    hST hSY hTX hXY hSX hTY hS hT hX hY
  have hsub : U ⊆ rootOutside G v := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hzY
    · rcases Finset.mem_union.mp hz with hz | hzX
      · rcases Finset.mem_union.mp hz with hzS | hzT
        · exact (Finset.mem_filter.mp hzS).1
        · exact (Finset.mem_filter.mp hzT).1
      · exact (Finset.mem_filter.mp hzX).1
    · exact (Finset.mem_filter.mp hzY).1
  have hp := Finset.card_sdiff_add_card_eq_card hsub
  change F.residualPool.card + U.card = (rootOutside G v).card at hp
  have hn : (rootOutside G v).card ≤ 33 := by
    change ((insert v (G.neighborFinset v))ᶜ : Finset V).card ≤ 33
    exact equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  omega

theorem equality_degreeTwelve_residualPool_card_le_seven
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.residualPool.card ≤ 7 :=
  F.pureSplit_residualPool_card_le_seven hcrit hc hnot hv
    (equality_degreeTwelve_pureSplit hcrit hc hnot v c hv F)

end TaskH.Seven
#print axioms TaskH.Seven.four_pool_union_card_ge_twenty_six
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_residualPool_card_le_seven
#print axioms TaskH.Seven.equality_degreeTwelve_residualPool_card_le_seven
