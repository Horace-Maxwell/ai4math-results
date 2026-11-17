import Research.TaskH.Seven.SevenTwoColorResidualColors

/-! Actual residual color-class counts and final INTERNAL branch closure.
The residual card<=7 input is explicit; its original-graph derivation is
owned by a separate source branch and is not silently assumed proved. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.swapCenters_residualPool {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    F.swapCenters.residualPool = F.residualPool := by
  ext z
  simp only [DegreeTwelveFrame.residualPool, F.swapCenters_centerPool_zero,
    F.swapCenters_centerPool_one, F.swapCenters_splitPoolA hF, F.swapCenters_splitPoolB hF,
    Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem DegreeTwelveFrame.swapCenters_residualColorClass {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (k : Fin 7) :
    F.swapCenters.residualColorClass k = F.residualColorClass k := by
  simp only [DegreeTwelveFrame.residualColorClass, F.swapCenters_residualPool hF]

theorem DegreeTwelveFrame.swapCenters_singleton_zero_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) :
    (F.swapCenters.singletonIndex 0).val = (F.singletonIndex 1).val := by
  have hc := F.swapCenters.center_color 0
  rw [F.swapCenters_center_zero] at hc
  exact hc.symm.trans (F.center_color 1)

theorem equality_fixed_pureSplit_both_residual_colors_ge_two
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) :
    2 ≤ (F.residualColorClass (F.singletonIndex 0).val).card ∧
      2 ≤ (F.residualColorClass (F.singletonIndex 1).val).card := by
  obtain ⟨P⟩ := equality_exists_sevenPathSystem hcrit hc hnot hv F hF hsmall
  have hzero := P.alpha_residual_card_ge_two hcrit hc hnot hF hsmall
  have hswapF := F.swapCenters_pureSplit hF
  have hswapSmall : F.swapCenters.residualPool.card ≤ 7 := by
    simpa only [F.swapCenters_residualPool hF] using hsmall
  obtain ⟨Q⟩ := equality_exists_sevenPathSystem hcrit hc hnot hv F.swapCenters hswapF hswapSmall
  have hone := Q.alpha_residual_card_ge_two hcrit hc hnot hswapF hswapSmall
  rw [F.swapCenters_singleton_zero_color, F.swapCenters_residualColorClass hF] at hone
  exact ⟨hzero, hone⟩

theorem equality_fixed_pureSplit_residual_card_ge_eight
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) : 8 ≤ F.residualPool.card := by
  classical
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  obtain ⟨P⟩ := equality_exists_sevenPathSystem hcrit hc hnot hv F hF hsmall
  obtain ⟨hA, hB⟩ := equality_fixed_pureSplit_both_residual_colors_ge_two hcrit hc hnot hv F hF hsmall
  let A := F.residualColorClass (F.singletonIndex 0).val
  let B := F.residualColorClass (F.singletonIndex 1).val
  let T : Finset {x : V // x ≠ v} := Finset.univ.image (fun i : ↥P.indices => (P.paths i).getVert 3)
  have hTi : Function.Injective (fun i : ↥P.indices => (P.paths i).getVert 3) := by
    intro i j he
    exact P.odd_position_injective 3 (by decide) (by decide) (congrArg Subtype.val he)
  have hTcard : T.card = P.indices.card := by
    calc
      T.card = (Finset.univ : Finset ↥P.indices).card := Finset.card_image_of_injective _ hTi
      _ = P.indices.card := by simp
  have hTsub : ∀ z ∈ T, z.val ∈ F.residualPool := by
    intro z hz
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
    exact (P.middle_residual hr hF i).1
  have hTdis (j : Fin 2) : Disjoint T (F.residualColorClass (F.singletonIndex j).val) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzj
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
    have hpair := P.odd_color i 3 (by decide) (by decide)
    have hsingle := (Finset.mem_filter.mp hzj).2.2
    exact F.pairColor_ne_singleton i.val j (hpair.symm.trans hsingle)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    have hca := (Finset.mem_filter.mp hzA).2.2
    have hcb := (Finset.mem_filter.mp hzB).2.2
    exact (F.singletonColor_injective.ne (by decide : (0 : Fin 2) ≠ 1)) (hca.symm.trans hcb)
  have hTAB : Disjoint (T ∪ A) B := by
    apply Finset.disjoint_left.mpr
    intro z hz hzB
    rcases Finset.mem_union.mp hz with hzT | hzA
    · exact Finset.disjoint_left.mp (hTdis 1) hzT hzB
    · exact Finset.disjoint_left.mp hAB hzA hzB
  let U := T ∪ A ∪ B
  have hUcard : U.card = T.card + A.card + B.card := by
    rw [Finset.card_union_of_disjoint hTAB, Finset.card_union_of_disjoint (hTdis 0)]
  have hUsub : U.image Subtype.val ⊆ F.residualPool := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_union.mp hw with hwTA | hwB
    · rcases Finset.mem_union.mp hwTA with hwT | hwA
      · exact hTsub w hwT
      · exact (Finset.mem_filter.mp hwA).2.1
    · exact (Finset.mem_filter.mp hwB).2.1
  have hUimage : (U.image Subtype.val).card = U.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hZ := Finset.card_le_card hUsub
  rw [hUimage, hUcard, hTcard] at hZ
  have hfour := P.card_ge_four
  change 2 ≤ A.card at hA
  change 2 ≤ B.card at hB
  omega

theorem equality_fixed_pureSplit_false_of_residual_card
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) : False := by
  have hlarge := equality_fixed_pureSplit_residual_card_ge_eight hcrit hc hnot hv F hF hsmall
  omega

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_residualPool
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_residualColorClass
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_singleton_zero_color
#print axioms TaskH.Seven.equality_fixed_pureSplit_both_residual_colors_ge_two
#print axioms TaskH.Seven.equality_fixed_pureSplit_residual_card_ge_eight
#print axioms TaskH.Seven.equality_fixed_pureSplit_false_of_residual_card
