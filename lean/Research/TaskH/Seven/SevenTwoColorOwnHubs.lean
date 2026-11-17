import Research.TaskH.Seven.SevenTwoColorAlphaPool
import Research.TaskH.Seven.SevenTwoColorHubBudget
import Research.TaskH.Seven.SevenSplitLeafPoolSeparation

/-! Actual own-pool intersections. Hub coincidence is handled by the two
explicit cases of the finite lemma: a large hub permits T={that same hub};
two small disjoint hubs exclude each other as well as every third point. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def DegreeTwelveFrame.alphaHubSet {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset V := F.alphaQPool.image Subtype.val

noncomputable def DegreeTwelveFrame.Qlabels {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : V) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => G.Adj z (F.splitB i).val)

theorem DegreeTwelveFrame.alphaQPool_outside {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z : {x : V // x ≠ v}) (hz : z ∈ F.alphaQPool) : z.val ∈ rootOutside G v := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  apply Finset.mem_compl.mpr
  intro hin
  have hcol := (Finset.mem_filter.mp hz).2.1
  obtain ⟨j, hzj⟩ := (Finset.mem_filter.mp hz).2.2
  rcases Finset.mem_insert.mp hin with he | he
  · exact z.property he
  · have hadj := (G.mem_neighborFinset v z.val).mp he
    have heq := (F.singleton_fiber_as_deleted 0 z hadj).mp hcol
    rw [heq] at hzj
    exact (F.splitAB_adjacencies j (hF j)).2.2.2 hzj

theorem DegreeTwelveFrame.alphaHubSet_outside {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (z : V)
    (hz : z ∈ F.alphaHubSet) : z ∈ rootOutside G v := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact F.alphaQPool_outside hF w hw

theorem DegreeTwelveFrame.alphaHubSet_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : V) (hz : z ∈ F.alphaHubSet)
    (hzv : z ≠ v) : c ⟨z, hzv⟩ = (F.singletonIndex 0).val := by
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hz
  have hwe : w = ⟨z, hzv⟩ := Subtype.ext he
  have hc := (Finset.mem_filter.mp hw).2.1
  simpa only [hwe] using hc

theorem DegreeTwelveFrame.alpha_hub_forbids_own_labels
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z t : V) (hz : z ∈ F.alphaHubSet)
    (ht : t ∈ F.centerPool 1 ∩ F.splitPoolB) (hzt : z ≠ t)
    (i j l : Fin 5) (hi : i ∈ F.Qlabels z) (hj : j ∈ F.Qlabels z)
    (hij : i ≠ j) (hl : l ∈ F.Qlabels t) (hli : l ≠ i) (hlj : l ≠ j) : False := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have hzO := F.alphaHubSet_outside hF z hz
  have htO := (Finset.mem_filter.mp (Finset.mem_inter.mp ht).1).1
  have hbt := (Finset.mem_filter.mp (Finset.mem_inter.mp ht).1).2
  have hzi := (Finset.mem_filter.mp hi).2
  have hzj := (Finset.mem_filter.mp hj).2
  have htl := (Finset.mem_filter.mp hl).2
  have hjb := (F.splitAB_adjacencies j (hF j)).2.2.1.symm
  have hBiBj := F.splitB_injective.ne hij
  have hBiBl := F.splitB_injective.ne (Ne.symm hli)
  have hBjBl := F.splitB_injective.ne (Ne.symm hlj)
  have hcb := F.center_splitB_ne
  have hzn := rootOutside_ne_neighbor hzO
  have htn := rootOutside_ne_neighbor htO
  let q : Fin 6 → V := ![(F.splitB i).val, z, (F.splitB j).val,
    (F.center 1).val, t, (F.splitB l).val]
  have hq : Function.Injective q := by
    change Function.Injective ![(F.splitB i).val, z, (F.splitB j).val,
      (F.center 1).val, t, (F.splitB l).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitB i).val ≠ z ∧ (F.splitB i).val ≠ (F.splitB j).val ∧
            (F.splitB i).val ≠ (F.center 1).val ∧ (F.splitB i).val ≠ t ∧
            (F.splitB i).val ≠ (F.splitB l).val from
          ⟨Ne.symm (hzn (F.splitB i)), hBiBj, Ne.symm (hcb 1 i),
            Ne.symm (htn (F.splitB i)), hBiBl⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z ≠ (F.splitB j).val ∧ z ≠ (F.center 1).val ∧ z ≠ t ∧
            z ≠ (F.splitB l).val from
          ⟨hzn (F.splitB j), hzn (F.center 1), hzt, hzn (F.splitB l)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitB j).val ≠ (F.center 1).val ∧ (F.splitB j).val ≠ t ∧
            (F.splitB j).val ≠ (F.splitB l).val from
          ⟨Ne.symm (hcb 1 j), Ne.symm (htn (F.splitB j)), hBjBl⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 1).val ≠ t ∧ (F.center 1).val ≠ (F.splitB l).val from
          ⟨Ne.symm (htn (F.center 1)), hcb 1 l⟩)
    exact injective_pair_iff_ne.mpr (htn (F.splitB l))
  have hqv : ∀ a : Fin 6, q a ≠ v := by
    intro a
    fin_cases a
    · exact (F.splitB i).property.ne.symm
    · exact rootOutside_ne_root hzO
    · exact (F.splitB j).property.ne.symm
    · exact (F.center 1).property.ne.symm
    · exact rootOutside_ne_root htO
    · exact (F.splitB l).property.ne.symm
  have hna : q 1 ≠ (singletonNeighbor v c (F.singletonIndex 0)).val :=
    rootOutside_ne_neighbor hzO (F.center 0)
  have hforbid := singleton_color_forbidden_on_rooted_five_path hr v c (F.singletonIndex 0)
    q hq hqv (F.splitB i).property (F.splitB l).property hzi.symm hzj hjb hbt htl 1 hna
  exact hforbid (F.alphaHubSet_color z hz (rootOutside_ne_root hzO))

theorem DegreeTwelveFrame.pureSplit_own_B_pool_card_le_one
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    (F.centerPool 1 ∩ F.splitPoolB).card ≤ 1 := by
  let : DecidableEq (Fin 5) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨hpool, hfour, hhit⟩ := equality_fixed_pureSplit_two_hubs_cover_four_pairs
    hcrit hc hnot hv F hF
  have hU : F.alphaHubSet.card ≤ 2 :=
    (Finset.card_image_le).trans hpool
  have hsub : F.connectedPairSet ⊆ F.alphaHubSet.biUnion F.Qlabels := by
    intro i hi
    obtain ⟨z, hz, hzi⟩ := hhit i hi
    apply Finset.mem_biUnion.mpr
    refine ⟨z.val, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩
  have hcover : 4 ≤ (F.alphaHubSet.biUnion F.Qlabels).card :=
    hfour.trans (Finset.card_le_card hsub)
  apply twoColor_two_hubs_own_pool_card_le_one F.alphaHubSet
    (F.centerPool 1 ∩ F.splitPoolB) F.Qlabels hU hcover
  · intro t ht
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp (Finset.mem_inter.mp ht).2).2
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · intro z hz t ht hzt i hi j hj hij l hl hli hlj
    exact F.alpha_hub_forbids_own_labels (equality_rainbowSevenCycles hcrit hc)
      hF z t hz ht hzt i j l hi hj hij hl hli hlj

theorem DegreeTwelveFrame.pureSplit_own_A_pool_card_le_one
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    (F.centerPool 0 ∩ F.splitPoolA).card ≤ 1 := by
  have h := F.swapCenters.pureSplit_own_B_pool_card_le_one hcrit hc hnot hv
    (F.swapCenters_pureSplit hF)
  simpa only [F.swapCenters_centerPool_one, F.swapCenters_splitPoolB hF] using h

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.alphaHubSet
#print axioms TaskH.Seven.DegreeTwelveFrame.Qlabels
#print axioms TaskH.Seven.DegreeTwelveFrame.alphaQPool_outside
#print axioms TaskH.Seven.DegreeTwelveFrame.alphaHubSet_outside
#print axioms TaskH.Seven.DegreeTwelveFrame.alphaHubSet_color
#print axioms TaskH.Seven.DegreeTwelveFrame.alpha_hub_forbids_own_labels
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_own_B_pool_card_le_one
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_own_A_pool_card_le_one
