import Research.TaskH.Seven.SevenSplitCenterSymmetry

/-! The two complete outside leaf pools are disjoint and have no cross edge.
The equal-index shared-point case is a genuine C7, not a C6 shortcut. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.pureSplit_no_shared_split_hook
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z : V) (hz : z ∈ rootOutside G v) (i j : Fin 5)
    (hzi : G.Adj z (F.splitA i).val) (hzj : G.Adj z (F.splitB j).val) : False := by
  have hi := F.splitAB_adjacencies i (hF i)
  have hj := F.splitAB_adjacencies j (hF j)
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hzn := rootOutside_ne_neighbor hz
  have hzv := rootOutside_ne_root hz
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki⟩ : ∃ k : Fin 5, k ≠ i := exists_ne i
    have hk := F.splitAB_adjacencies k (hF k)
    have hA := F.splitA_injective.ne hki
    let f : Fin 7 → V := ![(F.splitA i).val, z, (F.splitB i).val,
      (F.center 1).val, v, (F.splitA k).val, (F.center 0).val]
    have hf : IsHeptagon G f := by
      refine ⟨?_, hzi.symm, hzj, hi.2.2.1.symm,
        (F.center 1).property.symm, (F.splitA k).property, hk.1.symm, hi.1⟩
      change Function.Injective ![(F.splitA i).val, z, (F.splitB i).val, (F.center 1).val, v, (F.splitA k).val, (F.center 0).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ (F.splitB i).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ v ∧ (F.splitA i).val ≠ (F.splitA k).val ∧ (F.splitA i).val ≠ (F.center 0).val from
            ⟨(Ne.symm (hzn (F.splitA i))), (hcross i i), (Ne.symm (hca 1 i)), (Ne.symm ((F.splitA i).property.ne)), (Ne.symm (hA)), (Ne.symm (hca 0 i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (F.splitB i).val ∧ z ≠ (F.center 1).val ∧ z ≠ v ∧ z ≠ (F.splitA k).val ∧ z ≠ (F.center 0).val from
            ⟨(hzn (F.splitB i)), (hzn (F.center 1)), (hzv), (hzn (F.splitA k)), (hzn (F.center 0))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB i).val ≠ (F.center 1).val ∧ (F.splitB i).val ≠ v ∧ (F.splitB i).val ≠ (F.splitA k).val ∧ (F.splitB i).val ≠ (F.center 0).val from
            ⟨(Ne.symm (hcb 1 i)), (Ne.symm ((F.splitB i).property.ne)), (Ne.symm (hcross k i)), (Ne.symm (hcb 0 i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 1).val ≠ v ∧ (F.center 1).val ≠ (F.splitA k).val ∧ (F.center 1).val ≠ (F.center 0).val from
            ⟨(Ne.symm ((F.center 1).property.ne)), (hca 1 k), (Ne.symm (hab))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show v ≠ (F.splitA k).val ∧ v ≠ (F.center 0).val from
            ⟨((F.splitA k).property.ne), ((F.center 0).property.ne)⟩)
      exact injective_pair_iff_ne.mpr (Ne.symm (hca 0 k))
    exact rainbow_heptagon_same_color_impossible hr v c f hf
      (F.splitA i).val (F.splitB i).val
      (F.splitA i).property.ne.symm (F.splitB i).property.ne.symm
      (F.splitAB_ne i) ⟨0, rfl⟩ ⟨2, rfl⟩
      ((F.splitA_color i).trans (F.splitB_color i).symm)
  · have hB := F.splitB_injective.ne hij
    let t : Fin 6 → V := ![(F.splitB i).val, (F.center 1).val,
      (F.splitB j).val, z, (F.splitA i).val, (F.center 0).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitB i).val, (F.center 1).val, (F.splitB j).val, z, (F.splitA i).val, (F.center 0).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB i).val ≠ (F.center 1).val ∧ (F.splitB i).val ≠ (F.splitB j).val ∧ (F.splitB i).val ≠ z ∧ (F.splitB i).val ≠ (F.splitA i).val ∧ (F.splitB i).val ≠ (F.center 0).val from
            ⟨(Ne.symm (hcb 1 i)), (hB), (Ne.symm (hzn (F.splitB i))), (Ne.symm (hcross i i)), (Ne.symm (hcb 0 i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 1).val ≠ (F.splitB j).val ∧ (F.center 1).val ≠ z ∧ (F.center 1).val ≠ (F.splitA i).val ∧ (F.center 1).val ≠ (F.center 0).val from
            ⟨(hcb 1 j), (Ne.symm (hzn (F.center 1))), (hca 1 i), (Ne.symm (hab))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB j).val ≠ z ∧ (F.splitB j).val ≠ (F.splitA i).val ∧ (F.splitB j).val ≠ (F.center 0).val from
            ⟨(Ne.symm (hzn (F.splitB j))), (Ne.symm (hcross i j)), (Ne.symm (hcb 0 j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (F.splitA i).val ∧ z ≠ (F.center 0).val from
            ⟨(hzn (F.splitA i)), (hzn (F.center 0))⟩)
      exact injective_pair_iff_ne.mpr (Ne.symm (hca 0 i))
    have htv : ∀ l : Fin 6, t l ≠ v := by
      intro l
      fin_cases l
      · exact (F.splitB i).property.ne.symm
      · exact (F.center 1).property.ne.symm
      · exact (F.splitB j).property.ne.symm
      · exact hzv
      · exact (F.splitA i).property.ne.symm
      · exact (F.center 0).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv
      (F.splitB i).property (F.center 0).property
      hi.2.2.1.symm hj.2.2.1 hzj.symm hzi hi.1.symm
      0 4 (by decide) ((F.splitB_color i).trans (F.splitA_color i).symm)

theorem DegreeTwelveFrame.pureSplit_splitPools_disjoint
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    Disjoint F.splitPoolA F.splitPoolB := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨hzO, i, hzi⟩ := Finset.mem_filter.mp hz
  obtain ⟨j, hzj⟩ := (Finset.mem_filter.mp hw).2
  exact F.pureSplit_no_shared_split_hook hr hF z hzO i j hzi hzj

theorem DegreeTwelveFrame.pureSplit_splitPools_no_edge
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z w : V) (hz : z ∈ F.splitPoolA) (hw : w ∈ F.splitPoolB) :
    ¬ G.Adj z w := by
  intro hzw
  obtain ⟨hzO, i, hzi⟩ := Finset.mem_filter.mp hz
  obtain ⟨hwO, j, hwj⟩ := Finset.mem_filter.mp hw
  have hi := F.splitAB_adjacencies i (hF i)
  have hj := F.splitAB_adjacencies j (hF j)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hzn := rootOutside_ne_neighbor hzO
  have hwn := rootOutside_ne_neighbor hwO
  have hne := hzw.ne
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki⟩ : ∃ k : Fin 5, k ≠ i := exists_ne i
    have hk := F.splitAB_adjacencies k (hF k)
    have hA := F.splitA_injective.ne hki
    let t : Fin 6 → V := ![(F.splitA k).val, (F.center 0).val,
      (F.splitA i).val, z, w, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA k).val, (F.center 0).val, (F.splitA i).val, z, w, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA k).val ≠ (F.center 0).val ∧ (F.splitA k).val ≠ (F.splitA i).val ∧ (F.splitA k).val ≠ z ∧ (F.splitA k).val ≠ w ∧ (F.splitA k).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (hca 0 k)), (hA), (Ne.symm (hzn (F.splitA k))), (Ne.symm (hwn (F.splitA k))), (hcross k i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (F.splitA i).val ∧ (F.center 0).val ≠ z ∧ (F.center 0).val ≠ w ∧ (F.center 0).val ≠ (F.splitB i).val from
            ⟨(hca 0 i), (Ne.symm (hzn (F.center 0))), (Ne.symm (hwn (F.center 0))), (hcb 0 i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ w ∧ (F.splitA i).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (hzn (F.splitA i))), (Ne.symm (hwn (F.splitA i))), (hcross i i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ w ∧ z ≠ (F.splitB i).val from
            ⟨(hne), (hzn (F.splitB i))⟩)
      exact injective_pair_iff_ne.mpr (hwn (F.splitB i))
    have htv : ∀ l : Fin 6, t l ≠ v := by
      intro l
      fin_cases l
      · exact (F.splitA k).property.ne.symm
      · exact (F.center 0).property.ne.symm
      · exact (F.splitA i).property.ne.symm
      · exact rootOutside_ne_root hzO
      · exact rootOutside_ne_root hwO
      · exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv
      (F.splitA k).property (F.splitB i).property
      hk.1.symm hi.1 hzi.symm hzw hwj
      2 5 (by decide) ((F.splitA_color i).trans (F.splitB_color i).symm)
  · have hB := F.splitB_injective.ne hij
    let t : Fin 6 → V := ![(F.splitA i).val, z, w,
      (F.splitB j).val, (F.center 1).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, z, w, (F.splitB j).val, (F.center 1).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ w ∧ (F.splitA i).val ≠ (F.splitB j).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (hzn (F.splitA i))), (Ne.symm (hwn (F.splitA i))), (hcross i j), (Ne.symm (hca 1 i)), (hcross i i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ w ∧ z ≠ (F.splitB j).val ∧ z ≠ (F.center 1).val ∧ z ≠ (F.splitB i).val from
            ⟨(hne), (hzn (F.splitB j)), (hzn (F.center 1)), (hzn (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show w ≠ (F.splitB j).val ∧ w ≠ (F.center 1).val ∧ w ≠ (F.splitB i).val from
            ⟨(hwn (F.splitB j)), (hwn (F.center 1)), (hwn (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB j).val ≠ (F.center 1).val ∧ (F.splitB j).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (hcb 1 j)), (Ne.symm (hB))⟩)
      exact injective_pair_iff_ne.mpr (hcb 1 i)
    have htv : ∀ l : Fin 6, t l ≠ v := by
      intro l
      fin_cases l
      · exact (F.splitA i).property.ne.symm
      · exact rootOutside_ne_root hzO
      · exact rootOutside_ne_root hwO
      · exact (F.splitB j).property.ne.symm
      · exact (F.center 1).property.ne.symm
      · exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv
      (F.splitA i).property (F.splitB i).property
      hzi.symm hzw hwj hj.2.2.1.symm hi.2.2.1
      0 5 (by decide) ((F.splitA_color i).trans (F.splitB_color i).symm)

end TaskH.Seven

#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_no_shared_split_hook
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_splitPools_disjoint
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_splitPools_no_edge
