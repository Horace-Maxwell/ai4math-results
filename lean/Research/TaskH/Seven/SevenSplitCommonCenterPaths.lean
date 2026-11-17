import Research.TaskH.Seven.SevenSplitAdjacentPacking

/-! A real common outside center neighbor forces A independent and outside
A-capacity four. These are path statements in the same actual graph. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.common_center_A_independent
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1)
    (i j : Fin 5) (hij : i ≠ j) :
    ¬ G.Adj (F.splitA i).val (F.splitA j).val := by
  intro he
  obtain ⟨hwa, hwb⟩ := Finset.mem_inter.mp hw
  have hwO := (Finset.mem_filter.mp hwa).1
  have haw := (Finset.mem_filter.mp hwa).2
  have hbw := (Finset.mem_filter.mp hwb).2
  have hi := F.splitAB_adjacencies i (hF i)
  have hcc := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hA := F.splitA_injective.ne hij
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hwn := rootOutside_ne_neighbor hwO
  have hwv := rootOutside_ne_root hwO
  let f : Fin 7 → V := ![v, (F.splitB i).val, (F.center 1).val, w,
    (F.center 0).val, (F.splitA i).val, (F.splitA j).val]
  have hf : IsHeptagon G f := by
    refine ⟨?_, (F.splitB i).property, hi.2.2.1.symm, hbw, haw.symm,
      hi.1, he, (F.splitA j).property.symm⟩
    change Function.Injective ![v, (F.splitB i).val, (F.center 1).val, w,
      (F.center 0).val, (F.splitA i).val, (F.splitA j).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show v ≠ (F.splitB i).val ∧ v ≠ (F.center 1).val ∧ v ≠ w ∧
            v ≠ (F.center 0).val ∧ v ≠ (F.splitA i).val ∧ v ≠ (F.splitA j).val from
          ⟨(F.splitB i).property.ne, (F.center 1).property.ne, Ne.symm hwv,
            (F.center 0).property.ne, (F.splitA i).property.ne, (F.splitA j).property.ne⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitB i).val ≠ (F.center 1).val ∧ (F.splitB i).val ≠ w ∧
            (F.splitB i).val ≠ (F.center 0).val ∧ (F.splitB i).val ≠ (F.splitA i).val ∧
            (F.splitB i).val ≠ (F.splitA j).val from
          ⟨Ne.symm (hcb 1 i), Ne.symm (hwn (F.splitB i)), Ne.symm (hcb 0 i),
            Ne.symm (hcross i i), Ne.symm (hcross j i)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 1).val ≠ w ∧ (F.center 1).val ≠ (F.center 0).val ∧
            (F.center 1).val ≠ (F.splitA i).val ∧ (F.center 1).val ≠ (F.splitA j).val from
          ⟨Ne.symm (hwn (F.center 1)), Ne.symm hcc, hca 1 i, hca 1 j⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show w ≠ (F.center 0).val ∧ w ≠ (F.splitA i).val ∧ w ≠ (F.splitA j).val from
          ⟨hwn (F.center 0), hwn (F.splitA i), hwn (F.splitA j)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ (F.splitA i).val ∧ (F.center 0).val ≠ (F.splitA j).val from
          ⟨hca 0 i, hca 0 j⟩)
    exact injective_pair_iff_ne.mpr hA
  exact rainbow_heptagon_same_color_impossible hr v c f hf
    (F.splitB i).val (F.splitA i).val
    (F.splitB i).property.ne.symm (F.splitA i).property.ne.symm
    (F.splitAB_ne i).symm ⟨1, rfl⟩ ⟨5, rfl⟩
    ((F.splitB_color i).trans (F.splitA_color i).symm)

theorem DegreeTwelveFrame.common_center_outside_A_omits_hook
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1)
    (z : V) (hz : z ∈ rootOutside G v) :
    ∃ i : Fin 5, ¬ G.Adj z (F.splitA i).val := by
  classical
  by_contra h
  have hall : ∀ i : Fin 5, G.Adj z (F.splitA i).val := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨hwa, hwb⟩ := Finset.mem_inter.mp hw
  have hwO := (Finset.mem_filter.mp hwa).1
  have haw := (Finset.mem_filter.mp hwa).2
  have hbw := (Finset.mem_filter.mp hwb).2
  have hzw : z ≠ w := by
    intro he
    have hwX : w ∈ F.splitPoolA := Finset.mem_filter.mpr
      ⟨hwO, 0, by rw [← he]; exact hall 0⟩
    exact (Finset.disjoint_left.mp (F.pureSplit_centerPool_one_disjoint_A hr hF))
      hwb hwX
  have hi := F.splitAB_adjacencies 1 (hF 1)
  have hcc := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hA := F.splitA_injective.ne (by decide : (0 : Fin 5) ≠ 1)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hzn := rootOutside_ne_neighbor hz
  have hwn := rootOutside_ne_neighbor hwO
  let t : Fin 6 → V := ![(F.splitA 0).val, z, (F.splitA 1).val,
    (F.center 0).val, w, (F.center 1).val]
  have ht : Function.Injective t := by
    change Function.Injective ![(F.splitA 0).val, z, (F.splitA 1).val,
      (F.center 0).val, w, (F.center 1).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA 0).val ≠ z ∧ (F.splitA 0).val ≠ (F.splitA 1).val ∧
            (F.splitA 0).val ≠ (F.center 0).val ∧ (F.splitA 0).val ≠ w ∧
            (F.splitA 0).val ≠ (F.center 1).val from
          ⟨Ne.symm (hzn (F.splitA 0)), hA, Ne.symm (hca 0 0),
            Ne.symm (hwn (F.splitA 0)), Ne.symm (hca 1 0)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z ≠ (F.splitA 1).val ∧ z ≠ (F.center 0).val ∧ z ≠ w ∧
            z ≠ (F.center 1).val from
          ⟨hzn (F.splitA 1), hzn (F.center 0), hzw, hzn (F.center 1)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA 1).val ≠ (F.center 0).val ∧ (F.splitA 1).val ≠ w ∧
            (F.splitA 1).val ≠ (F.center 1).val from
          ⟨Ne.symm (hca 0 1), Ne.symm (hwn (F.splitA 1)), Ne.symm (hca 1 1)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ w ∧ (F.center 0).val ≠ (F.center 1).val from
          ⟨Ne.symm (hwn (F.center 0)), hcc⟩)
    exact injective_pair_iff_ne.mpr (hwn (F.center 1))
  have htv : ∀ l : Fin 6, t l ≠ v := by
    intro l
    fin_cases l
    · exact (F.splitA 0).property.ne.symm
    · exact rootOutside_ne_root hz
    · exact (F.splitA 1).property.ne.symm
    · exact (F.center 0).property.ne.symm
    · exact rootOutside_ne_root hwO
    · exact (F.center 1).property.ne.symm
  have hinj := rooted_five_path_colors_injective hr v c t ht htv
    (F.splitA 0).property (F.center 1).property
    (hall 0).symm (hall 1) hi.1.symm haw hbw.symm
  let zD : {x : V // x ≠ v} := ⟨z, rootOutside_ne_root hz⟩
  have hna : c zD ≠ (F.singletonIndex 0).val := by
    intro he
    have hcolor : c ⟨t 1, htv 1⟩ = c ⟨t 3, htv 3⟩ :=
      he.trans (F.center_color 0).symm
    have hh : (1 : Fin 6) = 3 := @hinj 1 3 hcolor
    exact (by decide : (1 : Fin 6) ≠ 3) hh
  have hnb : c zD ≠ (F.singletonIndex 1).val := by
    intro he
    have hcolor : c ⟨t 1, htv 1⟩ = c ⟨t 5, htv 5⟩ :=
      he.trans (F.center_color 1).symm
    have hh : (1 : Fin 6) = 5 := @hinj 1 5 hcolor
    exact (by decide : (1 : Fin 6) ≠ 5) hh
  have hnp : ∀ i : Fin 5, c zD ≠ (F.pairIndex i).val := by
    intro i he
    have hvalid := c.valid (show (G.induce {x | x ≠ v}).Adj zD (F.splitAD i) from hall i)
    exact hvalid (he.trans (F.splitA_color i).symm)
  rcases F.color_cases (c zD) with ⟨j, hj⟩ | ⟨i, hi⟩
  · fin_cases j
    · exact hna hj.symm
    · exact hnb hj.symm
  · exact hnp i hi.symm

theorem DegreeTwelveFrame.common_center_outside_A_capacity_four
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (w : V) (hw : w ∈ F.centerPool 0 ∩ F.centerPool 1)
    (z : V) (hz : z ∈ rootOutside G v) :
    ((Finset.univ : Finset (Fin 5)).filter
      (fun i => G.Adj z (F.splitA i).val)).card ≤ 4 := by
  obtain ⟨i, hi⟩ := F.common_center_outside_A_omits_hook hr hF w hw z hz
  have hsub : ((Finset.univ : Finset (Fin 5)).filter
      (fun j => G.Adj z (F.splitA j).val)) ⊆ Finset.univ.erase i := by
    intro j hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j⟩
    intro he
    exact hi (by rw [← he]; exact (Finset.mem_filter.mp hj).2)
  have hcard := Finset.card_le_card hsub
  simpa using hcard

end TaskH.Seven

#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_A_independent
#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_outside_A_omits_hook
#print axioms TaskH.Seven.DegreeTwelveFrame.common_center_outside_A_capacity_four
