import Research.TaskH.Seven.SevenSplitLeafPoolSeparation
import Research.TaskH.Seven.SevenTwoColorFrameSwap

/-! The adjacent-center internal branch has matching A-neighborhoods and
outside A-capacity one. All restrictions come from actual length-five paths.
The finite degree/cardinality contradiction is a separate transport. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.split_neighbor_cases {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : G.neighborSet v) :
    (∃ j : Fin 2, z.val = (F.center j).val) ∨
      ∃ i : Fin 5, z.val = (F.splitA i).val ∨ z.val = (F.splitB i).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  rcases F.color_cases (neighborColor v c z) with ⟨j, hj⟩ | ⟨i, hi⟩
  · left
    exact ⟨j, congrArg Subtype.val
      (singletonNeighbor_eq_of_color v c (F.singletonIndex j) z hj.symm)⟩
  · right
    let zD := twoColorNeighborDeleted v z
    have hz : c zD = (F.pairIndex i).val := hi.symm
    rcases (F.pair_fiber_as_deleted i zD z.property).mp hz with he | he
    · exact ⟨i, Or.inl (congrArg (fun w : {x : V // x ≠ v} => w.val) he)⟩
    · exact ⟨i, Or.inr (congrArg (fun w : {x : V // x ≠ v} => w.val) he)⟩

theorem DegreeTwelveFrame.adjacent_centers_forbids_A_two_step
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hab : G.Adj (F.center 0).val (F.center 1).val)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hijE : G.Adj (F.splitA i).val (F.splitA j).val)
    (hjkE : G.Adj (F.splitA j).val (F.splitA k).val) : False := by
  have hi := F.splitAB_adjacencies i (hF i)
  have hk := F.splitAB_adjacencies k (hF k)
  have hcc := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hAij := F.splitA_injective.ne hij
  have hAik := F.splitA_injective.ne hik
  have hAjk := F.splitA_injective.ne hjk
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  let t : Fin 6 → G.neighborSet v := ![F.splitA i, F.splitA j, F.splitA k,
    F.center 0, F.center 1, F.splitB i]
  have ht : Function.Injective t := by
    change Function.Injective ![F.splitA i, F.splitA j, F.splitA k, F.center 0, F.center 1, F.splitB i]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show F.splitA i ≠ F.splitA j ∧ F.splitA i ≠ F.splitA k ∧ F.splitA i ≠ F.center 0 ∧ F.splitA i ≠ F.center 1 ∧ F.splitA i ≠ F.splitB i from
          ⟨(fun he => (hAij) (congrArg Subtype.val he)), (fun he => (hAik) (congrArg Subtype.val he)), (fun he => (Ne.symm (hca 0 i)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hca 1 i)) (congrArg Subtype.val he)), (fun he => (hcross i i) (congrArg Subtype.val he))⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show F.splitA j ≠ F.splitA k ∧ F.splitA j ≠ F.center 0 ∧ F.splitA j ≠ F.center 1 ∧ F.splitA j ≠ F.splitB i from
          ⟨(fun he => (hAjk) (congrArg Subtype.val he)), (fun he => (Ne.symm (hca 0 j)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hca 1 j)) (congrArg Subtype.val he)), (fun he => (hcross j i) (congrArg Subtype.val he))⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show F.splitA k ≠ F.center 0 ∧ F.splitA k ≠ F.center 1 ∧ F.splitA k ≠ F.splitB i from
          ⟨(fun he => (Ne.symm (hca 0 k)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hca 1 k)) (congrArg Subtype.val he)), (fun he => (hcross k i) (congrArg Subtype.val he))⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show F.center 0 ≠ F.center 1 ∧ F.center 0 ≠ F.splitB i from
          ⟨(fun he => (hcc) (congrArg Subtype.val he)), (fun he => (hcb 0 i) (congrArg Subtype.val he))⟩)
    exact injective_pair_iff_ne.mpr (fun he => (hcb 1 i) (congrArg Subtype.val he))
  exact neighbor_five_path_same_color_false hr v c t ht
    hijE hjkE hk.1.symm hab hi.2.2.1
    0 5 (by decide) ((F.splitA_color i).trans (F.splitB_color i).symm)

theorem DegreeTwelveFrame.adjacent_centers_A_internal_capacity
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hab : G.Adj (F.center 0).val (F.center 1).val) (i : Fin 5) :
    ((Finset.univ : Finset (Fin 5)).filter
      (fun j => G.Adj (F.splitA i).val (F.splitA j).val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hij := (Finset.mem_filter.mp hj).2
  have hik := (Finset.mem_filter.mp hk).2
  have hji : j ≠ i := fun he => hij.ne (congrArg (fun l => (F.splitA l).val) he.symm)
  have hik' : i ≠ k := fun he => hik.ne (congrArg (fun l => (F.splitA l).val) he)
  by_contra hjk
  exact F.adjacent_centers_forbids_A_two_step hr hF hab j i k hji hjk hik'
    hij.symm hik

theorem DegreeTwelveFrame.adjacent_centers_outside_A_capacity
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hab : G.Adj (F.center 0).val (F.center 1).val)
    (z : V) (hz : z ∈ rootOutside G v) :
    ((Finset.univ : Finset (Fin 5)).filter
      (fun i => G.Adj z (F.splitA i).val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hzi := (Finset.mem_filter.mp hi).2
  have hzj := (Finset.mem_filter.mp hj).2
  by_contra hij
  have hia := F.splitAB_adjacencies i (hF i)
  have hja := F.splitAB_adjacencies j (hF j)
  have hcc := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hA := F.splitA_injective.ne hij
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hzn := rootOutside_ne_neighbor hz
  let t : Fin 6 → V := ![(F.splitA i).val, z, (F.splitA j).val,
    (F.center 0).val, (F.center 1).val, (F.splitB i).val]
  have ht : Function.Injective t := by
    change Function.Injective ![(F.splitA i).val, z, (F.splitA j).val, (F.center 0).val, (F.center 1).val, (F.splitB i).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ (F.splitA j).val ∧ (F.splitA i).val ≠ (F.center 0).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB i).val from
          ⟨(Ne.symm (hzn (F.splitA i))), (hA), (Ne.symm (hca 0 i)), (Ne.symm (hca 1 i)), (hcross i i)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z ≠ (F.splitA j).val ∧ z ≠ (F.center 0).val ∧ z ≠ (F.center 1).val ∧ z ≠ (F.splitB i).val from
          ⟨(hzn (F.splitA j)), (hzn (F.center 0)), (hzn (F.center 1)), (hzn (F.splitB i))⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA j).val ≠ (F.center 0).val ∧ (F.splitA j).val ≠ (F.center 1).val ∧ (F.splitA j).val ≠ (F.splitB i).val from
          ⟨(Ne.symm (hca 0 j)), (Ne.symm (hca 1 j)), (hcross j i)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ (F.center 1).val ∧ (F.center 0).val ≠ (F.splitB i).val from
          ⟨(hcc), (hcb 0 i)⟩)
    exact injective_pair_iff_ne.mpr (hcb 1 i)
  have htv : ∀ l : Fin 6, t l ≠ v := by
    intro l
    fin_cases l
    · exact (F.splitA i).property.ne.symm
    · exact rootOutside_ne_root hz
    · exact (F.splitA j).property.ne.symm
    · exact (F.center 0).property.ne.symm
    · exact (F.center 1).property.ne.symm
    · exact (F.splitB i).property.ne.symm
  exact rooted_five_path_same_color_false hr v c t ht htv
    (F.splitA i).property (F.splitB i).property
    hzi.symm hzj hja.1.symm hab hia.2.2.1
    0 5 (by decide) ((F.splitA_color i).trans (F.splitB_color i).symm)

end TaskH.Seven

#print axioms TaskH.Seven.DegreeTwelveFrame.split_neighbor_cases
#print axioms TaskH.Seven.DegreeTwelveFrame.adjacent_centers_forbids_A_two_step
#print axioms TaskH.Seven.DegreeTwelveFrame.adjacent_centers_A_internal_capacity
#print axioms TaskH.Seven.DegreeTwelveFrame.adjacent_centers_outside_A_capacity
