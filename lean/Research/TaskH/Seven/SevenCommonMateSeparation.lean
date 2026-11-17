import Research.TaskH.Seven.SevenCommonMateOutside

/-! The OUTSIDE representative/mate pools are disjoint by the actual path
b-r_l-a-r_i-z-mate_j. This is separate from internal R-to-mate no edges. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_rep_mate_outside_overlap_false
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j l : ↥F.commonColors) (hli : l ≠ i)
    (hcase : l = j ∨ i = j)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzi : G.Adj z.val (F.commonRep i).val)
    (hzj : G.Adj z.val (F.commonMate j).val) : False := by
  let a := (F.center 0).val
  let b := (F.center 1).val
  let ri := (F.commonRep i).val
  let rl := (F.commonRep l).val
  let s := (F.commonMate j).val
  have hliv : l.val ≠ i.val := fun he => hli (Subtype.ext he)
  have hrli : rl ≠ ri := F.leaf_leaf_ne hliv (F.commonRepSide l) (F.commonRepSide i)
  have hrls : rl ≠ s := F.commonRep_ne_commonMate l j
  have hris : ri ≠ s := F.commonRep_ne_commonMate i j
  have harl : a ≠ rl := F.center_leaf_ne 0 l.val (F.commonRepSide l)
  have hari : a ≠ ri := F.center_leaf_ne 0 i.val (F.commonRepSide i)
  have has : a ≠ s := F.center_leaf_ne 0 j.val (F.commonRepSide j + 1)
  have hbrl : b ≠ rl := F.center_leaf_ne 1 l.val (F.commonRepSide l)
  have hbri : b ≠ ri := F.center_leaf_ne 1 i.val (F.commonRepSide i)
  have hbs : b ≠ s := F.center_leaf_ne 1 j.val (F.commonRepSide j + 1)
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hza := outside_closed_ne_neighbor z.val hz (F.center 0)
  have hzb := outside_closed_ne_neighbor z.val hz (F.center 1)
  have hzri := outside_closed_ne_neighbor z.val hz (F.commonRep i)
  have hzrl := outside_closed_ne_neighbor z.val hz (F.commonRep l)
  have hzs := outside_closed_ne_neighbor z.val hz (F.commonMate j)
  let t : Fin 6 → V := ![b, rl, a, ri, z.val, s]
  have ht : Function.Injective t := by
    change Function.Injective ![b, rl, a, ri, z.val, s]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show b ≠ rl ∧ b ≠ a ∧ b ≠ ri ∧ b ≠ z.val ∧ b ≠ s from
          ⟨hbrl, Ne.symm hab, hbri, Ne.symm hzb, hbs⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show rl ≠ a ∧ rl ≠ ri ∧ rl ≠ z.val ∧ rl ≠ s from
          ⟨Ne.symm harl, hrli, Ne.symm hzrl, hrls⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show a ≠ ri ∧ a ≠ z.val ∧ a ≠ s from
          ⟨hari, Ne.symm hza, has⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show ri ≠ z.val ∧ ri ≠ s from ⟨Ne.symm hzri, hris⟩)
    exact injective_pair_iff_ne.mpr hzs
  have htv : ∀ m : Fin 6, t m ≠ v := by
    intro m
    fin_cases m
    · exact (F.center 1).property.ne.symm
    · exact (F.commonRep l).property.ne.symm
    · exact (F.center 0).property.ne.symm
    · exact (F.commonRep i).property.ne.symm
    · exact z.property
    · exact (F.commonMate j).property.ne.symm
  have hpath := rooted_five_path_colors_injective hr v c t ht htv
    (F.center 1).property (F.commonMate j).property
    (F.commonRep_adj_one l) (F.commonRep_adj_zero l).symm
    (F.commonRep_adj_zero i) hzi.symm hzj
  rcases hcase with hlj | hij
  · have he : c ⟨t 1, htv 1⟩ = c ⟨t 5, htv 5⟩ := by
      change neighborColor v c (F.commonRep l) = neighborColor v c (F.commonMate j)
      rw [F.commonRep_color, F.commonMate_color, hlj]
    have hh : (1 : Fin 6) = 5 := @hpath 1 5 he
    exact (by decide : (1 : Fin 6) ≠ 5) hh
  · have he : c ⟨t 3, htv 3⟩ = c ⟨t 5, htv 5⟩ := by
      change neighborColor v c (F.commonRep i) = neighborColor v c (F.commonMate j)
      rw [F.commonRep_color, F.commonMate_color, hij]
    have hh : (3 : Fin 6) = 5 := @hpath 3 5 he
    exact (by decide : (3 : Fin 6) ≠ 5) hh

theorem commonPoolHits_empty_at_mate_neighbor
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hcommon : 2 ≤ F.commonColors.card)
    (j : ↥F.commonColors)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzj : G.Adj z.val (F.commonMate j).val) : commonPoolHits F z.val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hzi := (mem_commonPoolHits F z.val i).mp hi
  by_cases hij : i = j
  · obtain ⟨q, hq, hqi⟩ := Finset.exists_mem_ne (by omega : 1 < F.commonColors.card) i.val
    let l : ↥F.commonColors := ⟨q, hq⟩
    have hli : l ≠ i := fun he => hqi (congrArg Subtype.val he)
    exact common_rep_mate_outside_overlap_false hr F i j l hli (Or.inr hij) z hz hzi hzj
  · exact common_rep_mate_outside_overlap_false hr F i j j (Ne.symm hij) (Or.inl rfl) z hz hzi hzj

end TaskH.Seven
#print axioms TaskH.Seven.common_rep_mate_outside_overlap_false
#print axioms TaskH.Seven.commonPoolHits_empty_at_mate_neighbor
