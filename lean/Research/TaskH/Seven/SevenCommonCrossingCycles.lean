import Research.TaskH.Seven.SevenCommonCaseReduction

/-! A local actual C7 excludes intersecting nonidentical multi-representative
labels of same-color outside vertices. No fourth/fifth representative is used. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_three_rep_crossing_same_color_false
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j k : ↥F.commonColors)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (z w : {x : V // x ≠ v})
    (hz : z.val ∉ insert v (G.neighborFinset v))
    (hw : w.val ∉ insert v (G.neighborFinset v)) (hzw : z.val ≠ w.val)
    (hzi : G.Adj z.val (F.commonRep i).val)
    (hzj : G.Adj z.val (F.commonRep j).val)
    (hwj : G.Adj w.val (F.commonRep j).val)
    (hwk : G.Adj w.val (F.commonRep k).val) (hcolor : c z = c w) : False := by
  let a := (F.center 0).val
  let ri := (F.commonRep i).val
  let rj := (F.commonRep j).val
  let rk := (F.commonRep k).val
  have hri : ri ≠ v := (F.commonRep i).property.ne.symm
  have hrj : rj ≠ v := (F.commonRep j).property.ne.symm
  have hrk : rk ≠ v := (F.commonRep k).property.ne.symm
  have ha : a ≠ v := (F.center 0).property.ne.symm
  have hivj : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  have hivk : i.val ≠ k.val := fun he => hik (Subtype.ext he)
  have hjvk : j.val ≠ k.val := fun he => hjk (Subtype.ext he)
  have hrij : ri ≠ rj := F.leaf_leaf_ne hivj (F.commonRepSide i) (F.commonRepSide j)
  have hrik : ri ≠ rk := F.leaf_leaf_ne hivk (F.commonRepSide i) (F.commonRepSide k)
  have hrjk : rj ≠ rk := F.leaf_leaf_ne hjvk (F.commonRepSide j) (F.commonRepSide k)
  have hari : a ≠ ri := F.center_leaf_ne 0 i.val (F.commonRepSide i)
  have harj : a ≠ rj := F.center_leaf_ne 0 j.val (F.commonRepSide j)
  have hark : a ≠ rk := F.center_leaf_ne 0 k.val (F.commonRepSide k)
  have hza : z.val ≠ a := outside_closed_ne_neighbor z.val hz (F.center 0)
  have hzri : z.val ≠ ri := outside_closed_ne_neighbor z.val hz (F.commonRep i)
  have hzrj : z.val ≠ rj := outside_closed_ne_neighbor z.val hz (F.commonRep j)
  have hzrk : z.val ≠ rk := outside_closed_ne_neighbor z.val hz (F.commonRep k)
  have hwa : w.val ≠ a := outside_closed_ne_neighbor w.val hw (F.center 0)
  have hwri : w.val ≠ ri := outside_closed_ne_neighbor w.val hw (F.commonRep i)
  have hwrj : w.val ≠ rj := outside_closed_ne_neighbor w.val hw (F.commonRep j)
  have hwrk : w.val ≠ rk := outside_closed_ne_neighbor w.val hw (F.commonRep k)
  let f : Fin 7 → V := ![a, v, ri, z.val, rj, w.val, rk]
  have hf : IsHeptagon G f := by
    refine ⟨?_, (F.center 0).property.symm, (F.commonRep i).property,
      hzi.symm, hzj, hwj.symm, hwk, (F.commonRep_adj_zero k).symm⟩
    change Function.Injective ![a, v, ri, z.val, rj, w.val, rk]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show a ≠ v ∧ a ≠ ri ∧ a ≠ z.val ∧ a ≠ rj ∧ a ≠ w.val ∧ a ≠ rk from ⟨ha, hari, Ne.symm hza, harj, Ne.symm hwa, hark⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show v ≠ ri ∧ v ≠ z.val ∧ v ≠ rj ∧ v ≠ w.val ∧ v ≠ rk from ⟨Ne.symm hri, Ne.symm z.property, Ne.symm hrj, Ne.symm w.property, Ne.symm hrk⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show ri ≠ z.val ∧ ri ≠ rj ∧ ri ≠ w.val ∧ ri ≠ rk from ⟨Ne.symm hzri, hrij, Ne.symm hwri, hrik⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z.val ≠ rj ∧ z.val ≠ w.val ∧ z.val ≠ rk from ⟨hzrj, hzw, hzrk⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show rj ≠ w.val ∧ rj ≠ rk from ⟨Ne.symm hwrj, hrjk⟩)
    exact injective_pair_iff_ne.mpr (hwrk)
  exact rainbow_heptagon_same_color_impossible hr v c f hf z.val w.val
    z.property w.property hzw ⟨3, rfl⟩ ⟨5, rfl⟩ hcolor

end TaskH.Seven
#print axioms TaskH.Seven.common_three_rep_crossing_same_color_false
