import Research.TaskP.GradedWilf.WilfAtoms
import Research.TaskP.GradedWilf.WilfLow
namespace TaskP.GradedWilf.Proof
open Challenge

theorem Wilf : Challenge.Wilf := by
  intro a b d ha hb hc hd
  dsimp only
  have cset := below_eq_ball ha hb hc hd
  have aset := atoms_eq (d:=d) ha hb hc
  have ds : Disjoint (layer d a) (layer d b) :=
    Finset.disjoint_left.mpr (fun _ hx hy => (Nat.ne_of_lt hb) ((mem_layer.mp hx).symm.trans (mem_layer.mp hy)))
  have ec : (atoms (graded a b d)).ncard = d.multichoose a+d.multichoose b := by
    rw [aset,Set.ncard_coe_finset,Finset.card_union_of_disjoint ds,card_layer,card_layer]
  refine ⟨cset ▸ (ball d (frob a b)).finite_toSet,aset ▸ (layer d a ∪ layer d b).finite_toSet,
    atoms_generate a b d,fun G h => atoms_minimal G h,?_⟩
  rw [ec,good_count ha hb hc hd, cset,Set.ncard_coe_finset,card_ball]
  by_cases h : 3 ≤ d
  · apply (high_wilf ha hb h).trans
    apply Nat.mul_le_mul_left
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact mem_good.mpr ⟨Nat.sub_le ..,penultimate_mem ha hb hc⟩
  · exact low_wilf ha hb hc hd (by omega)

end TaskP.GradedWilf.Proof
