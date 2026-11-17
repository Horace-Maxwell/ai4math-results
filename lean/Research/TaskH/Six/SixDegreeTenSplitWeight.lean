import Research.TaskH.Six.SixDegreeTenSplitColors
import Research.TaskH.Six.SixSplitClonePacking
import Research.TaskH.Six.SixFourLabelBudget

/-! The actual outside pool of either split star satisfies its label excess budget. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

noncomputable def degreeTenSplitPool (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (a : Fin 2) : Finset V :=
  (degreeTenOutside G v).filter
    (fun z => (fourLeafLabels G (degreeTenSplitLeaf F ε a) z).Nonempty)

theorem degreeTen_split_clone_fiber_card_le_three (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) (a : Fin 2)
    (hmin : ∀ x : V, 10 ≤ G.degree x) (hn : Fintype.card V ≤ 36)
    (S : Finset (Fin 4)) (hS : S.card = 2) :
    ((degreeTenSplitPool F ε a).filter
      (fun z => fourLeafLabels G (degreeTenSplitLeaf F ε a) z = S)).card ≤ 3 := by
  classical
  let L := fourLeafLabels G (degreeTenSplitLeaf F ε a)
  let Z := (degreeTenSplitPool F ε a).filter (fun z => L z = S)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hout : ∀ z ∈ Z, z ≠ v ∧ ¬ G.Adj v z := by
    intro z hz
    exact (mem_degreeTenOutside_iff z).mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hL : ∀ z ∈ Z, L z = S := fun z hz => (Finset.mem_filter.mp hz).2
  have hleaves : ∀ z ∈ Z,
      G.Adj z (degreeTenSplitLeaf F ε a i) ∧
        G.Adj z (degreeTenSplitLeaf F ε a j) := by
    intro z hz
    have hzi : i ∈ L z := (hL z hz).symm ▸ hi
    have hzj : j ∈ L z := (hL z hz).symm ▸ hj
    exact ⟨(mem_fourLeafLabels_iff _ z i).mp hzi,
      (mem_fourLeafLabels_iff _ z j).mp hzj⟩
  have hcolor : ∀ z (hz : z ∈ Z), ∀ z' (hz' : z' ∈ Z),
      c ⟨z, (hout z hz).1⟩ = c ⟨z', (hout z' hz').1⟩ := by
    intro z hz z' hz'
    have hzO := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    have hz'O := (Finset.mem_filter.mp (Finset.mem_filter.mp hz').1).1
    have hsz : 2 ≤ (L z).card := by rw [hL z hz, hS]
    have hsz' : 2 ≤ (L z').card := by rw [hL z' hz', hS]
    exact (degreeTen_split_multi_forced_color hr F ε hSplit a z hzO hsz).trans
      (degreeTen_split_multi_forced_color hr F ε hSplit a z' hz'O hsz').symm
  exact same_color_two_leaf_clone_card_le_three hr v (degreeTenCenter F a).val
    (degreeTenSplitLeaf F ε a i) (degreeTenSplitLeaf F ε a j) c
    (degreeTenCenter F a).property (degreeTenPair F i (ε i + a)).property
    (degreeTenPair F j (ε j + a)).property
    (degreeTen_split_center_leaf_adj F ε hSplit a i)
    (degreeTen_split_center_leaf_adj F ε hSplit a j)
    ((degreeTenSplitLeaf_injective F ε a).ne hij) Z hout hleaves hcolor
    (fun z _ => hmin z) hn

theorem degreeTen_split_pool_weight_le_card_add_six (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) (a : Fin 2)
    (hmin : ∀ x : V, 10 ≤ G.degree x) (hn : Fintype.card V ≤ 36) :
    (∑ z ∈ degreeTenSplitPool F ε a,
      (fourLeafLabels G (degreeTenSplitLeaf F ε a) z).card) ≤
        (degreeTenSplitPool F ε a).card + 6 := by
  apply four_label_total_weight_le_card_add_six
  · intro x hx y hy hxy hLx hLy
    exact degreeTen_split_multi_labels_intersection hr F ε hSplit a x y
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy hLx hLy
  · exact degreeTen_split_clone_fiber_card_le_three hr F ε hSplit a hmin hn

end TaskH.Six

#print axioms TaskH.Six.degreeTenSplitPool
#print axioms TaskH.Six.degreeTen_split_clone_fiber_card_le_three
#print axioms TaskH.Six.degreeTen_split_pool_weight_le_card_add_six
