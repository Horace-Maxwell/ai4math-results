import Research.TaskH.Six.SixStarForcedColor
import Research.TaskH.Six.SixDegreeTenLocalShape
import Research.TaskH.Six.SixDegreeTenCommonOutside

/-! Derive the common color of actual multiple attachments in each split side. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

noncomputable def degreeTenSplitLeaf (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (a : Fin 2) (i : Fin 4) : V :=
  (degreeTenPair F i (ε i + a)).val

theorem degreeTenSplitLeaf_injective (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (a : Fin 2) :
    Function.Injective (degreeTenSplitLeaf F ε a) := by
  intro i j he
  have he' : (degreeTenPair F i (ε i + a)).val =
      (degreeTenPair F j (ε j + a)).val := he
  exact congrArg Prod.fst (degreeTenPair_all_val_injective F
    (a₁ := (i, ε i + a)) (a₂ := (j, ε j + a)) he')

theorem degreeTenFrame_split_color_coverage (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (a : Fin 2) (k : Fin 6) :
    k = neighborColor v c (degreeTenCenter F a) ∨
      k = neighborColor v c (degreeTenCenter F (a + 1)) ∨
        ∃ i : Fin 4, k = neighborColor v c (degreeTenPair F i (ε i + a)) := by
  by_cases hS : k ∈ singletonNeighborColors v c
  · let s : ↥(singletonNeighborColors v c) := ⟨k, hS⟩
    let b : Fin 2 := F.singletonColors s
    have he : k = neighborColor v c (degreeTenCenter F b) := by
      rw [degreeTenCenter_color, F.singletonColors.symm_apply_apply]
    have hb : b = a ∨ b = a + 1 := by
      have htwo : ∀ a b : Fin 2, b = a ∨ b = a + 1 := by decide +kernel
      exact htwo a b
    rcases hb with hb | hb
    · exact Or.inl (by simpa only [hb] using he)
    · exact Or.inr (Or.inl (by simpa only [hb] using he))
  · let s : ↥((singletonNeighborColors v c)ᶜ) := ⟨k, Finset.mem_compl.mpr hS⟩
    refine Or.inr (Or.inr ⟨F.doubleColors s, ?_⟩)
    rw [degreeTenPair_color, F.doubleColors.symm_apply_apply]

theorem degreeTen_split_center_leaf_adj (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (hSplit : ∀ i, DegreeTenSplitAt F i (ε i))
    (a : Fin 2) (i : Fin 4) :
    G.Adj (degreeTenCenter F a).val (degreeTenSplitLeaf F ε a i) := by
  fin_cases a
  · change G.Adj (degreeTenCenter F 0).val (degreeTenPair F i (ε i + 0)).val
    simpa only [add_zero] using (hSplit i).1
  · change G.Adj (degreeTenCenter F 1).val (degreeTenPair F i (ε i + 1)).val
    exact (hSplit i).2.2.1

theorem degreeTen_split_multi_forced_color (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i))
    (a : Fin 2) (z : V) (hz : z ∈ degreeTenOutside G v)
    (hL : 2 ≤ (fourLeafLabels G (degreeTenSplitLeaf F ε a) z).card) :
    c ⟨z, ((mem_degreeTenOutside_iff z).mp hz).1⟩ =
      neighborColor v c (degreeTenCenter F (a + 1)) := by
  have hpv : ∀ i, G.Adj v (degreeTenSplitLeaf F ε a i) :=
    fun i => (degreeTenPair F i (ε i + a)).property
  have hcover : ∀ k : Fin 6,
      k = c ⟨(degreeTenCenter F a).val, (degreeTenCenter F a).property.ne.symm⟩ ∨
      k = c ⟨(degreeTenCenter F (a + 1)).val,
        (degreeTenCenter F (a + 1)).property.ne.symm⟩ ∨
      ∃ i : Fin 4, k = c ⟨degreeTenSplitLeaf F ε a i, (hpv i).ne.symm⟩ := by
    intro k
    exact degreeTenFrame_split_color_coverage F ε a k
  exact four_leaf_multiple_attachment_forced_color hr v
    (degreeTenCenter F a).val (degreeTenCenter F (a + 1)).val c
    (degreeTenSplitLeaf F ε a) (degreeTenSplitLeaf_injective F ε a)
    (degreeTenCenter F a).property (degreeTenCenter F (a + 1)).property hpv
    (degreeTen_split_center_leaf_adj F ε hSplit a) hcover z
    ((mem_degreeTenOutside_iff z).mp hz) hL

theorem degreeTen_split_multi_labels_intersection (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i))
    (a : Fin 2) (x y : V) (hx : x ∈ degreeTenOutside G v)
    (hy : y ∈ degreeTenOutside G v) (hxy : x ≠ y)
    (hLx : 2 ≤ (fourLeafLabels G (degreeTenSplitLeaf F ε a) x).card)
    (hLy : 2 ≤ (fourLeafLabels G (degreeTenSplitLeaf F ε a) y).card) :
    Disjoint (fourLeafLabels G (degreeTenSplitLeaf F ε a) x)
      (fourLeafLabels G (degreeTenSplitLeaf F ε a) y) ∨
      (fourLeafLabels G (degreeTenSplitLeaf F ε a) x =
        fourLeafLabels G (degreeTenSplitLeaf F ε a) y ∧
          (fourLeafLabels G (degreeTenSplitLeaf F ε a) x).card = 2) := by
  have hcolor := (degreeTen_split_multi_forced_color hr F ε hSplit a x hx hLx).trans
    (degreeTen_split_multi_forced_color hr F ε hSplit a y hy hLy).symm
  exact same_color_four_leaf_labels_intersection hr v (degreeTenCenter F a).val c
    (degreeTenSplitLeaf F ε a) (degreeTenSplitLeaf_injective F ε a)
    (degreeTenCenter F a).property (fun i => (degreeTenPair F i (ε i + a)).property)
    (degreeTen_split_center_leaf_adj F ε hSplit a) x y
    ((mem_degreeTenOutside_iff x).mp hx) ((mem_degreeTenOutside_iff y).mp hy)
    hxy hcolor hLx hLy

end TaskH.Six

#print axioms TaskH.Six.degreeTenSplitLeaf
#print axioms TaskH.Six.degreeTenSplitLeaf_injective
#print axioms TaskH.Six.degreeTenFrame_split_color_coverage
#print axioms TaskH.Six.degreeTen_split_center_leaf_adj
#print axioms TaskH.Six.degreeTen_split_multi_forced_color
#print axioms TaskH.Six.degreeTen_split_multi_labels_intersection
