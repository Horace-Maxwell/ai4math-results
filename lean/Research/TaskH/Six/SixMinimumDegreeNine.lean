import Research.TaskH.Six.SixFiveCliqueClosedPacking

/-!
Four singleton neighbor colors would supply, together with their deleted
vertex, a genuine five-clique. The proved K5-free conclusion therefore
limits singleton colors to three and forces every degree to be at least 9.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem singletonNeighbor_val_injective (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) :
    Function.Injective (fun i : ↥(singletonNeighborColors v c) => (singletonNeighbor v c i).val) := by
  intro i j he
  have hsub : singletonNeighbor v c i = singletonNeighbor v c j := Subtype.ext he
  have hc : i.val = j.val := (singletonNeighbor_color v c i).symm.trans
    ((congrArg (neighborColor v c) hsub).trans (singletonNeighbor_color v c j))
  exact Subtype.ext hc

theorem singleton_colors_card_lt_four_of_cliqueFree_five (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G) (hfree : G.CliqueFree 5)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) :
    (singletonNeighborColors v c).card < 4 := by
  classical
  by_contra hlarge
  have hfour : 4 ≤ (singletonNeighborColors v c).card := by omega
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card ↥(singletonNeighborColors v c) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hfour
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let g : Fin 4 → V := fun i => (singletonNeighbor v c (e i)).val
  have hg : Function.Injective g := (singletonNeighbor_val_injective v c).comp e.injective
  let S : Finset V := insert v (Finset.univ.image g)
  have hclique : G.IsClique S := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, S, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and] at ha hb
    rcases ha with hav | ⟨i, hi⟩
    · rcases hb with hbv | ⟨j, hj⟩
      · exact (hab (hav.trans hbv.symm)).elim
      · rw [hav, ← hj]
        exact (singletonNeighbor v c (e j)).property
    · rcases hb with hbv | ⟨j, hj⟩
      · rw [hbv, ← hi]
        exact (singletonNeighbor v c (e i)).property.symm
      · have hij : i ≠ j := by
          intro he
          exact hab (hi.symm.trans ((congrArg g he).trans hj))
        rw [← hi, ← hj]
        exact singleton_neighbors_adj hcrit hs hr v c (by omega) (e i) (e j) (e.injective.ne hij)
  have hvout : v ∉ Finset.univ.image g := by
    intro hmem
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hmem
    exact (singletonNeighbor v c (e i)).property.ne hi.symm
  have hS : S.card = 5 := by
    change (insert v (Finset.univ.image g)).card = 5
    rw [Finset.card_insert_of_notMem hvout,
      Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  exact hfree S ⟨hclique, hS⟩

theorem critical_degree_ge_nine_of_cliqueFree_five (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G) (hfree : G.CliqueFree 5)
    (v : V) : 9 ≤ G.degree v := by
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit v
  have hlo := singletonNeighborColors_card_ge hcrit v c
  have hhi := singleton_colors_card_lt_four_of_cliqueFree_five hcrit hs hr hfree v c
  omega

theorem equality_degree_ge_nine (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    ∀ v : V, 9 ≤ G.degree v :=
  critical_degree_ge_nine_of_cliqueFree_five hcrit (equality_shortSixCycles hcrit hc)
    (equality_rainbowSixCycles hcrit hc) (equality_cliqueFree_five hcrit hc hnot)

theorem equality_minDegree_ge_nine (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) : 9 ≤ G.minDegree := by
  classical
  have hn := critical_six_card_ge_seven hcrit
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact G.le_minDegree_of_forall_le_degree 9 (equality_degree_ge_nine hcrit hc hnot)

end TaskH.Six

#print axioms TaskH.Six.singletonNeighbor_val_injective
#print axioms TaskH.Six.singleton_colors_card_lt_four_of_cliqueFree_five
#print axioms TaskH.Six.critical_degree_ge_nine_of_cliqueFree_five
#print axioms TaskH.Six.equality_degree_ge_nine
#print axioms TaskH.Six.equality_minDegree_ge_nine
