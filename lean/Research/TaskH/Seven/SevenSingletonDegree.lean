import Research.TaskH.Seven.SingletonClique

/-!
Actual singleton neighbors give finite cliques. The generic cardinal argument
below then supplies the degree-ten and degree-eleven steps once the separate
original-graph K6/K5 exclusions have been proved. No clique-freeness conclusion
or original equality theorem is postulated in this module.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem singletonNeighbor_val_injective (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) :
    Function.Injective (fun i : ↥(singletonNeighborColors v c) =>
      (singletonNeighbor v c i).val) := by
  intro i j he
  have hsub : singletonNeighbor v c i = singletonNeighbor v c j := Subtype.ext he
  have hc : i.val = j.val := (singletonNeighbor_color v c i).symm.trans
    ((congrArg (neighborColor v c) hsub).trans (singletonNeighbor_color v c j))
  exact Subtype.ext hc

theorem singleton_colors_card_lt_of_cliqueFree (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (n : ℕ) (hn : 3 ≤ n) (hfree : G.CliqueFree (n + 1))
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) :
    (singletonNeighborColors v c).card < n := by
  classical
  by_contra hlarge
  have hncard : n ≤ (singletonNeighborColors v c).card := by omega
  have hcard : Fintype.card (Fin n) ≤ Fintype.card ↥(singletonNeighborColors v c) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hncard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let g : Fin n → V := fun i => (singletonNeighbor v c (e i)).val
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
        exact singleton_neighbors_adj hcrit hs hr v c (by omega)
          (e i) (e j) (e.injective.ne hij)
  have hvout : v ∉ Finset.univ.image g := by
    intro hmem
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hmem
    exact (singletonNeighbor v c (e i)).property.ne hi.symm
  have hS : S.card = n + 1 := by
    change (insert v (Finset.univ.image g)).card = n + 1
    rw [Finset.card_insert_of_notMem hvout,
      Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  exact hfree S ⟨hclique, hS⟩

theorem singleton_colors_card_lt_five_of_cliqueFree_six (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (hfree : G.CliqueFree 6)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) :
    (singletonNeighborColors v c).card < 5 :=
  singleton_colors_card_lt_of_cliqueFree hcrit hs hr 5 (by decide) hfree v c

theorem singleton_colors_card_lt_four_of_cliqueFree_five (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (hfree : G.CliqueFree 5)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) :
    (singletonNeighborColors v c).card < 4 :=
  singleton_colors_card_lt_of_cliqueFree hcrit hs hr 4 (by decide) hfree v c

theorem critical_degree_ge_ten_of_cliqueFree_six (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (hfree : G.CliqueFree 6)
    (v : V) : 10 ≤ G.degree v := by
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  have hlo := singletonNeighborColors_card_ge hcrit v c
  have hhi := singleton_colors_card_lt_five_of_cliqueFree_six hcrit hs hr hfree v c
  omega

theorem critical_degree_ge_eleven_of_cliqueFree_five (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (hfree : G.CliqueFree 5)
    (v : V) : 11 ≤ G.degree v := by
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  have hlo := singletonNeighborColors_card_ge hcrit v c
  have hhi := singleton_colors_card_lt_four_of_cliqueFree_five hcrit hs hr hfree v c
  omega

end TaskH.Seven

#print axioms TaskH.Seven.singletonNeighbor_val_injective
#print axioms TaskH.Seven.singleton_colors_card_lt_of_cliqueFree
#print axioms TaskH.Seven.singleton_colors_card_lt_five_of_cliqueFree_six
#print axioms TaskH.Seven.singleton_colors_card_lt_four_of_cliqueFree_five
#print axioms TaskH.Seven.critical_degree_ge_ten_of_cliqueFree_six
#print axioms TaskH.Seven.critical_degree_ge_eleven_of_cliqueFree_five
