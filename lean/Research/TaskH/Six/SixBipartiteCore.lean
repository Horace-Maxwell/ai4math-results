import Research.TaskH.Six.SixFourCliqueConsequences

/-! Degree-nine rigidity supplies an actual K_(4,6), with ten distinct vertices. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem fourClique_outside_root_subset_multi (q : Fin 4 → V) (i : Fin 4)
    (hi : i ∉ fourCliqueActiveLabels G q) :
    packingNeighborsIn G (fourCliqueSet q)ᶜ (q i) ⊆ fourCliqueMulti G q := by
  classical
  intro x hx
  have hh := Finset.mem_filter.mp hx
  have hiL : i ∈ fourCliqueLabels G q x := by
    simpa only [fourCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and]
      using hh.2.symm
  have hl : 2 ≤ (fourCliqueLabels G q x).card := by
    by_contra hsmall
    have hle : (fourCliqueLabels G q x).card ≤ 1 := by omega
    have he : fourCliqueLabels G q x = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hiL, fun j hj => Finset.card_le_one.mp hle j hj i hiL⟩
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨x, Finset.mem_filter.mpr ⟨hh.1, he⟩⟩⟩
  exact Finset.mem_filter.mpr ⟨hh.1, hl⟩

theorem degree_nine_four_clique_multi_all_adjacent
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn35 : Fintype.card V ≤ 35)
    (hdegree : ∀ x : V, 9 ≤ G.degree x)
    (q : Fin 4 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    ∀ i : Fin 4, ∀ x ∈ fourCliqueMulti G q, G.Adj (q i) x := by
  obtain ⟨hM, hp⟩ := degree_nine_four_clique_actual_rigid hcrit hr hn8 hn35
    hdegree q hq hclique
  intro i x hx
  have hi : i ∉ fourCliqueActiveLabels G q := by
    rw [Finset.card_eq_zero.mp hp]
    exact Finset.notMem_empty _
  have hsub := fourClique_outside_root_subset_multi (G := G) q i hi
  have hlo : 6 ≤ (packingNeighborsIn G (fourCliqueSet q)ᶜ (q i)).card := by
    have hh := packingNeighborsIn_compl_lower (fourCliqueSet q) (q i) 9 3
      (hdegree _) (fourClique_root_internal_neighbors_card q hq hclique i).le
    simpa using hh
  have he : packingNeighborsIn G (fourCliqueSet q)ᶜ (q i) = fourCliqueMulti G q :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hM]; exact hlo)
  have hm : x ∈ packingNeighborsIn G (fourCliqueSet q)ᶜ (q i) := by rwa [he]
  exact (Finset.mem_filter.mp hm).2

theorem degree_nine_four_clique_has_actual_bipartite_core
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn35 : Fintype.card V ≤ 35)
    (hdegree : ∀ x : V, 9 ≤ G.degree x)
    (q : Fin 4 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    ∃ t : Fin 6 → V, Function.Injective t ∧
      (∀ i j, q i ≠ t j) ∧ ∀ i j, G.Adj (q i) (t j) := by
  classical
  have hM := (degree_nine_four_clique_actual_rigid hcrit hr hn8 hn35
    hdegree q hq hclique).1
  let e : (fourCliqueMulti G q) ≃ Fin 6 := Finset.equivFinOfCardEq hM
  let t : Fin 6 → V := fun j => (e.symm j).val
  have hti : Function.Injective t := Subtype.val_injective.comp e.symm.injective
  have htM : ∀ j, t j ∈ fourCliqueMulti G q := fun j => (e.symm j).property
  refine ⟨t, hti, ?_, ?_⟩
  · intro i j he
    have hnot : t j ∉ fourCliqueSet q :=
      Finset.mem_compl.mp (Finset.mem_filter.mp (htM j)).1
    apply hnot
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro i j
    exact degree_nine_four_clique_multi_all_adjacent hcrit hr hn8 hn35 hdegree
      q hq hclique i (t j) (htM j)

end TaskH.Six

#print axioms TaskH.Six.fourClique_outside_root_subset_multi
#print axioms TaskH.Six.degree_nine_four_clique_multi_all_adjacent
#print axioms TaskH.Six.degree_nine_four_clique_has_actual_bipartite_core
