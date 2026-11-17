import Research.TaskH.Six.SixFourCliqueRepresentatives
import Research.TaskH.Six.SixFiniteBudget

/-! Consequences of the actual four-clique packing for the degree branches. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem fourClique_packing_labels_alternative (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x) :
    (fourCliqueActiveLabels G q).card = 4 ∨ δ - 3 ≤ (fourCliqueMulti G q).card := by
  have hp := fourCliqueActiveLabels_card_le_four (G := G) q
  by_cases he : (fourCliqueActiveLabels G q).card = 4
  · exact Or.inl he
  · exact Or.inr (fourClique_missing_singleton_many_multi q hq hclique δ hdegree (by omega))

theorem degree_eleven_no_four_clique_embedding
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn37 : Fintype.card V ≤ 37)
    (hdegree : ∀ x : V, 11 ≤ G.degree x)
    (q : Fin 4 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) : False := by
  have hp := fourClique_full_open_packing hcrit hr hn8 q hq hclique 11 hdegree
  have hlabels := fourClique_packing_labels_alternative q hq hclique 11 hdegree
  exact high_degree_four_clique_packing_incompatible
    (fourCliqueMulti G q).card (fourCliqueActiveLabels G q).card (by omega) hlabels

theorem degree_eleven_cliqueFree_four
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn37 : Fintype.card V ≤ 37)
    (hdegree : ∀ x : V, 11 ≤ G.degree x) : G.CliqueFree 4 := by
  classical
  by_contra hnot
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hnot
  apply degree_eleven_no_four_clique_embedding hcrit hr hn8 hn37 hdegree e e.injective
  intro i j hij
  exact e.map_rel_iff.mpr (by simpa using hij)

theorem degree_nine_four_clique_actual_rigid
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn35 : Fintype.card V ≤ 35)
    (hdegree : ∀ x : V, 9 ≤ G.degree x)
    (q : Fin 4 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    (fourCliqueMulti G q).card = 6 ∧ (fourCliqueActiveLabels G q).card = 0 := by
  have hp := fourClique_full_open_packing hcrit hr hn8 q hq hclique 9 hdegree
  have hlabels := fourClique_packing_labels_alternative q hq hclique 9 hdegree
  exact degree_nine_four_clique_packing_rigid
    (fourCliqueMulti G q).card (fourCliqueActiveLabels G q).card (by omega) hlabels

theorem degree_ten_no_four_clique_embedding
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn36 : Fintype.card V ≤ 36)
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (q : Fin 4 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) : False := by
  have hp := fourClique_full_open_packing hcrit hr hn8 q hq hclique 10 hdegree
  have hlabels := fourClique_packing_labels_alternative q hq hclique 10 hdegree
  exact degree_ten_four_clique_packing_incompatible
    (fourCliqueMulti G q).card (fourCliqueActiveLabels G q).card (by omega) hlabels

theorem degree_ten_cliqueFree_four
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hn36 : Fintype.card V ≤ 36)
    (hdegree : ∀ x : V, 10 ≤ G.degree x) : G.CliqueFree 4 := by
  classical
  by_contra hnot
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hnot
  apply degree_ten_no_four_clique_embedding hcrit hr hn8 hn36 hdegree e e.injective
  intro i j hij
  exact e.map_rel_iff.mpr (by simpa using hij)

end TaskH.Six

#print axioms TaskH.Six.fourClique_packing_labels_alternative
#print axioms TaskH.Six.degree_eleven_no_four_clique_embedding
#print axioms TaskH.Six.degree_eleven_cliqueFree_four
#print axioms TaskH.Six.degree_nine_four_clique_actual_rigid
#print axioms TaskH.Six.degree_ten_no_four_clique_embedding
#print axioms TaskH.Six.degree_ten_cliqueFree_four
