import Research.TaskH.Six.SixDegreeTenPairDichotomy
import Research.TaskH.Six.SixDegreeTenFrameWords

/-!
Complete actual local neighborhood shapes at degree ten. Alternative A has
only the two four-leaf stars and an optional center edge. Alternative B has
K_(2,4), no center edge, no edges to the other four vertices, and a triangle-free
graph on those four vertices. Every vertex is covered by the actual frame.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

omit [Fintype V] [DecidableRel G.Adj] in
theorem degreeTen_neighbor_triangle_impossible (hfree : G.CliqueFree 4)
    (v a b d : V) (ha : G.Adj v a) (hb : G.Adj v b) (hd : G.Adj v d)
    (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d) : False := by
  classical
  have hN : (G.induce (G.neighborSet v)).CliqueFree 3 := by
    rw [SimpleGraph.cliqueFree_induce_iff]
    have hu : G.CliqueFreeOn Set.univ (3 + 1) := hfree.cliqueFreeOn
    have hn := SimpleGraph.CliqueFreeOn.of_succ G hu (Set.mem_univ v)
    simpa only [Set.univ_inter] using hn
  let A : G.neighborSet v := ⟨a, ha⟩
  let B : G.neighborSet v := ⟨b, hb⟩
  let D : G.neighborSet v := ⟨d, hd⟩
  have hthree : (G.induce (G.neighborSet v)).IsNClique 3 {A, B, D} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, had, hbd⟩
  exact hN _ hthree

theorem degreeTen_split_left_independent (hfree : G.CliqueFree 4)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) (i j : Fin 4) :
    ¬ G.Adj (degreeTenPair F i (ε i)).val (degreeTenPair F j (ε j)).val := by
  intro hadj
  exact degreeTen_neighbor_triangle_impossible hfree v (degreeTenCenter F 0).val
    (degreeTenPair F i (ε i)).val (degreeTenPair F j (ε j)).val
    (degreeTenCenter F 0).property (degreeTenPair F i (ε i)).property
    (degreeTenPair F j (ε j)).property (hSplit i).1 (hSplit j).1 hadj

theorem degreeTen_split_right_independent (hfree : G.CliqueFree 4)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) (i j : Fin 4) :
    ¬ G.Adj (degreeTenPair F i (ε i + 1)).val (degreeTenPair F j (ε j + 1)).val := by
  intro hadj
  exact degreeTen_neighbor_triangle_impossible hfree v (degreeTenCenter F 1).val
    (degreeTenPair F i (ε i + 1)).val (degreeTenPair F j (ε j + 1)).val
    (degreeTenCenter F 1).property (degreeTenPair F i (ε i + 1)).property
    (degreeTenPair F j (ε j + 1)).property (hSplit i).2.2.1 (hSplit j).2.2.1 hadj

theorem degreeTen_split_cross_independent (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) (i j : Fin 4) :
    ¬ G.Adj (degreeTenPair F i (ε i)).val (degreeTenPair F j (ε j + 1)).val := by
  intro hadj
  by_cases hij : i = j
  · subst j
    exact degreeTenPair_same_color_not_adj F i (ε i) (ε i + 1) hadj
  · let w := degreeTenCrossWord i j (ε j) (ε j + 1) (ε i)
    have hother : ε j ≠ ε j + 1 := by
      generalize ε j = t
      fin_cases t <;> decide +kernel
    have hwi : Function.Injective w := degreeTenCrossWord_injective i j _ _ _ hij hother
    have hcolorinj := degreeTen_indexed_path_colors_injective hr F w hwi
      (hSplit j).1.symm (hSplit i).1 hadj (hSplit j).2.2.1.symm
    have hcolor : neighborColor v c (degreeTenIndexedNeighbor F (w 0)) =
        neighborColor v c (degreeTenIndexedNeighbor F (w 3)) :=
      (degreeTenPair_color F j (ε j)).trans (degreeTenPair_color F j (ε j + 1)).symm
    exact (by decide : (0 : Fin 5) ≠ 3) (hcolorinj hcolor)

theorem degreeTen_common_centers_not_adj (hfree : G.CliqueFree 4)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) :
    ¬ G.Adj (degreeTenCenter F 0).val (degreeTenCenter F 1).val := by
  intro hadj
  exact degreeTen_neighbor_triangle_impossible hfree v (degreeTenCenter F 0).val
    (degreeTenCenter F 1).val (degreeTenPair F 0 (r 0)).val
    (degreeTenCenter F 0).property (degreeTenCenter F 1).property
    (degreeTenPair F 0 (r 0)).property hadj (hCommon 0).1 (hCommon 0).2.1

theorem degreeTen_common_left_independent (hfree : G.CliqueFree 4)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) (i j : Fin 4) :
    ¬ G.Adj (degreeTenPair F i (r i)).val (degreeTenPair F j (r j)).val := by
  intro hadj
  exact degreeTen_neighbor_triangle_impossible hfree v (degreeTenCenter F 0).val
    (degreeTenPair F i (r i)).val (degreeTenPair F j (r j)).val
    (degreeTenCenter F 0).property (degreeTenPair F i (r i)).property
    (degreeTenPair F j (r j)).property (hCommon i).1 (hCommon j).1 hadj

theorem degreeTen_common_cross_independent (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) (i j : Fin 4) :
    ¬ G.Adj (degreeTenPair F i (r i)).val (degreeTenPair F j (r j + 1)).val := by
  intro hadj
  by_cases hij : i = j
  · subst j
    exact degreeTenPair_same_color_not_adj F i (r i) (r i + 1) hadj
  · let w := degreeTenCommonCrossWord i j (r j + 1) (r j) (r i)
    have hother : r j + 1 ≠ r j := by
      generalize r j = t
      fin_cases t <;> decide +kernel
    have hwi : Function.Injective w := degreeTenCommonCrossWord_injective i j _ _ _ hij hother
    have hcolorinj := degreeTen_indexed_path_colors_injective hr F w hwi
      hadj.symm (hCommon i).1.symm (hCommon j).1 (hCommon j).2.1.symm
    have hcolor : neighborColor v c (degreeTenIndexedNeighbor F (w 0)) =
        neighborColor v c (degreeTenIndexedNeighbor F (w 3)) :=
      (degreeTenPair_color F j (r j + 1)).trans (degreeTenPair_color F j (r j)).symm
    exact (by decide : (0 : Fin 5) ≠ 3) (hcolorinj hcolor)

theorem degreeTen_common_other_triangle_free (hfree : G.CliqueFree 4)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) (i j k : Fin 4) :
    ¬ (G.Adj (degreeTenPair F i (r i + 1)).val (degreeTenPair F j (r j + 1)).val ∧
      G.Adj (degreeTenPair F i (r i + 1)).val (degreeTenPair F k (r k + 1)).val ∧
      G.Adj (degreeTenPair F j (r j + 1)).val (degreeTenPair F k (r k + 1)).val) := by
  rintro ⟨hij, hik, hjk⟩
  exact degreeTen_neighbor_triangle_impossible hfree v
    (degreeTenPair F i (r i + 1)).val (degreeTenPair F j (r j + 1)).val
    (degreeTenPair F k (r k + 1)).val (degreeTenPair F i (r i + 1)).property
    (degreeTenPair F j (r j + 1)).property (degreeTenPair F k (r k + 1)).property hij hik hjk

def DegreeTenLocalShapeA (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2) : Prop :=
  (∀ i, DegreeTenSplitAt F i (ε i)) ∧
    (∀ i j, ¬ G.Adj (degreeTenPair F i (ε i)).val (degreeTenPair F j (ε j)).val) ∧
    (∀ i j, ¬ G.Adj (degreeTenPair F i (ε i + 1)).val (degreeTenPair F j (ε j + 1)).val) ∧
    ∀ i j, ¬ G.Adj (degreeTenPair F i (ε i)).val (degreeTenPair F j (ε j + 1)).val

def DegreeTenLocalShapeB (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) : Prop :=
  (∀ i, DegreeTenCommonAt F i (r i)) ∧
    ¬ G.Adj (degreeTenCenter F 0).val (degreeTenCenter F 1).val ∧
    (∀ i j, ¬ G.Adj (degreeTenPair F i (r i)).val (degreeTenPair F j (r j)).val) ∧
    (∀ i j, ¬ G.Adj (degreeTenPair F i (r i)).val (degreeTenPair F j (r j + 1)).val) ∧
    ∀ i j k, ¬ (G.Adj (degreeTenPair F i (r i + 1)).val (degreeTenPair F j (r j + 1)).val ∧
      G.Adj (degreeTenPair F i (r i + 1)).val (degreeTenPair F k (r k + 1)).val ∧
      G.Adj (degreeTenPair F j (r j + 1)).val (degreeTenPair F k (r k + 1)).val)

theorem degreeTen_frame_local_shape_dichotomy
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hfree : G.CliqueFree 4) (F : DegreeTenColorFrame v c) :
    (∃ ε : Fin 4 → Fin 2, DegreeTenLocalShapeA F ε) ∨
      ∃ r : Fin 4 → Fin 2, DegreeTenLocalShapeB F r := by
  obtain ⟨ε, hε⟩ | ⟨r, hr'⟩ := degreeTen_pair_dichotomy hcrit hs hr F
  · exact Or.inl ⟨ε, hε, degreeTen_split_left_independent hfree F ε hε,
      degreeTen_split_right_independent hfree F ε hε,
      degreeTen_split_cross_independent hr F ε hε⟩
  · exact Or.inr ⟨r, hr', degreeTen_common_centers_not_adj hfree F r hr',
      degreeTen_common_left_independent hfree F r hr',
      degreeTen_common_cross_independent hr F r hr', degreeTen_common_other_triangle_free hfree F r⟩

theorem degreeTen_actual_neighbor_dichotomy
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hfree : G.CliqueFree 4) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 10) :
    ∃ F : DegreeTenColorFrame v c,
      (∃ ε : Fin 4 → Fin 2, DegreeTenLocalShapeA F ε) ∨
        ∃ r : Fin 4 → Fin 2, DegreeTenLocalShapeB F r := by
  let F := degreeTenColorFrame hcrit hs hr hfree v c hv
  exact ⟨F, degreeTen_frame_local_shape_dichotomy hcrit hs hr hfree F⟩

end TaskH.Six

#print axioms TaskH.Six.degreeTen_neighbor_triangle_impossible
#print axioms TaskH.Six.degreeTen_split_left_independent
#print axioms TaskH.Six.degreeTen_split_right_independent
#print axioms TaskH.Six.degreeTen_split_cross_independent
#print axioms TaskH.Six.degreeTen_common_centers_not_adj
#print axioms TaskH.Six.degreeTen_common_left_independent
#print axioms TaskH.Six.degreeTen_common_cross_independent
#print axioms TaskH.Six.degreeTen_common_other_triangle_free
#print axioms TaskH.Six.DegreeTenLocalShapeA
#print axioms TaskH.Six.DegreeTenLocalShapeB
#print axioms TaskH.Six.degreeTen_frame_local_shape_dichotomy
#print axioms TaskH.Six.degreeTen_actual_neighbor_dichotomy
