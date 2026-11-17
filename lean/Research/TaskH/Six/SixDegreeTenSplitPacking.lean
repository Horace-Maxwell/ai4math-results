import Research.TaskH.Six.SixDegreeTenSplitSeparation
import Research.TaskH.Six.SixOpenNeighborhoodPacking

/-!
The actual split alternative has at least 32 outside incidences on each side.
Its proved label excess bound gives total64 <= outside-card+12 = n+1,
contradicting n<=36. No pool size or adjacency premise is assumed.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

theorem degreeTen_split_center_leaf_adj_iff (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (hSplit : ∀ i, DegreeTenSplitAt F i (ε i))
    (a b : Fin 2) (i : Fin 4) :
    G.Adj (degreeTenCenter F b).val (degreeTenSplitLeaf F ε a i) ↔ b = a := by
  fin_cases a <;> fin_cases b
  · change G.Adj (degreeTenCenter F 0).val (degreeTenPair F i (ε i + 0)).val ↔ (0 : Fin 2) = 0
    simpa only [add_zero] using (iff_of_true (hSplit i).1 (rfl : (0 : Fin 2) = 0))
  · change G.Adj (degreeTenCenter F 1).val (degreeTenPair F i (ε i + 0)).val ↔ (1 : Fin 2) = 0
    simpa only [add_zero] using (iff_of_false (hSplit i).2.1 (by decide : ¬ (1 : Fin 2) = 0))
  · exact iff_of_false (hSplit i).2.2.2 (by decide : ¬ (0 : Fin 2) = 1)
  · exact iff_of_true (hSplit i).2.2.1 (rfl : (1 : Fin 2) = 1)

theorem degreeTen_split_leaves_not_adj (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (hA : DegreeTenLocalShapeA F ε)
    (a b : Fin 2) (i j : Fin 4) :
    ¬ G.Adj (degreeTenSplitLeaf F ε a i) (degreeTenSplitLeaf F ε b j) := by
  fin_cases a <;> fin_cases b
  · change ¬ G.Adj (degreeTenPair F i (ε i + 0)).val (degreeTenPair F j (ε j + 0)).val
    simpa only [add_zero] using hA.2.1 i j
  · change ¬ G.Adj (degreeTenPair F i (ε i + 0)).val (degreeTenPair F j (ε j + 1)).val
    simpa only [add_zero] using hA.2.2.2 i j
  · intro hadj
    change G.Adj (degreeTenPair F i (ε i + 1)).val (degreeTenPair F j (ε j + 0)).val at hadj
    apply hA.2.2.2 j i
    simpa only [add_zero] using hadj.symm
  · exact hA.2.2.1 i j

theorem degreeTen_split_inside_neighbors_le_two (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (hA : DegreeTenLocalShapeA F ε) (a : Fin 2) (i : Fin 4) :
    (packingNeighborsIn G (degreeTenClosedSet G v) (degreeTenSplitLeaf F ε a i)).card ≤ 2 := by
  have hsub : packingNeighborsIn G (degreeTenClosedSet G v) (degreeTenSplitLeaf F ε a i) ⊆
      {v, (degreeTenCenter F a).val} := by
    intro y hy
    obtain ⟨hyW, hiy⟩ := Finset.mem_filter.mp hy
    obtain hyv | hyN := Finset.mem_insert.mp hyW
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · let ny : G.neighborSet v := ⟨y, (G.mem_neighborFinset v y).mp hyN⟩
      obtain ⟨b, hb⟩ | ⟨j, d, hjd⟩ := degreeTenFrame_neighbor_exhaustion F ny
      · have he : y = (degreeTenCenter F b).val := (congrArg Subtype.val hb).symm
        have hadj : G.Adj (degreeTenCenter F b).val (degreeTenSplitLeaf F ε a i) := by
          simpa only [he] using hiy.symm
        have hba := (degreeTen_split_center_leaf_adj_iff F ε hA.1 a b i).mp hadj
        rw [he, hba]
        simp
      · have he : y = (degreeTenPair F j d).val := (congrArg Subtype.val hjd).symm
        have hd : d = ε j ∨ d = ε j + 1 := by
          have htwo : ∀ d t : Fin 2, d = t ∨ d = t + 1 := by decide +kernel
          exact htwo d (ε j)
        rcases hd with hd | hd
        · apply False.elim
          apply degreeTen_split_leaves_not_adj F ε hA a 0 i j
          simpa only [degreeTenSplitLeaf, add_zero, he, hd] using hiy
        · apply False.elim
          apply degreeTen_split_leaves_not_adj F ε hA a 1 i j
          simpa only [degreeTenSplitLeaf, he, hd] using hiy
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem degreeTen_split_outside_leaf_row_ge_eight (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (hA : DegreeTenLocalShapeA F ε)
    (hmin : ∀ x : V, 10 ≤ G.degree x) (a : Fin 2) (i : Fin 4) :
    8 ≤ (packingNeighborsIn G (degreeTenOutside G v) (degreeTenSplitLeaf F ε a i)).card :=
  packingNeighborsIn_compl_lower (degreeTenClosedSet G v) (degreeTenSplitLeaf F ε a i)
    10 2 (hmin _) (degreeTen_split_inside_neighbors_le_two F ε hA a i)

theorem degreeTen_split_outside_incidence_eq_pool_weight (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (a : Fin 2) :
    (∑ i : Fin 4,
      (packingNeighborsIn G (degreeTenOutside G v) (degreeTenSplitLeaf F ε a i)).card) =
        ∑ z ∈ degreeTenSplitPool F ε a,
          (fourLeafLabels G (degreeTenSplitLeaf F ε a) z).card := by
  let L := fourLeafLabels G (degreeTenSplitLeaf F ε a)
  have hpool : (∑ z ∈ degreeTenSplitPool F ε a, (L z).card) =
      ∑ z ∈ degreeTenOutside G v, (L z).card := by
    rw [degreeTenSplitPool, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hL : (L z).Nonempty
    · rw [ite_eq_left hL]
    · have hzero : (L z).card = 0 := by
        by_contra hne
        exact hL (Finset.card_pos.mp (Nat.pos_of_ne_zero hne))
      rw [ite_eq_right hL, hzero]
  rw [hpool]
  calc
    _ = ∑ z ∈ degreeTenOutside G v,
        ((Finset.univ : Finset (Fin 4)).filter
          (fun i => G.Adj (degreeTenSplitLeaf F ε a i) z)).card := by
      convert FiniteBudget.relation_double_count (Finset.univ : Finset (Fin 4))
        (degreeTenOutside G v) (fun i z => G.Adj (degreeTenSplitLeaf F ε a i) z) using 1 <;>
        apply Finset.sum_congr rfl
      all_goals
        intro x _
        congr 1
        ext z
        simp only [packingNeighborsIn, Finset.mem_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _hz
      congr 1
      ext i
      simp only [L, fourLeafLabels, Finset.mem_filter, G.adj_comm]

theorem degreeTen_split_pool_weight_ge_thirty_two (F : DegreeTenColorFrame v c)
    (ε : Fin 4 → Fin 2) (hA : DegreeTenLocalShapeA F ε)
    (hmin : ∀ x : V, 10 ≤ G.degree x) (a : Fin 2) :
    32 ≤ ∑ z ∈ degreeTenSplitPool F ε a,
      (fourLeafLabels G (degreeTenSplitLeaf F ε a) z).card := by
  rw [← degreeTen_split_outside_incidence_eq_pool_weight]
  calc
    32 = ∑ _i : Fin 4, 8 := by norm_num
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      degreeTen_split_outside_leaf_row_ge_eight F ε hA hmin a i)

theorem degreeTen_split_packing_budget (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2) (hA : DegreeTenLocalShapeA F ε)
    (hv : G.degree v = 10) (hmin : ∀ x : V, 10 ≤ G.degree x)
    (hn36 : Fintype.card V ≤ 36) : 64 ≤ Fintype.card V + 1 := by
  have hP := degreeTen_split_pool_weight_ge_thirty_two F ε hA hmin 0
  have hQ := degreeTen_split_pool_weight_ge_thirty_two F ε hA hmin 1
  have hPw := degreeTen_split_pool_weight_le_card_add_six hr F ε hA.1 0 hmin hn36
  have hQw := degreeTen_split_pool_weight_le_card_add_six hr F ε hA.1 1 hmin hn36
  have hd := degreeTen_split_pools_disjoint hr F ε hA.1
  have hsub : degreeTenSplitPool F ε 0 ∪ degreeTenSplitPool F ε 1 ⊆ degreeTenOutside G v :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum : (degreeTenSplitPool F ε 0).card + (degreeTenSplitPool F ε 1).card ≤
      (degreeTenOutside G v).card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card hsub
  have hvnot : v ∉ G.neighborFinset v := by simp
  have hclosed : (degreeTenClosedSet G v).card = 11 := by
    rw [degreeTenClosedSet, Finset.card_insert_of_notMem hvnot,
      G.card_neighborFinset_eq_degree, hv]
  have hcomp := Finset.card_add_card_compl (degreeTenClosedSet G v)
  change (degreeTenClosedSet G v).card + (degreeTenOutside G v).card = Fintype.card V at hcomp
  rw [hclosed] at hcomp
  omega

theorem degreeTen_split_packing_impossible (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2) (hA : DegreeTenLocalShapeA F ε)
    (hv : G.degree v = 10) (hmin : ∀ x : V, 10 ≤ G.degree x)
    (hn36 : Fintype.card V ≤ 36) : False := by
  have hh := degreeTen_split_packing_budget hr F ε hA hv hmin hn36
  omega

end TaskH.Six

#print axioms TaskH.Six.degreeTen_split_center_leaf_adj_iff
#print axioms TaskH.Six.degreeTen_split_leaves_not_adj
#print axioms TaskH.Six.degreeTen_split_inside_neighbors_le_two
#print axioms TaskH.Six.degreeTen_split_outside_leaf_row_ge_eight
#print axioms TaskH.Six.degreeTen_split_outside_incidence_eq_pool_weight
#print axioms TaskH.Six.degreeTen_split_pool_weight_ge_thirty_two
#print axioms TaskH.Six.degreeTen_split_packing_budget
#print axioms TaskH.Six.degreeTen_split_packing_impossible
