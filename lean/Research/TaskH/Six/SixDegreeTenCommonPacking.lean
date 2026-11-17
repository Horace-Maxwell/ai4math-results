import Research.TaskH.Six.SixDegreeTenCommonOutside
import Research.TaskH.Six.SixOpenNeighborhoodPacking

/-!
The actual common-fiber alternative requires at least 45 vertices. Its four
common vertices each have seven outside neighbors, whose pools are disjoint;
one of the other four vertices has six outside neighbors in the other pool.
The root's closed neighborhood has exactly eleven vertices.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

noncomputable def degreeTenCommonSet (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) : Finset V :=
  Finset.univ.image (fun i => (degreeTenPair F i (r i)).val)

noncomputable def degreeTenOtherSet (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) : Finset V :=
  Finset.univ.image (fun i => (degreeTenPair F i (r i + 1)).val)

theorem degreeTenCommonVertex_injective (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) :
    Function.Injective (fun i => (degreeTenPair F i (r i)).val) := by
  intro i j he
  exact congrArg Prod.fst (degreeTenPair_all_val_injective F
    (a₁ := (i, r i)) (a₂ := (j, r j)) he)

theorem degreeTenOtherVertex_injective (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) :
    Function.Injective (fun i => (degreeTenPair F i (r i + 1)).val) := by
  intro i j he
  exact congrArg Prod.fst (degreeTenPair_all_val_injective F
    (a₁ := (i, r i + 1)) (a₂ := (j, r j + 1)) he)

theorem degreeTenCommonSet_card (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) :
    (degreeTenCommonSet F r).card = 4 := by
  rw [degreeTenCommonSet, Finset.card_image_of_injective _
    (degreeTenCommonVertex_injective F r), Finset.card_univ, Fintype.card_fin]

theorem degreeTenOtherSet_card (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) :
    (degreeTenOtherSet F r).card = 4 := by
  rw [degreeTenOtherSet, Finset.card_image_of_injective _
    (degreeTenOtherVertex_injective F r), Finset.card_univ, Fintype.card_fin]

theorem degreeTenClosedSet_card (hv : G.degree v = 10) :
    (degreeTenClosedSet G v).card = 11 := by
  have hvnot : v ∉ G.neighborFinset v := by simp
  rw [degreeTenClosedSet, Finset.card_insert_of_notMem hvnot,
    G.card_neighborFinset_eq_degree, hv]

theorem degreeTen_common_inside_neighbors_le_three (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r) (i : Fin 4) :
    (packingNeighborsIn G (degreeTenClosedSet G v)
      (degreeTenPair F i (r i)).val).card ≤ 3 := by
  have hsub : packingNeighborsIn G (degreeTenClosedSet G v)
      (degreeTenPair F i (r i)).val ⊆
        {v, (degreeTenCenter F 0).val, (degreeTenCenter F 1).val} := by
    intro y hy
    obtain ⟨hyW, hiy⟩ := Finset.mem_filter.mp hy
    obtain hyv | hyN := Finset.mem_insert.mp hyW
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · let ny : G.neighborSet v := ⟨y, (G.mem_neighborFinset v y).mp hyN⟩
      obtain ⟨a, ha⟩ | ⟨j, b, hjb⟩ := degreeTenFrame_neighbor_exhaustion F ny
      · have he : y = (degreeTenCenter F a).val := (congrArg Subtype.val ha).symm
        rw [he]
        fin_cases a <;> simp
      · have he : y = (degreeTenPair F j b).val := (congrArg Subtype.val hjb).symm
        have hp : G.Adj (degreeTenPair F i (r i)).val (degreeTenPair F j b).val := by
          simpa only [he] using hiy
        by_cases hb : b = r j
        · rw [hb] at hp
          exact False.elim (hB.2.2.1 i j hp)
        · have hb' : b = r j + 1 := by
            have htwo : ∀ b t : Fin 2, b ≠ t → b = t + 1 := by decide +kernel
            exact htwo b (r j) hb
          rw [hb'] at hp
          exact False.elim (hB.2.2.2.1 i j hp)
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

theorem degreeTen_other_inside_neighbors_le_four (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r) (i : Fin 4) :
    (packingNeighborsIn G (degreeTenClosedSet G v)
      (degreeTenPair F i (r i + 1)).val).card ≤ 4 := by
  let s := (degreeTenPair F i (r i + 1)).val
  have hs : s ∈ degreeTenOtherSet F r :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hcard : ((degreeTenOtherSet F r).erase s).card = 3 := by
    rw [Finset.card_erase_of_mem hs, degreeTenOtherSet_card]
  have hsub : packingNeighborsIn G (degreeTenClosedSet G v) s ⊆
      insert v ((degreeTenOtherSet F r).erase s) := by
    intro y hy
    obtain ⟨hyW, hsy⟩ := Finset.mem_filter.mp hy
    obtain hyv | hyN := Finset.mem_insert.mp hyW
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · let ny : G.neighborSet v := ⟨y, (G.mem_neighborFinset v y).mp hyN⟩
      obtain ⟨a, ha⟩ | ⟨j, b, hjb⟩ := degreeTenFrame_neighbor_exhaustion F ny
      · have he : y = (degreeTenCenter F a).val := (congrArg Subtype.val ha).symm
        have hp : G.Adj (degreeTenCenter F a).val (degreeTenPair F i (r i + 1)).val := by
          simpa only [he] using hsy.symm
        fin_cases a
        · exact False.elim ((hB.1 i).2.2.1 hp)
        · exact False.elim ((hB.1 i).2.2.2 hp)
      · have he : y = (degreeTenPair F j b).val := (congrArg Subtype.val hjb).symm
        by_cases hb : b = r j
        · have hp : G.Adj (degreeTenPair F j (r j)).val
              (degreeTenPair F i (r i + 1)).val := by
            simpa only [he, hb] using hsy.symm
          exact False.elim (hB.2.2.2.1 j i hp)
        · have hb' : b = r j + 1 := by
            have htwo : ∀ b t : Fin 2, b ≠ t → b = t + 1 := by decide +kernel
            exact htwo b (r j) hb
          refine Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hsy.ne.symm, ?_⟩))
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp only [he, hb']⟩
  calc
    _ ≤ (insert v ((degreeTenOtherSet F r).erase s)).card := Finset.card_le_card hsub
    _ ≤ ((degreeTenOtherSet F r).erase s).card + 1 := Finset.card_insert_le _ _
    _ = 4 := by rw [hcard]

theorem degreeTen_common_pool_row_ge_seven (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r)
    (hmin : ∀ x : V, 10 ≤ G.degree x) (i : Fin 4) :
    7 ≤ (packingNeighborsIn G (degreeTenCommonPool F r)
      (degreeTenPair F i (r i)).val).card := by
  have hlo : 7 ≤ (packingNeighborsIn G (degreeTenOutside G v)
      (degreeTenPair F i (r i)).val).card :=
    packingNeighborsIn_compl_lower (degreeTenClosedSet G v)
      (degreeTenPair F i (r i)).val 10 3 (hmin _)
      (degreeTen_common_inside_neighbors_le_three F r hB i)
  have hsub : packingNeighborsIn G (degreeTenOutside G v)
      (degreeTenPair F i (r i)).val ⊆
      packingNeighborsIn G (degreeTenCommonPool F r) (degreeTenPair F i (r i)).val := by
    intro z hz
    obtain ⟨hzO, hiz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hzO, i, hiz.symm⟩, hiz⟩
  exact hlo.trans (Finset.card_le_card hsub)

theorem degreeTenCommonPool_card_ge_twenty_eight (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r)
    (hmin : ∀ x : V, 10 ≤ G.degree x) : 28 ≤ (degreeTenCommonPool F r).card := by
  have hrow : ∀ x ∈ degreeTenCommonSet F r,
      7 ≤ (packingNeighborsIn G (degreeTenCommonPool F r) x).card := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact degreeTen_common_pool_row_ge_seven F r hB hmin i
  have hcommon : ∀ z ∈ degreeTenCommonPool F r, ∀ x ∈ degreeTenCommonSet F r,
      ∀ y ∈ degreeTenCommonSet F r, G.Adj x z → G.Adj y z → x = y := by
    intro z hz x hx y hy hxz hyz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hij := degreeTen_common_outside_hook_unique hr F r hB.1 z
      (Finset.mem_filter.mp hz).1 i j hxz.symm hyz.symm
    exact congrArg (fun k => (degreeTenPair F k (r k)).val) hij
  have hh := actual_open_neighborhood_uniform_packing (G := G)
    (degreeTenCommonSet F r) (degreeTenCommonPool F r) 7 hrow hcommon
  rw [degreeTenCommonSet_card] at hh
  exact hh

theorem degreeTenOtherPool_card_ge_six (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r)
    (hmin : ∀ x : V, 10 ≤ G.degree x) : 6 ≤ (degreeTenOtherPool F r).card := by
  have hlo : 6 ≤ (packingNeighborsIn G (degreeTenOutside G v)
      (degreeTenPair F 0 (r 0 + 1)).val).card :=
    packingNeighborsIn_compl_lower (degreeTenClosedSet G v)
      (degreeTenPair F 0 (r 0 + 1)).val 10 4 (hmin _)
      (degreeTen_other_inside_neighbors_le_four F r hB 0)
  have hsub : packingNeighborsIn G (degreeTenOutside G v)
      (degreeTenPair F 0 (r 0 + 1)).val ⊆ degreeTenOtherPool F r := by
    intro z hz
    obtain ⟨hzO, hsz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzO, 0, hsz.symm⟩
  exact hlo.trans (Finset.card_le_card hsub)

theorem degreeTen_common_card_ge_forty_five (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r)
    (hv : G.degree v = 10) (hmin : ∀ x : V, 10 ≤ G.degree x) :
    45 ≤ Fintype.card V := by
  have hR := degreeTenCommonPool_card_ge_twenty_eight hr F r hB hmin
  have hS := degreeTenOtherPool_card_ge_six F r hB hmin
  have hd := degreeTen_common_other_pool_disjoint hr F r hB.1
  have hsub : degreeTenCommonPool F r ∪ degreeTenOtherPool F r ⊆ degreeTenOutside G v :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum : (degreeTenCommonPool F r).card + (degreeTenOtherPool F r).card ≤
      (degreeTenOutside G v).card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card hsub
  have hcomp := Finset.card_add_card_compl (degreeTenClosedSet G v)
  change (degreeTenClosedSet G v).card + (degreeTenOutside G v).card = Fintype.card V at hcomp
  rw [degreeTenClosedSet_card hv] at hcomp
  omega

theorem degreeTen_common_packing_impossible (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2) (hB : DegreeTenLocalShapeB F r)
    (hv : G.degree v = 10) (hmin : ∀ x : V, 10 ≤ G.degree x)
    (hn36 : Fintype.card V ≤ 36) : False := by
  have hh := degreeTen_common_card_ge_forty_five hr F r hB hv hmin
  omega

end TaskH.Six

#print axioms TaskH.Six.degreeTenCommonSet
#print axioms TaskH.Six.degreeTenOtherSet
#print axioms TaskH.Six.degreeTenCommonVertex_injective
#print axioms TaskH.Six.degreeTenOtherVertex_injective
#print axioms TaskH.Six.degreeTenCommonSet_card
#print axioms TaskH.Six.degreeTenOtherSet_card
#print axioms TaskH.Six.degreeTenClosedSet_card
#print axioms TaskH.Six.degreeTen_common_inside_neighbors_le_three
#print axioms TaskH.Six.degreeTen_other_inside_neighbors_le_four
#print axioms TaskH.Six.degreeTen_common_pool_row_ge_seven
#print axioms TaskH.Six.degreeTenCommonPool_card_ge_twenty_eight
#print axioms TaskH.Six.degreeTenOtherPool_card_ge_six
#print axioms TaskH.Six.degreeTen_common_card_ge_forty_five
#print axioms TaskH.Six.degreeTen_common_packing_impossible
