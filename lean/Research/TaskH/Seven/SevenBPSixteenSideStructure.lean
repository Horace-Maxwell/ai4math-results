import Research.TaskH.Seven.SevenBPSixteenSideAttachments
import Research.TaskH.Seven.SevenBPQuadNeighbors

/-! Actual C16 outside-side partition, weight classes, and forced four low
or zero vertices, all transported to the original graph's actual side sets. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

noncomputable def sixteenSideWeight [Fintype V] (c : G.Coloring Bool) (u : Fin 16 → V)
    (q : Fin 2) (j : ℕ) : Finset V :=
  (sixteenAttachmentOutsideSide c u q).filter (fun z=>(outsideHookFinset G u z).card=j)
noncomputable def sixteenSideLow [Fintype V] (c : G.Coloring Bool) (u : Fin 16 → V)
    (q : Fin 2) : Finset V :=
  (sixteenAttachmentOutsideSide c u q).filter (fun z=>(outsideHookFinset G u z).card≤1)
noncomputable def sixteenSideHigh [Fintype V] (c : G.Coloring Bool) (u : Fin 16 → V)
    (q : Fin 2) : Finset V :=
  (sixteenAttachmentOutsideSide c u q).filter (fun z=>3≤(outsideHookFinset G u z).card)

theorem sixteen_side_not_range [Fintype V] (c : G.Coloring Bool) (u : Fin 16 → V)
    (q : Fin 2) (z : V) (hz : z∈sixteenAttachmentOutsideSide c u q) : z∉Set.range u := by
  rintro ⟨i,hi⟩
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)

theorem sixteen_outside_side_union [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) :
    sixteenAttachmentOutsideSide c u 0 ∪ sixteenAttachmentOutsideSide c u 1=Finset.univ \ Finset.univ.image u := by
  have hne := sixteenAttachment_class_colors_ne u hu c 0 1 (by decide) 0 0
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1
  · intro hz
    by_cases h0 : c z≠c (u (sixteenAttachmentClassIndex 0 0))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h0⟩)
    · have he : c z=c (u (sixteenAttachmentClassIndex 0 0)) := not_ne_iff.mp h0
      have h1 : c z≠c (u (sixteenAttachmentClassIndex 1 0)) := by
        intro hh
        exact hne (he.symm.trans hh)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h1⟩)

theorem sixteen_outside_sides_disjoint [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) :
    Disjoint (sixteenAttachmentOutsideSide c u 0) (sixteenAttachmentOutsideSide c u 1) := by
  apply Finset.disjoint_left.mpr
  intro z hz0 hz1
  have h0 := (Finset.mem_filter.mp hz0).2
  have h1 := (Finset.mem_filter.mp hz1).2
  have hne := sixteenAttachment_class_colors_ne u hu c 0 1 (by decide) 0 0
  cases hz : c z <;> cases hx : c (u (sixteenAttachmentClassIndex 0 0)) <;>
    cases hy : c (u (sixteenAttachmentClassIndex 1 0)) <;> simp_all

theorem sixteen_outside_sides_card [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) :
    (sixteenAttachmentOutsideSide c u 0).card+(sixteenAttachmentOutsideSide c u 1).card=Fintype.card V-16 := by
  have hS : (Finset.univ.image u).card=16 := by
    rw [Finset.card_image_of_injective _ hu.1,Finset.card_univ,Fintype.card_fin]
  have hh := Finset.card_union_of_disjoint (sixteen_outside_sides_disjoint c u hu)
  rw [sixteen_outside_side_union c u hu] at hh
  simpa only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,hS] using hh.symm

theorem sixteen_outside_sides_card_le_twenty_nine [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : Fintype.card V≤45) :
    (sixteenAttachmentOutsideSide c u 0).card+(sixteenAttachmentOutsideSide c u 1).card≤29 := by
  have hh := sixteen_outside_sides_card c u hu
  omega

theorem sixteen_outside_neighbor_opposite_side [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) (a b : V)
    (ha : a∉Set.range u) (hb : b∈sixteenAttachmentOutsideSide c u q) (hba : G.Adj b a) :
    a∈sixteenAttachmentOutsideSide c u (q+1) := by
  have hqr : q≠q+1 := by
    have tab : ∀ q : Fin 2,q≠q+1 := by decide +kernel
    exact tab q
  have hne := sixteenAttachment_class_colors_ne u hu c q (q+1) hqr 0 0
  have hbq := (Finset.mem_filter.mp hb).2
  have hbeq : c b=c (u (sixteenAttachmentClassIndex (q+1) 0)) := by
    cases h0 : c b <;> cases h1 : c (u (sixteenAttachmentClassIndex q 0)) <;>
      cases h2 : c (u (sixteenAttachmentClassIndex (q+1) 0)) <;> simp_all
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    exact ha ⟨i,hi⟩
  · intro he
    exact c.valid hba (hbeq.trans he.symm)

theorem sixteen_side_same_color [Fintype V] (c : G.Coloring Bool) (u : Fin 16 → V)
    (q : Fin 2) (z w : V) (hz : z∈sixteenAttachmentOutsideSide c u q)
    (hw : w∉Set.range u) (he : c z=c w) : w∈sixteenAttachmentOutsideSide c u q := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    exact hw ⟨i,hi⟩
  · rw [←he]
    exact (Finset.mem_filter.mp hz).2

theorem sixteen_side_weight_bound [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (c : G.Coloring Bool) (q : Fin 2) (z : V)
    (hz : z∈sixteenAttachmentOutsideSide c u q) : (outsideHookFinset G u z).card≤4 :=
  outside_hook_card_le_four hb u hu h14 z (sixteen_side_not_range c u q z hz)

theorem sixteen_side_neighbors_exact [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) (z : V)
    (hz : z∈sixteenAttachmentOutsideSide c u q) :
    (sixteenAttachmentOutsideSide c u (q+1)).filter (G.Adj z)=actualOutsideNeighbors G u z := by
  ext w
  constructor
  · intro hw
    obtain ⟨hws,hzw⟩ := Finset.mem_filter.mp hw
    exact (mem_actualOutsideNeighbors u z w).mpr
      ⟨hzw,sixteen_side_not_range c u (q+1) w hws⟩
  · intro hw
    have hh := (mem_actualOutsideNeighbors u z w).mp hw
    exact Finset.mem_filter.mpr
      ⟨sixteen_outside_neighbor_opposite_side c u hu q w z hh.2 hz hh.1,hh.1⟩

theorem sixteen_high_forces_four_low_on_side [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (c : G.Coloring Bool) (q : Fin 2) (z : V)
    (hz : z∈sixteenSideHigh c u q) : 4≤(sixteenSideLow c u q).card := by
  obtain ⟨hzs,hz3⟩ := Finset.mem_filter.mp hz
  have hzout := sixteen_side_not_range c u q z hzs
  obtain ⟨a,hza,ha,hN,hL⟩ := high_forces_four_low_actual hb u hu h14 hd z hzout hz3
  have hs : actualOutsideNeighbors G u a \ {z} ⊆ sixteenSideLow c u q := by
    intro w hw
    have hwa := (mem_actualOutsideNeighbors u a w).mp (Finset.mem_sdiff.mp hw).1
    have hws := sixteen_side_same_color c u q z w hzs hwa.2
      (forced_low_same_color c z a w hza hwa.1)
    exact Finset.mem_filter.mpr ⟨hws,hL w hw⟩
  exact le_trans hN (Finset.card_le_card hs)

theorem sixteen_quad_forces_four_zero_on_side [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (c : G.Coloring Bool) (q : Fin 2) (z : V)
    (hz : z∈sixteenSideWeight c u q 4) : 4≤(sixteenSideWeight c u q 0).card := by
  obtain ⟨hzs,hz4⟩ := Finset.mem_filter.mp hz
  have hzout := sixteen_side_not_range c u q z hzs
  obtain ⟨a,hza,ha,hN,hZ⟩ := quad_forces_four_zero_actual hb u hu h14 hd z hzout hz4
  have hs : actualOutsideNeighbors G u a \ {z} ⊆ sixteenSideWeight c u q 0 := by
    intro w hw
    have hwa := (mem_actualOutsideNeighbors u a w).mp (Finset.mem_sdiff.mp hw).1
    have hws := sixteen_side_same_color c u q z w hzs hwa.2
      (forced_low_same_color c z a w hza hwa.1)
    exact Finset.mem_filter.mpr ⟨hws,hZ w hw⟩
  exact le_trans hN (Finset.card_le_card hs)

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.sixteenSideWeight
#print axioms TaskH.Seven.BP.sixteenSideLow
#print axioms TaskH.Seven.BP.sixteenSideHigh
#print axioms TaskH.Seven.BP.sixteen_side_not_range
#print axioms TaskH.Seven.BP.sixteen_outside_side_union
#print axioms TaskH.Seven.BP.sixteen_outside_sides_disjoint
#print axioms TaskH.Seven.BP.sixteen_outside_sides_card
#print axioms TaskH.Seven.BP.sixteen_outside_sides_card_le_twenty_nine
#print axioms TaskH.Seven.BP.sixteen_outside_neighbor_opposite_side
#print axioms TaskH.Seven.BP.sixteen_side_same_color
#print axioms TaskH.Seven.BP.sixteen_side_weight_bound
#print axioms TaskH.Seven.BP.sixteen_side_neighbors_exact
#print axioms TaskH.Seven.BP.sixteen_high_forces_four_low_on_side
#print axioms TaskH.Seven.BP.sixteen_quad_forces_four_zero_on_side
