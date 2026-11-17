import Research.TaskH.Seven.SevenBPSixteenSideCounts

/-! The actual five-quad-neighborhood cover at side size14. The finite
saturation theorem is instantiated with graph adjacency and actual side sets. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem sixteen_opposite_involutive (q : Fin 2) : (q+1)+1=q := by
  revert q
  decide +kernel

theorem sixteen_side_opposite_size_budget [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn45 : Fintype.card V≤45) (q : Fin 2) :
    (sixteenAttachmentOutsideSide c u q).card+
      (sixteenAttachmentOutsideSide c u (q+1)).card≤29 := by
  have hh := sixteen_outside_sides_card_le_twenty_nine c u hu hn45
  have hcases : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide +kernel
  rcases hcases q with hq | hq
  · subst q
    simpa only [show (0 : Fin 2)+1=1 by decide] using hh
  · subst q
    simpa only [show (1 : Fin 2)+1=0 by decide,Nat.add_comm] using hh

theorem sixteen_quad_side_at_least_fourteen [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (hn45 : Fintype.card V≤45)
    (c : G.Coloring Bool) (q : Fin 2) (hq : (sixteenSideWeight c u q 4).Nonempty) :
    14≤(sixteenAttachmentOutsideSide c u q).card := by
  obtain ⟨z,hz⟩ := hq
  exact quad_side_at_least_fourteen _ _ _ _ _ _ _
    (sixteen_side_opposite_size_budget c u hu hn45 q)
    (sixteenAttachment_each_side_attachments_ge_twenty_nine hb h14 u hu hd c q)
    (sixteen_side_attachment_identity hb u hu h14 c q)
    (sixteen_side_high_budget hb u hu h14 hd c q)
    (sixteen_quad_forces_four_zero_on_side hb u hu h14 hd c q z hz)

theorem sixteen_quad_opposite_coverage [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (c : G.Coloring Bool) (q : Fin 2)
    (hQ : (sixteenSideWeight c u q 4).card=5)
    (hB : (sixteenAttachmentOutsideSide c u (q+1)).card=15) :
    ∀w∈sixteenAttachmentOutsideSide c u (q+1),
      ∃z∈sixteenSideWeight c u q 4,G.Adj z w := by
  let A := sixteenSideWeight c u q 4
  let B := sixteenAttachmentOutsideSide c u (q+1)
  have hrow (z : V) (hz : z∈A) : 3≤(B.filter (G.Adj z)).card := by
    have hzs := (Finset.mem_filter.mp hz).1
    rw [sixteen_side_neighbors_exact c u hu q z hzs]
    exact outside_degree_ge_three hb u hu h14 z
      (sixteen_side_not_range c u q z hzs) (hd z)
  have hcol (w : V) (hw : w∈B) : (A.filter (fun z=>G.Adj z w)).card≤1 := by
    have hs : A.filter (fun z=>G.Adj z w)⊆
        (actualOutsideNeighbors G u w).filter (fun z=>3≤(outsideHookFinset G u z).card) := by
      intro z hz
      obtain ⟨hzA,hzw⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzs,hz4⟩ := Finset.mem_filter.mp hzA
      exact Finset.mem_filter.mpr
        ⟨(mem_actualOutsideNeighbors u w z).mpr
          ⟨hzw.symm,sixteen_side_not_range c u q z hzs⟩,by omega⟩
    exact le_trans (Finset.card_le_card hs)
      (outside_neighbors_high_count_le_one hb u hu h14 w
        (sixteen_side_not_range c u (q+1) w hw))
  have hbalance : A.card*3=B.card*1 := by
    change (sixteenSideWeight c u q 4).card*3=
      (sixteenAttachmentOutsideSide c u (q+1)).card*1
    rw [hQ,hB]
  have hs := FiniteBudget.columns_saturated A B G.Adj 3 1 hbalance hrow hcol
  intro w hw
  have hc := hs w hw
  obtain ⟨z,hz⟩ := Finset.card_pos.mp
    (show 0<(A.filter (fun z=>G.Adj z w)).card by omega)
  exact ⟨z,(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩

theorem sixteen_quad_side_not_fourteen [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (hn45 : Fintype.card V≤45)
    (c : G.Coloring Bool) (q : Fin 2) (hq : (sixteenSideWeight c u q 4).Nonempty) :
    (sixteenAttachmentOutsideSide c u q).card≠14 := by
  intro ha14
  obtain ⟨z0,hz0⟩ := hq
  have hzero := sixteen_quad_forces_four_zero_on_side hb u hu h14 hd c q z0 hz0
  obtain ⟨hB,h3,h4,h0,h1⟩ := quad_side_fourteen_extreme _ _ _ _ _ _ _ ha14
    (sixteen_side_opposite_size_budget c u hu hn45 q)
    (sixteenAttachment_each_side_attachments_ge_twenty_nine hb h14 u hu hd c q)
    (sixteen_side_attachment_identity hb u hu h14 c q)
    (sixteen_side_high_budget hb u hu h14 hd c q) hzero
  have hp := sixteen_side_weight_partition hb u hu h14 c q
  have htwo : 0<(sixteenSideWeight c u q 2).card := by omega
  obtain ⟨w,hw2⟩ := Finset.card_pos.mp htwo
  obtain ⟨hws,hwc⟩ := Finset.mem_filter.mp hw2
  have hwout := sixteen_side_not_range c u q w hws
  have hN5 : 5≤(actualOutsideNeighbors G u w).card :=
    outside_degree_ge_five_of_at_most_two_hooks u hu.1 w (by omega) (hd w)
  obtain ⟨a,ha⟩ := Finset.card_pos.mp
    (show 0<(actualOutsideNeighbors G u w).card by omega)
  have hwa := (mem_actualOutsideNeighbors u w a).mp ha
  have haB := sixteen_outside_neighbor_opposite_side c u hu q a w hwa.2 hws hwa.1
  obtain ⟨z,hz4,hza⟩ := sixteen_quad_opposite_coverage hb u hu h14 hd c q h4 hB a haB
  obtain ⟨hzs,hzc⟩ := Finset.mem_filter.mp hz4
  have hzout := sixteen_side_not_range c u q z hzs
  have hzw : z≠w := by
    intro he
    subst z
    omega
  have hwzero := actual_quad_shared_has_zero_hooks hb u hu h14 z a w hzout hwa.2 hwout
    hzw hza hwa.1.symm hzc
  omega

theorem sixteen_quad_side_at_least_fifteen [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (hn45 : Fintype.card V≤45)
    (c : G.Coloring Bool) (q : Fin 2) (hq : (sixteenSideWeight c u q 4).Nonempty) :
    15≤(sixteenAttachmentOutsideSide c u q).card := by
  have hge := sixteen_quad_side_at_least_fourteen hb u hu h14 hd hn45 c q hq
  have hne := sixteen_quad_side_not_fourteen hb u hu h14 hd hn45 c q hq
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.sixteen_opposite_involutive
#print axioms TaskH.Seven.BP.sixteen_side_opposite_size_budget
#print axioms TaskH.Seven.BP.sixteen_quad_side_at_least_fourteen
#print axioms TaskH.Seven.BP.sixteen_quad_opposite_coverage
#print axioms TaskH.Seven.BP.sixteen_quad_side_not_fourteen
#print axioms TaskH.Seven.BP.sixteen_quad_side_at_least_fifteen
