import Research.TaskH.Seven.SevenBPSixteenQuadSide

/-! Actual C16 double-sided attachment endgame. Size4 hooks are excluded
using the genuine size14 cover obstruction; the remaining0..3 statistics
then contradict the two actual attachment lower bounds29. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem sixteen_side_no_quad [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (hn45 : Fintype.card V≤45)
    (c : G.Coloring Bool) (q : Fin 2) : sixteenSideWeight c u q 4=∅ := by
  by_contra hnot
  have hq := Finset.nonempty_iff_ne_empty.mpr hnot
  have ha := sixteen_quad_side_at_least_fifteen hb u hu h14 hd hn45 c q hq
  have hN := sixteen_side_opposite_size_budget c u hu hn45 q
  have hOpp : sixteenSideWeight c u (q+1) 4=∅ := by
    by_contra hne
    have hb := sixteen_quad_side_at_least_fifteen hb u hu h14 hd hn45 c (q+1)
      (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  have hOpp0 : (sixteenSideWeight c u (q+1) 4).card=0 := by rw [hOpp,Finset.card_empty]
  have hI := sixteen_side_attachment_identity hb u hu h14 c (q+1)
  have hD := sixteen_side_high_budget hb u hu h14 hd c (q+1)
  rw [sixteen_opposite_involutive] at hD
  apply noquad_opposite_to_large_side_impossible
    (sixteenAttachmentOutsideSide c u q).card
    (sixteenAttachmentOutsideSide c u (q+1)).card
    (sixteenSideHookSum c u (q+1)) (sixteenSideWeight c u (q+1) 3).card
    ((sixteenSideWeight c u (q+1) 1).card+2*(sixteenSideWeight c u (q+1) 0).card)
    hN ha
    (sixteenAttachment_each_side_attachments_ge_twenty_nine hb h14 u hu hd c (q+1))
    (by omega) (by omega)
    (sixteen_side_high_count_forces_low hb u hu h14 hd c (q+1))

theorem sixteen_actual_cycle_impossible_at_order_forty_five [Fintype V]
    (hb : G.IsBipartite) (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn45 : Fintype.card V≤45) (hd : ∀z : V,7≤G.degree z)
    (h14 : NoFourteenCycle G) : False := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  have h40 : (sixteenSideWeight c u 0 4).card=0 := by
    rw [sixteen_side_no_quad hb u hu h14 hd hn45 c 0,Finset.card_empty]
  have h41 : (sixteenSideWeight c u 1 4).card=0 := by
    rw [sixteen_side_no_quad hb u hu h14 hd hn45 c 1,Finset.card_empty]
  have hI0 := sixteen_side_attachment_identity hb u hu h14 c 0
  have hI1 := sixteen_side_attachment_identity hb u hu h14 c 1
  have hD0 := sixteen_side_high_budget hb u hu h14 hd c 0
  have hD1 := sixteen_side_high_budget hb u hu h14 hd c 1
  have h01 : (0 : Fin 2)+1=1 := by decide
  have h10 : (1 : Fin 2)+1=0 := by decide
  rw [h01] at hD0
  rw [h10] at hD1
  exact two_noquad_sides_impossible
    (sixteenAttachmentOutsideSide c u 0).card (sixteenAttachmentOutsideSide c u 1).card
    (sixteenSideHookSum c u 0) (sixteenSideHookSum c u 1)
    (sixteenSideWeight c u 0 3).card (sixteenSideWeight c u 1 3).card
    ((sixteenSideWeight c u 0 1).card+2*(sixteenSideWeight c u 0 0).card)
    ((sixteenSideWeight c u 1 1).card+2*(sixteenSideWeight c u 1 0).card)
    (sixteen_outside_sides_card_le_twenty_nine c u hu hn45)
    (sixteenAttachment_each_side_attachments_ge_twenty_nine hb h14 u hu hd c 0)
    (sixteenAttachment_each_side_attachments_ge_twenty_nine hb h14 u hu hd c 1)
    (by omega) (by omega) (by omega) (by omega)
    (sixteen_side_high_count_forces_low hb u hu h14 hd c 0)
    (sixteen_side_high_count_forces_low hb u hu h14 hd c 1)

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.sixteen_side_no_quad
#print axioms TaskH.Seven.BP.sixteen_actual_cycle_impossible_at_order_forty_five
