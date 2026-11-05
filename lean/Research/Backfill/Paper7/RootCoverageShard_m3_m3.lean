import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m3_m3_m3_m3_m3_m3 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, -3] 2 (-3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_m3

theorem rootnode_m3_m3_m3_m3_m3_m2 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, -2] 2 (-2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_m2

theorem rootnode_m3_m3_m3_m3_m3_m1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_m1

theorem rootnode_m3_m3_m3_m3_m3_p0 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p0

theorem rootnode_m3_m3_m3_m3_m3_p1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p1

theorem rootnode_m3_m3_m3_m3_m3_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p2

theorem rootnode_m3_m3_m3_m3_m3_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p3

theorem rootnode_m3_m3_m3_m3_m3_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p4

theorem rootnode_m3_m3_m3_m3_m3_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 5] 2 (5) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p5

theorem rootnode_m3_m3_m3_m3_m3_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -3, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p6

theorem rootnode_m3_m3_m3_m3_m3_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -3, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p7

theorem rootnode_m3_m3_m3_m3_m3_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -3, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p8

theorem rootnode_m3_m3_m3_m3_m3_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -3, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3_p9

theorem rootnode_m3_m3_m3_m3_m3 : prunedRootCheck candidateRows [-3, -3, -3, -3, -3] 3 (-3) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, -3] 1 (-3)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_m3_m3
  · exact rootnode_m3_m3_m3_m3_m3_m2
  · exact rootnode_m3_m3_m3_m3_m3_m1
  · exact rootnode_m3_m3_m3_m3_m3_p0
  · exact rootnode_m3_m3_m3_m3_m3_p1
  · exact rootnode_m3_m3_m3_m3_m3_p2
  · exact rootnode_m3_m3_m3_m3_m3_p3
  · exact rootnode_m3_m3_m3_m3_m3_p4
  · exact rootnode_m3_m3_m3_m3_m3_p5
  · exact rootnode_m3_m3_m3_m3_m3_p6
  · exact rootnode_m3_m3_m3_m3_m3_p7
  · exact rootnode_m3_m3_m3_m3_m3_p8
  · exact rootnode_m3_m3_m3_m3_m3_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m3

theorem rootnode_m3_m3_m3_m3_m2_m2 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, -2] 2 (-2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_m2

theorem rootnode_m3_m3_m3_m3_m2_m1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_m1

theorem rootnode_m3_m3_m3_m3_m2_p0 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p0

theorem rootnode_m3_m3_m3_m3_m2_p1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p1

theorem rootnode_m3_m3_m3_m3_m2_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p2

theorem rootnode_m3_m3_m3_m3_m2_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p3

theorem rootnode_m3_m3_m3_m3_m2_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p4

theorem rootnode_m3_m3_m3_m3_m2_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p5

theorem rootnode_m3_m3_m3_m3_m2_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p6

theorem rootnode_m3_m3_m3_m3_m2_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p7

theorem rootnode_m3_m3_m3_m3_m2_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p8

theorem rootnode_m3_m3_m3_m3_m2_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2_p9

theorem rootnode_m3_m3_m3_m3_m2 : prunedRootCheck candidateRows [-3, -3, -3, -3, -2] 3 (-2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, -2] 1 (-2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_m2_m2
  · exact rootnode_m3_m3_m3_m3_m2_m1
  · exact rootnode_m3_m3_m3_m3_m2_p0
  · exact rootnode_m3_m3_m3_m3_m2_p1
  · exact rootnode_m3_m3_m3_m3_m2_p2
  · exact rootnode_m3_m3_m3_m3_m2_p3
  · exact rootnode_m3_m3_m3_m3_m2_p4
  · exact rootnode_m3_m3_m3_m3_m2_p5
  · exact rootnode_m3_m3_m3_m3_m2_p6
  · exact rootnode_m3_m3_m3_m3_m2_p7
  · exact rootnode_m3_m3_m3_m3_m2_p8
  · exact rootnode_m3_m3_m3_m3_m2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m2

theorem rootnode_m3_m3_m3_m3_m1_m1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_m1

theorem rootnode_m3_m3_m3_m3_m1_p0 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p0

theorem rootnode_m3_m3_m3_m3_m1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p1

theorem rootnode_m3_m3_m3_m3_m1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p2

theorem rootnode_m3_m3_m3_m3_m1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p3

theorem rootnode_m3_m3_m3_m3_m1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p4

theorem rootnode_m3_m3_m3_m3_m1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p5

theorem rootnode_m3_m3_m3_m3_m1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p6

theorem rootnode_m3_m3_m3_m3_m1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p7

theorem rootnode_m3_m3_m3_m3_m1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p8

theorem rootnode_m3_m3_m3_m3_m1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, -1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1_p9

theorem rootnode_m3_m3_m3_m3_m1 : prunedRootCheck candidateRows [-3, -3, -3, -3, -1] 3 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, -1] 1 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_m1_m1
  · exact rootnode_m3_m3_m3_m3_m1_p0
  · exact rootnode_m3_m3_m3_m3_m1_p1
  · exact rootnode_m3_m3_m3_m3_m1_p2
  · exact rootnode_m3_m3_m3_m3_m1_p3
  · exact rootnode_m3_m3_m3_m3_m1_p4
  · exact rootnode_m3_m3_m3_m3_m1_p5
  · exact rootnode_m3_m3_m3_m3_m1_p6
  · exact rootnode_m3_m3_m3_m3_m1_p7
  · exact rootnode_m3_m3_m3_m3_m1_p8
  · exact rootnode_m3_m3_m3_m3_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_m1

theorem rootnode_m3_m3_m3_m3_p0_p0 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p0

theorem rootnode_m3_m3_m3_m3_p0_p1 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p1

theorem rootnode_m3_m3_m3_m3_p0_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p2

theorem rootnode_m3_m3_m3_m3_p0_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p3

theorem rootnode_m3_m3_m3_m3_p0_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p4

theorem rootnode_m3_m3_m3_m3_p0_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p5

theorem rootnode_m3_m3_m3_m3_p0_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p6

theorem rootnode_m3_m3_m3_m3_p0_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p7

theorem rootnode_m3_m3_m3_m3_p0_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p8

theorem rootnode_m3_m3_m3_m3_p0_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0_p9

theorem rootnode_m3_m3_m3_m3_p0 : prunedRootCheck candidateRows [-3, -3, -3, -3, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_p0_p0
  · exact rootnode_m3_m3_m3_m3_p0_p1
  · exact rootnode_m3_m3_m3_m3_p0_p2
  · exact rootnode_m3_m3_m3_m3_p0_p3
  · exact rootnode_m3_m3_m3_m3_p0_p4
  · exact rootnode_m3_m3_m3_m3_p0_p5
  · exact rootnode_m3_m3_m3_m3_p0_p6
  · exact rootnode_m3_m3_m3_m3_p0_p7
  · exact rootnode_m3_m3_m3_m3_p0_p8
  · exact rootnode_m3_m3_m3_m3_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p0

theorem rootnode_m3_m3_m3_m3_p1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p1

theorem rootnode_m3_m3_m3_m3_p1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p2

theorem rootnode_m3_m3_m3_m3_p1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p3

theorem rootnode_m3_m3_m3_m3_p1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p4

theorem rootnode_m3_m3_m3_m3_p1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p5

theorem rootnode_m3_m3_m3_m3_p1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p6

theorem rootnode_m3_m3_m3_m3_p1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p7

theorem rootnode_m3_m3_m3_m3_p1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p8

theorem rootnode_m3_m3_m3_m3_p1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1_p9

theorem rootnode_m3_m3_m3_m3_p1 : prunedRootCheck candidateRows [-3, -3, -3, -3, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_p1_p1
  · exact rootnode_m3_m3_m3_m3_p1_p2
  · exact rootnode_m3_m3_m3_m3_p1_p3
  · exact rootnode_m3_m3_m3_m3_p1_p4
  · exact rootnode_m3_m3_m3_m3_p1_p5
  · exact rootnode_m3_m3_m3_m3_p1_p6
  · exact rootnode_m3_m3_m3_m3_p1_p7
  · exact rootnode_m3_m3_m3_m3_p1_p8
  · exact rootnode_m3_m3_m3_m3_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p1

theorem rootnode_m3_m3_m3_m3_p2_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p2

theorem rootnode_m3_m3_m3_m3_p2_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p3

theorem rootnode_m3_m3_m3_m3_p2_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p4

theorem rootnode_m3_m3_m3_m3_p2_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p5

theorem rootnode_m3_m3_m3_m3_p2_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p6

theorem rootnode_m3_m3_m3_m3_p2_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p7

theorem rootnode_m3_m3_m3_m3_p2_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p8

theorem rootnode_m3_m3_m3_m3_p2_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2_p9

theorem rootnode_m3_m3_m3_m3_p2 : prunedRootCheck candidateRows [-3, -3, -3, -3, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_p2_p2
  · exact rootnode_m3_m3_m3_m3_p2_p3
  · exact rootnode_m3_m3_m3_m3_p2_p4
  · exact rootnode_m3_m3_m3_m3_p2_p5
  · exact rootnode_m3_m3_m3_m3_p2_p6
  · exact rootnode_m3_m3_m3_m3_p2_p7
  · exact rootnode_m3_m3_m3_m3_p2_p8
  · exact rootnode_m3_m3_m3_m3_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p2

theorem rootnode_m3_m3_m3_m3_p3_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p3

theorem rootnode_m3_m3_m3_m3_p3_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 3, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p4

theorem rootnode_m3_m3_m3_m3_p3_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 3, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p5

theorem rootnode_m3_m3_m3_m3_p3_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 3, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p6

theorem rootnode_m3_m3_m3_m3_p3_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 3, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p7

theorem rootnode_m3_m3_m3_m3_p3_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 3, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p8

theorem rootnode_m3_m3_m3_m3_p3_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 3, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3_p9

theorem rootnode_m3_m3_m3_m3_p3 : prunedRootCheck candidateRows [-3, -3, -3, -3, 3] 3 (3) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3, 3] 1 (3)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_p3_p3
  · exact rootnode_m3_m3_m3_m3_p3_p4
  · exact rootnode_m3_m3_m3_m3_p3_p5
  · exact rootnode_m3_m3_m3_m3_p3_p6
  · exact rootnode_m3_m3_m3_m3_p3_p7
  · exact rootnode_m3_m3_m3_m3_p3_p8
  · exact rootnode_m3_m3_m3_m3_p3_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p3

theorem rootnode_m3_m3_m3_m3_p4 : prunedRootCheck candidateRows [-3, -3, -3, -3, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p4

theorem rootnode_m3_m3_m3_m3_p5 : prunedRootCheck candidateRows [-3, -3, -3, -3, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p5

theorem rootnode_m3_m3_m3_m3_p6 : prunedRootCheck candidateRows [-3, -3, -3, -3, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p6

theorem rootnode_m3_m3_m3_m3_p7 : prunedRootCheck candidateRows [-3, -3, -3, -3, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p7

theorem rootnode_m3_m3_m3_m3_p8 : prunedRootCheck candidateRows [-3, -3, -3, -3, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p8

theorem rootnode_m3_m3_m3_m3_p9 : prunedRootCheck candidateRows [-3, -3, -3, -3, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -3, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3_p9

theorem rootnode_m3_m3_m3_m3 : prunedRootCheck candidateRows [-3, -3, -3, -3] 4 (-3) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -3] 2 (-3)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3_m3
  · exact rootnode_m3_m3_m3_m3_m2
  · exact rootnode_m3_m3_m3_m3_m1
  · exact rootnode_m3_m3_m3_m3_p0
  · exact rootnode_m3_m3_m3_m3_p1
  · exact rootnode_m3_m3_m3_m3_p2
  · exact rootnode_m3_m3_m3_m3_p3
  · exact rootnode_m3_m3_m3_m3_p4
  · exact rootnode_m3_m3_m3_m3_p5
  · exact rootnode_m3_m3_m3_m3_p6
  · exact rootnode_m3_m3_m3_m3_p7
  · exact rootnode_m3_m3_m3_m3_p8
  · exact rootnode_m3_m3_m3_m3_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m3

theorem rootnode_m3_m3_m3_m2_m2_m2 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, -2] 2 (-2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_m2

theorem rootnode_m3_m3_m3_m2_m2_m1 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_m1

theorem rootnode_m3_m3_m3_m2_m2_p0 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p0

theorem rootnode_m3_m3_m3_m2_m2_p1 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p1

theorem rootnode_m3_m3_m3_m2_m2_p2 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p2

theorem rootnode_m3_m3_m3_m2_m2_p3 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p3

theorem rootnode_m3_m3_m3_m2_m2_p4 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p4

theorem rootnode_m3_m3_m3_m2_m2_p5 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p5

theorem rootnode_m3_m3_m3_m2_m2_p6 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p6

theorem rootnode_m3_m3_m3_m2_m2_p7 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p7

theorem rootnode_m3_m3_m3_m2_m2_p8 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p8

theorem rootnode_m3_m3_m3_m2_m2_p9 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2_p9

theorem rootnode_m3_m3_m3_m2_m2 : prunedRootCheck candidateRows [-3, -3, -3, -2, -2] 3 (-2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -2, -2] 1 (-2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m2_m2_m2
  · exact rootnode_m3_m3_m3_m2_m2_m1
  · exact rootnode_m3_m3_m3_m2_m2_p0
  · exact rootnode_m3_m3_m3_m2_m2_p1
  · exact rootnode_m3_m3_m3_m2_m2_p2
  · exact rootnode_m3_m3_m3_m2_m2_p3
  · exact rootnode_m3_m3_m3_m2_m2_p4
  · exact rootnode_m3_m3_m3_m2_m2_p5
  · exact rootnode_m3_m3_m3_m2_m2_p6
  · exact rootnode_m3_m3_m3_m2_m2_p7
  · exact rootnode_m3_m3_m3_m2_m2_p8
  · exact rootnode_m3_m3_m3_m2_m2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m2

theorem rootnode_m3_m3_m3_m2_m1_m1 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_m1

theorem rootnode_m3_m3_m3_m2_m1_p0 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p0

theorem rootnode_m3_m3_m3_m2_m1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p1

theorem rootnode_m3_m3_m3_m2_m1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p2

theorem rootnode_m3_m3_m3_m2_m1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p3

theorem rootnode_m3_m3_m3_m2_m1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p4

theorem rootnode_m3_m3_m3_m2_m1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p5

theorem rootnode_m3_m3_m3_m2_m1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p6

theorem rootnode_m3_m3_m3_m2_m1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p7

theorem rootnode_m3_m3_m3_m2_m1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p8

theorem rootnode_m3_m3_m3_m2_m1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, -1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1_p9

theorem rootnode_m3_m3_m3_m2_m1 : prunedRootCheck candidateRows [-3, -3, -3, -2, -1] 3 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -2, -1] 1 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m2_m1_m1
  · exact rootnode_m3_m3_m3_m2_m1_p0
  · exact rootnode_m3_m3_m3_m2_m1_p1
  · exact rootnode_m3_m3_m3_m2_m1_p2
  · exact rootnode_m3_m3_m3_m2_m1_p3
  · exact rootnode_m3_m3_m3_m2_m1_p4
  · exact rootnode_m3_m3_m3_m2_m1_p5
  · exact rootnode_m3_m3_m3_m2_m1_p6
  · exact rootnode_m3_m3_m3_m2_m1_p7
  · exact rootnode_m3_m3_m3_m2_m1_p8
  · exact rootnode_m3_m3_m3_m2_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_m1

theorem rootnode_m3_m3_m3_m2_p0_p0 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p0

theorem rootnode_m3_m3_m3_m2_p0_p1 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p1

theorem rootnode_m3_m3_m3_m2_p0_p2 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p2

theorem rootnode_m3_m3_m3_m2_p0_p3 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p3

theorem rootnode_m3_m3_m3_m2_p0_p4 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p4

theorem rootnode_m3_m3_m3_m2_p0_p5 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p5

theorem rootnode_m3_m3_m3_m2_p0_p6 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p6

theorem rootnode_m3_m3_m3_m2_p0_p7 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p7

theorem rootnode_m3_m3_m3_m2_p0_p8 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p8

theorem rootnode_m3_m3_m3_m2_p0_p9 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0_p9

theorem rootnode_m3_m3_m3_m2_p0 : prunedRootCheck candidateRows [-3, -3, -3, -2, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -2, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m2_p0_p0
  · exact rootnode_m3_m3_m3_m2_p0_p1
  · exact rootnode_m3_m3_m3_m2_p0_p2
  · exact rootnode_m3_m3_m3_m2_p0_p3
  · exact rootnode_m3_m3_m3_m2_p0_p4
  · exact rootnode_m3_m3_m3_m2_p0_p5
  · exact rootnode_m3_m3_m3_m2_p0_p6
  · exact rootnode_m3_m3_m3_m2_p0_p7
  · exact rootnode_m3_m3_m3_m2_p0_p8
  · exact rootnode_m3_m3_m3_m2_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p0

theorem rootnode_m3_m3_m3_m2_p1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p1

theorem rootnode_m3_m3_m3_m2_p1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p2

theorem rootnode_m3_m3_m3_m2_p1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p3

theorem rootnode_m3_m3_m3_m2_p1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p4

theorem rootnode_m3_m3_m3_m2_p1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p5

theorem rootnode_m3_m3_m3_m2_p1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p6

theorem rootnode_m3_m3_m3_m2_p1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p7

theorem rootnode_m3_m3_m3_m2_p1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p8

theorem rootnode_m3_m3_m3_m2_p1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1_p9

theorem rootnode_m3_m3_m3_m2_p1 : prunedRootCheck candidateRows [-3, -3, -3, -2, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -2, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m2_p1_p1
  · exact rootnode_m3_m3_m3_m2_p1_p2
  · exact rootnode_m3_m3_m3_m2_p1_p3
  · exact rootnode_m3_m3_m3_m2_p1_p4
  · exact rootnode_m3_m3_m3_m2_p1_p5
  · exact rootnode_m3_m3_m3_m2_p1_p6
  · exact rootnode_m3_m3_m3_m2_p1_p7
  · exact rootnode_m3_m3_m3_m2_p1_p8
  · exact rootnode_m3_m3_m3_m2_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p1

theorem rootnode_m3_m3_m3_m2_p2_p2 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p2

theorem rootnode_m3_m3_m3_m2_p2_p3 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p3

theorem rootnode_m3_m3_m3_m2_p2_p4 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p4

theorem rootnode_m3_m3_m3_m2_p2_p5 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p5

theorem rootnode_m3_m3_m3_m2_p2_p6 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p6

theorem rootnode_m3_m3_m3_m2_p2_p7 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p7

theorem rootnode_m3_m3_m3_m2_p2_p8 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p8

theorem rootnode_m3_m3_m3_m2_p2_p9 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2_p9

theorem rootnode_m3_m3_m3_m2_p2 : prunedRootCheck candidateRows [-3, -3, -3, -2, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -2, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m2_p2_p2
  · exact rootnode_m3_m3_m3_m2_p2_p3
  · exact rootnode_m3_m3_m3_m2_p2_p4
  · exact rootnode_m3_m3_m3_m2_p2_p5
  · exact rootnode_m3_m3_m3_m2_p2_p6
  · exact rootnode_m3_m3_m3_m2_p2_p7
  · exact rootnode_m3_m3_m3_m2_p2_p8
  · exact rootnode_m3_m3_m3_m2_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p2

theorem rootnode_m3_m3_m3_m2_p3 : prunedRootCheck candidateRows [-3, -3, -3, -2, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p3

theorem rootnode_m3_m3_m3_m2_p4 : prunedRootCheck candidateRows [-3, -3, -3, -2, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p4

theorem rootnode_m3_m3_m3_m2_p5 : prunedRootCheck candidateRows [-3, -3, -3, -2, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p5

theorem rootnode_m3_m3_m3_m2_p6 : prunedRootCheck candidateRows [-3, -3, -3, -2, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p6

theorem rootnode_m3_m3_m3_m2_p7 : prunedRootCheck candidateRows [-3, -3, -3, -2, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p7

theorem rootnode_m3_m3_m3_m2_p8 : prunedRootCheck candidateRows [-3, -3, -3, -2, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p8

theorem rootnode_m3_m3_m3_m2_p9 : prunedRootCheck candidateRows [-3, -3, -3, -2, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -2, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2_p9

theorem rootnode_m3_m3_m3_m2 : prunedRootCheck candidateRows [-3, -3, -3, -2] 4 (-2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -2] 2 (-2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m2_m2
  · exact rootnode_m3_m3_m3_m2_m1
  · exact rootnode_m3_m3_m3_m2_p0
  · exact rootnode_m3_m3_m3_m2_p1
  · exact rootnode_m3_m3_m3_m2_p2
  · exact rootnode_m3_m3_m3_m2_p3
  · exact rootnode_m3_m3_m3_m2_p4
  · exact rootnode_m3_m3_m3_m2_p5
  · exact rootnode_m3_m3_m3_m2_p6
  · exact rootnode_m3_m3_m3_m2_p7
  · exact rootnode_m3_m3_m3_m2_p8
  · exact rootnode_m3_m3_m3_m2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m2

theorem rootnode_m3_m3_m3_m1_m1_m1 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_m1

theorem rootnode_m3_m3_m3_m1_m1_p0 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p0

theorem rootnode_m3_m3_m3_m1_m1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p1

theorem rootnode_m3_m3_m3_m1_m1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p2

theorem rootnode_m3_m3_m3_m1_m1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p3

theorem rootnode_m3_m3_m3_m1_m1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, -1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p4

theorem rootnode_m3_m3_m3_m1_m1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, -1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p5

theorem rootnode_m3_m3_m3_m1_m1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, -1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p6

theorem rootnode_m3_m3_m3_m1_m1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, -1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p7

theorem rootnode_m3_m3_m3_m1_m1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, -1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p8

theorem rootnode_m3_m3_m3_m1_m1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, -1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1_p9

theorem rootnode_m3_m3_m3_m1_m1 : prunedRootCheck candidateRows [-3, -3, -3, -1, -1] 3 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -1, -1] 1 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m1_m1_m1
  · exact rootnode_m3_m3_m3_m1_m1_p0
  · exact rootnode_m3_m3_m3_m1_m1_p1
  · exact rootnode_m3_m3_m3_m1_m1_p2
  · exact rootnode_m3_m3_m3_m1_m1_p3
  · exact rootnode_m3_m3_m3_m1_m1_p4
  · exact rootnode_m3_m3_m3_m1_m1_p5
  · exact rootnode_m3_m3_m3_m1_m1_p6
  · exact rootnode_m3_m3_m3_m1_m1_p7
  · exact rootnode_m3_m3_m3_m1_m1_p8
  · exact rootnode_m3_m3_m3_m1_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_m1

theorem rootnode_m3_m3_m3_m1_p0_p0 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p0

theorem rootnode_m3_m3_m3_m1_p0_p1 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p1

theorem rootnode_m3_m3_m3_m1_p0_p2 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p2

theorem rootnode_m3_m3_m3_m1_p0_p3 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p3

theorem rootnode_m3_m3_m3_m1_p0_p4 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p4

theorem rootnode_m3_m3_m3_m1_p0_p5 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p5

theorem rootnode_m3_m3_m3_m1_p0_p6 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p6

theorem rootnode_m3_m3_m3_m1_p0_p7 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p7

theorem rootnode_m3_m3_m3_m1_p0_p8 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p8

theorem rootnode_m3_m3_m3_m1_p0_p9 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0_p9

theorem rootnode_m3_m3_m3_m1_p0 : prunedRootCheck candidateRows [-3, -3, -3, -1, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -1, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m1_p0_p0
  · exact rootnode_m3_m3_m3_m1_p0_p1
  · exact rootnode_m3_m3_m3_m1_p0_p2
  · exact rootnode_m3_m3_m3_m1_p0_p3
  · exact rootnode_m3_m3_m3_m1_p0_p4
  · exact rootnode_m3_m3_m3_m1_p0_p5
  · exact rootnode_m3_m3_m3_m1_p0_p6
  · exact rootnode_m3_m3_m3_m1_p0_p7
  · exact rootnode_m3_m3_m3_m1_p0_p8
  · exact rootnode_m3_m3_m3_m1_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p0

theorem rootnode_m3_m3_m3_m1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p1

theorem rootnode_m3_m3_m3_m1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p2

theorem rootnode_m3_m3_m3_m1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p3

theorem rootnode_m3_m3_m3_m1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p4

theorem rootnode_m3_m3_m3_m1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p5

theorem rootnode_m3_m3_m3_m1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p6

theorem rootnode_m3_m3_m3_m1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p7

theorem rootnode_m3_m3_m3_m1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p8

theorem rootnode_m3_m3_m3_m1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1_p9

theorem rootnode_m3_m3_m3_m1_p1 : prunedRootCheck candidateRows [-3, -3, -3, -1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m1_p1_p1
  · exact rootnode_m3_m3_m3_m1_p1_p2
  · exact rootnode_m3_m3_m3_m1_p1_p3
  · exact rootnode_m3_m3_m3_m1_p1_p4
  · exact rootnode_m3_m3_m3_m1_p1_p5
  · exact rootnode_m3_m3_m3_m1_p1_p6
  · exact rootnode_m3_m3_m3_m1_p1_p7
  · exact rootnode_m3_m3_m3_m1_p1_p8
  · exact rootnode_m3_m3_m3_m1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p1

theorem rootnode_m3_m3_m3_m1_p2_p2 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p2

theorem rootnode_m3_m3_m3_m1_p2_p3 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p3

theorem rootnode_m3_m3_m3_m1_p2_p4 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p4

theorem rootnode_m3_m3_m3_m1_p2_p5 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p5

theorem rootnode_m3_m3_m3_m1_p2_p6 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p6

theorem rootnode_m3_m3_m3_m1_p2_p7 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p7

theorem rootnode_m3_m3_m3_m1_p2_p8 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p8

theorem rootnode_m3_m3_m3_m1_p2_p9 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2_p9

theorem rootnode_m3_m3_m3_m1_p2 : prunedRootCheck candidateRows [-3, -3, -3, -1, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -1, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m1_p2_p2
  · exact rootnode_m3_m3_m3_m1_p2_p3
  · exact rootnode_m3_m3_m3_m1_p2_p4
  · exact rootnode_m3_m3_m3_m1_p2_p5
  · exact rootnode_m3_m3_m3_m1_p2_p6
  · exact rootnode_m3_m3_m3_m1_p2_p7
  · exact rootnode_m3_m3_m3_m1_p2_p8
  · exact rootnode_m3_m3_m3_m1_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p2

theorem rootnode_m3_m3_m3_m1_p3 : prunedRootCheck candidateRows [-3, -3, -3, -1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p3

theorem rootnode_m3_m3_m3_m1_p4 : prunedRootCheck candidateRows [-3, -3, -3, -1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p4

theorem rootnode_m3_m3_m3_m1_p5 : prunedRootCheck candidateRows [-3, -3, -3, -1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p5

theorem rootnode_m3_m3_m3_m1_p6 : prunedRootCheck candidateRows [-3, -3, -3, -1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p6

theorem rootnode_m3_m3_m3_m1_p7 : prunedRootCheck candidateRows [-3, -3, -3, -1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p7

theorem rootnode_m3_m3_m3_m1_p8 : prunedRootCheck candidateRows [-3, -3, -3, -1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p8

theorem rootnode_m3_m3_m3_m1_p9 : prunedRootCheck candidateRows [-3, -3, -3, -1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, -1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1_p9

theorem rootnode_m3_m3_m3_m1 : prunedRootCheck candidateRows [-3, -3, -3, -1] 4 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, -1] 2 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m1_m1
  · exact rootnode_m3_m3_m3_m1_p0
  · exact rootnode_m3_m3_m3_m1_p1
  · exact rootnode_m3_m3_m3_m1_p2
  · exact rootnode_m3_m3_m3_m1_p3
  · exact rootnode_m3_m3_m3_m1_p4
  · exact rootnode_m3_m3_m3_m1_p5
  · exact rootnode_m3_m3_m3_m1_p6
  · exact rootnode_m3_m3_m3_m1_p7
  · exact rootnode_m3_m3_m3_m1_p8
  · exact rootnode_m3_m3_m3_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_m1

theorem rootnode_m3_m3_m3_p0_p0_p0 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p0

theorem rootnode_m3_m3_m3_p0_p0_p1 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p1

theorem rootnode_m3_m3_m3_p0_p0_p2 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p2

theorem rootnode_m3_m3_m3_p0_p0_p3 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p3

theorem rootnode_m3_m3_m3_p0_p0_p4 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p4

theorem rootnode_m3_m3_m3_p0_p0_p5 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p5

theorem rootnode_m3_m3_m3_p0_p0_p6 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p6

theorem rootnode_m3_m3_m3_p0_p0_p7 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p7

theorem rootnode_m3_m3_m3_p0_p0_p8 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p8

theorem rootnode_m3_m3_m3_p0_p0_p9 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0_p9

theorem rootnode_m3_m3_m3_p0_p0 : prunedRootCheck candidateRows [-3, -3, -3, 0, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 0, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p0_p0_p0
  · exact rootnode_m3_m3_m3_p0_p0_p1
  · exact rootnode_m3_m3_m3_p0_p0_p2
  · exact rootnode_m3_m3_m3_p0_p0_p3
  · exact rootnode_m3_m3_m3_p0_p0_p4
  · exact rootnode_m3_m3_m3_p0_p0_p5
  · exact rootnode_m3_m3_m3_p0_p0_p6
  · exact rootnode_m3_m3_m3_p0_p0_p7
  · exact rootnode_m3_m3_m3_p0_p0_p8
  · exact rootnode_m3_m3_m3_p0_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p0

theorem rootnode_m3_m3_m3_p0_p1_p1 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p1

theorem rootnode_m3_m3_m3_p0_p1_p2 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p2

theorem rootnode_m3_m3_m3_p0_p1_p3 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p3

theorem rootnode_m3_m3_m3_p0_p1_p4 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p4

theorem rootnode_m3_m3_m3_p0_p1_p5 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p5

theorem rootnode_m3_m3_m3_p0_p1_p6 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p6

theorem rootnode_m3_m3_m3_p0_p1_p7 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p7

theorem rootnode_m3_m3_m3_p0_p1_p8 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p8

theorem rootnode_m3_m3_m3_p0_p1_p9 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1_p9

theorem rootnode_m3_m3_m3_p0_p1 : prunedRootCheck candidateRows [-3, -3, -3, 0, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 0, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p0_p1_p1
  · exact rootnode_m3_m3_m3_p0_p1_p2
  · exact rootnode_m3_m3_m3_p0_p1_p3
  · exact rootnode_m3_m3_m3_p0_p1_p4
  · exact rootnode_m3_m3_m3_p0_p1_p5
  · exact rootnode_m3_m3_m3_p0_p1_p6
  · exact rootnode_m3_m3_m3_p0_p1_p7
  · exact rootnode_m3_m3_m3_p0_p1_p8
  · exact rootnode_m3_m3_m3_p0_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p1

theorem rootnode_m3_m3_m3_p0_p2_p2 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p2

theorem rootnode_m3_m3_m3_p0_p2_p3 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p3

theorem rootnode_m3_m3_m3_p0_p2_p4 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p4

theorem rootnode_m3_m3_m3_p0_p2_p5 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p5

theorem rootnode_m3_m3_m3_p0_p2_p6 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p6

theorem rootnode_m3_m3_m3_p0_p2_p7 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p7

theorem rootnode_m3_m3_m3_p0_p2_p8 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p8

theorem rootnode_m3_m3_m3_p0_p2_p9 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2_p9

theorem rootnode_m3_m3_m3_p0_p2 : prunedRootCheck candidateRows [-3, -3, -3, 0, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 0, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p0_p2_p2
  · exact rootnode_m3_m3_m3_p0_p2_p3
  · exact rootnode_m3_m3_m3_p0_p2_p4
  · exact rootnode_m3_m3_m3_p0_p2_p5
  · exact rootnode_m3_m3_m3_p0_p2_p6
  · exact rootnode_m3_m3_m3_p0_p2_p7
  · exact rootnode_m3_m3_m3_p0_p2_p8
  · exact rootnode_m3_m3_m3_p0_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p2

theorem rootnode_m3_m3_m3_p0_p3 : prunedRootCheck candidateRows [-3, -3, -3, 0, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p3

theorem rootnode_m3_m3_m3_p0_p4 : prunedRootCheck candidateRows [-3, -3, -3, 0, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p4

theorem rootnode_m3_m3_m3_p0_p5 : prunedRootCheck candidateRows [-3, -3, -3, 0, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p5

theorem rootnode_m3_m3_m3_p0_p6 : prunedRootCheck candidateRows [-3, -3, -3, 0, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p6

theorem rootnode_m3_m3_m3_p0_p7 : prunedRootCheck candidateRows [-3, -3, -3, 0, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p7

theorem rootnode_m3_m3_m3_p0_p8 : prunedRootCheck candidateRows [-3, -3, -3, 0, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p8

theorem rootnode_m3_m3_m3_p0_p9 : prunedRootCheck candidateRows [-3, -3, -3, 0, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 0, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0_p9

theorem rootnode_m3_m3_m3_p0 : prunedRootCheck candidateRows [-3, -3, -3, 0] 4 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 0] 2 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p0_p0
  · exact rootnode_m3_m3_m3_p0_p1
  · exact rootnode_m3_m3_m3_p0_p2
  · exact rootnode_m3_m3_m3_p0_p3
  · exact rootnode_m3_m3_m3_p0_p4
  · exact rootnode_m3_m3_m3_p0_p5
  · exact rootnode_m3_m3_m3_p0_p6
  · exact rootnode_m3_m3_m3_p0_p7
  · exact rootnode_m3_m3_m3_p0_p8
  · exact rootnode_m3_m3_m3_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p0

theorem rootnode_m3_m3_m3_p1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p1

theorem rootnode_m3_m3_m3_p1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p2

theorem rootnode_m3_m3_m3_p1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p3

theorem rootnode_m3_m3_m3_p1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p4

theorem rootnode_m3_m3_m3_p1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p5

theorem rootnode_m3_m3_m3_p1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p6

theorem rootnode_m3_m3_m3_p1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p7

theorem rootnode_m3_m3_m3_p1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p8

theorem rootnode_m3_m3_m3_p1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1_p9

theorem rootnode_m3_m3_m3_p1_p1 : prunedRootCheck candidateRows [-3, -3, -3, 1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p1_p1_p1
  · exact rootnode_m3_m3_m3_p1_p1_p2
  · exact rootnode_m3_m3_m3_p1_p1_p3
  · exact rootnode_m3_m3_m3_p1_p1_p4
  · exact rootnode_m3_m3_m3_p1_p1_p5
  · exact rootnode_m3_m3_m3_p1_p1_p6
  · exact rootnode_m3_m3_m3_p1_p1_p7
  · exact rootnode_m3_m3_m3_p1_p1_p8
  · exact rootnode_m3_m3_m3_p1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p1

theorem rootnode_m3_m3_m3_p1_p2_p2 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p2

theorem rootnode_m3_m3_m3_p1_p2_p3 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p3

theorem rootnode_m3_m3_m3_p1_p2_p4 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p4

theorem rootnode_m3_m3_m3_p1_p2_p5 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p5

theorem rootnode_m3_m3_m3_p1_p2_p6 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p6

theorem rootnode_m3_m3_m3_p1_p2_p7 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p7

theorem rootnode_m3_m3_m3_p1_p2_p8 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p8

theorem rootnode_m3_m3_m3_p1_p2_p9 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2_p9

theorem rootnode_m3_m3_m3_p1_p2 : prunedRootCheck candidateRows [-3, -3, -3, 1, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 1, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p1_p2_p2
  · exact rootnode_m3_m3_m3_p1_p2_p3
  · exact rootnode_m3_m3_m3_p1_p2_p4
  · exact rootnode_m3_m3_m3_p1_p2_p5
  · exact rootnode_m3_m3_m3_p1_p2_p6
  · exact rootnode_m3_m3_m3_p1_p2_p7
  · exact rootnode_m3_m3_m3_p1_p2_p8
  · exact rootnode_m3_m3_m3_p1_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p2

theorem rootnode_m3_m3_m3_p1_p3 : prunedRootCheck candidateRows [-3, -3, -3, 1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p3

theorem rootnode_m3_m3_m3_p1_p4 : prunedRootCheck candidateRows [-3, -3, -3, 1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p4

theorem rootnode_m3_m3_m3_p1_p5 : prunedRootCheck candidateRows [-3, -3, -3, 1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p5

theorem rootnode_m3_m3_m3_p1_p6 : prunedRootCheck candidateRows [-3, -3, -3, 1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p6

theorem rootnode_m3_m3_m3_p1_p7 : prunedRootCheck candidateRows [-3, -3, -3, 1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p7

theorem rootnode_m3_m3_m3_p1_p8 : prunedRootCheck candidateRows [-3, -3, -3, 1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p8

theorem rootnode_m3_m3_m3_p1_p9 : prunedRootCheck candidateRows [-3, -3, -3, 1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1_p9

theorem rootnode_m3_m3_m3_p1 : prunedRootCheck candidateRows [-3, -3, -3, 1] 4 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3, 1] 2 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_p1_p1
  · exact rootnode_m3_m3_m3_p1_p2
  · exact rootnode_m3_m3_m3_p1_p3
  · exact rootnode_m3_m3_m3_p1_p4
  · exact rootnode_m3_m3_m3_p1_p5
  · exact rootnode_m3_m3_m3_p1_p6
  · exact rootnode_m3_m3_m3_p1_p7
  · exact rootnode_m3_m3_m3_p1_p8
  · exact rootnode_m3_m3_m3_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p1

theorem rootnode_m3_m3_m3_p2 : prunedRootCheck candidateRows [-3, -3, -3, 2] 4 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 2] 2 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p2

theorem rootnode_m3_m3_m3_p3 : prunedRootCheck candidateRows [-3, -3, -3, 3] 4 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 3] 2 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p3

theorem rootnode_m3_m3_m3_p4 : prunedRootCheck candidateRows [-3, -3, -3, 4] 4 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 4] 2 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p4

theorem rootnode_m3_m3_m3_p5 : prunedRootCheck candidateRows [-3, -3, -3, 5] 4 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 5] 2 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p5

theorem rootnode_m3_m3_m3_p6 : prunedRootCheck candidateRows [-3, -3, -3, 6] 4 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 6] 2 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p6

theorem rootnode_m3_m3_m3_p7 : prunedRootCheck candidateRows [-3, -3, -3, 7] 4 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 7] 2 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p7

theorem rootnode_m3_m3_m3_p8 : prunedRootCheck candidateRows [-3, -3, -3, 8] 4 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 8] 2 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p8

theorem rootnode_m3_m3_m3_p9 : prunedRootCheck candidateRows [-3, -3, -3, 9] 4 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -3, 9] 2 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3_p9

theorem rootnode_m3_m3_m3 : prunedRootCheck candidateRows [-3, -3, -3] 5 (-3) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -3] 3 (-3)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3_m3
  · exact rootnode_m3_m3_m3_m2
  · exact rootnode_m3_m3_m3_m1
  · exact rootnode_m3_m3_m3_p0
  · exact rootnode_m3_m3_m3_p1
  · exact rootnode_m3_m3_m3_p2
  · exact rootnode_m3_m3_m3_p3
  · exact rootnode_m3_m3_m3_p4
  · exact rootnode_m3_m3_m3_p5
  · exact rootnode_m3_m3_m3_p6
  · exact rootnode_m3_m3_m3_p7
  · exact rootnode_m3_m3_m3_p8
  · exact rootnode_m3_m3_m3_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m3

theorem rootnode_m3_m3_m2_m2_m2_m2 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, -2] 2 (-2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_m2

theorem rootnode_m3_m3_m2_m2_m2_m1 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_m1

theorem rootnode_m3_m3_m2_m2_m2_p0 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p0

theorem rootnode_m3_m3_m2_m2_m2_p1 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p1

theorem rootnode_m3_m3_m2_m2_m2_p2 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p2

theorem rootnode_m3_m3_m2_m2_m2_p3 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p3

theorem rootnode_m3_m3_m2_m2_m2_p4 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 4] 2 (4) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p4

theorem rootnode_m3_m3_m2_m2_m2_p5 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p5

theorem rootnode_m3_m3_m2_m2_m2_p6 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p6

theorem rootnode_m3_m3_m2_m2_m2_p7 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p7

theorem rootnode_m3_m3_m2_m2_m2_p8 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p8

theorem rootnode_m3_m3_m2_m2_m2_p9 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2_p9

theorem rootnode_m3_m3_m2_m2_m2 : prunedRootCheck candidateRows [-3, -3, -2, -2, -2] 3 (-2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -2, -2] 1 (-2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2_m2_m2
  · exact rootnode_m3_m3_m2_m2_m2_m1
  · exact rootnode_m3_m3_m2_m2_m2_p0
  · exact rootnode_m3_m3_m2_m2_m2_p1
  · exact rootnode_m3_m3_m2_m2_m2_p2
  · exact rootnode_m3_m3_m2_m2_m2_p3
  · exact rootnode_m3_m3_m2_m2_m2_p4
  · exact rootnode_m3_m3_m2_m2_m2_p5
  · exact rootnode_m3_m3_m2_m2_m2_p6
  · exact rootnode_m3_m3_m2_m2_m2_p7
  · exact rootnode_m3_m3_m2_m2_m2_p8
  · exact rootnode_m3_m3_m2_m2_m2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m2

theorem rootnode_m3_m3_m2_m2_m1_m1 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_m1

theorem rootnode_m3_m3_m2_m2_m1_p0 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p0

theorem rootnode_m3_m3_m2_m2_m1_p1 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p1

theorem rootnode_m3_m3_m2_m2_m1_p2 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p2

theorem rootnode_m3_m3_m2_m2_m1_p3 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p3

theorem rootnode_m3_m3_m2_m2_m1_p4 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p4

theorem rootnode_m3_m3_m2_m2_m1_p5 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p5

theorem rootnode_m3_m3_m2_m2_m1_p6 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p6

theorem rootnode_m3_m3_m2_m2_m1_p7 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p7

theorem rootnode_m3_m3_m2_m2_m1_p8 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p8

theorem rootnode_m3_m3_m2_m2_m1_p9 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, -1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1_p9

theorem rootnode_m3_m3_m2_m2_m1 : prunedRootCheck candidateRows [-3, -3, -2, -2, -1] 3 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -2, -1] 1 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2_m1_m1
  · exact rootnode_m3_m3_m2_m2_m1_p0
  · exact rootnode_m3_m3_m2_m2_m1_p1
  · exact rootnode_m3_m3_m2_m2_m1_p2
  · exact rootnode_m3_m3_m2_m2_m1_p3
  · exact rootnode_m3_m3_m2_m2_m1_p4
  · exact rootnode_m3_m3_m2_m2_m1_p5
  · exact rootnode_m3_m3_m2_m2_m1_p6
  · exact rootnode_m3_m3_m2_m2_m1_p7
  · exact rootnode_m3_m3_m2_m2_m1_p8
  · exact rootnode_m3_m3_m2_m2_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_m1

theorem rootnode_m3_m3_m2_m2_p0_p0 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p0

theorem rootnode_m3_m3_m2_m2_p0_p1 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p1

theorem rootnode_m3_m3_m2_m2_p0_p2 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p2

theorem rootnode_m3_m3_m2_m2_p0_p3 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p3

theorem rootnode_m3_m3_m2_m2_p0_p4 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p4

theorem rootnode_m3_m3_m2_m2_p0_p5 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p5

theorem rootnode_m3_m3_m2_m2_p0_p6 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p6

theorem rootnode_m3_m3_m2_m2_p0_p7 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p7

theorem rootnode_m3_m3_m2_m2_p0_p8 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p8

theorem rootnode_m3_m3_m2_m2_p0_p9 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0_p9

theorem rootnode_m3_m3_m2_m2_p0 : prunedRootCheck candidateRows [-3, -3, -2, -2, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -2, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2_p0_p0
  · exact rootnode_m3_m3_m2_m2_p0_p1
  · exact rootnode_m3_m3_m2_m2_p0_p2
  · exact rootnode_m3_m3_m2_m2_p0_p3
  · exact rootnode_m3_m3_m2_m2_p0_p4
  · exact rootnode_m3_m3_m2_m2_p0_p5
  · exact rootnode_m3_m3_m2_m2_p0_p6
  · exact rootnode_m3_m3_m2_m2_p0_p7
  · exact rootnode_m3_m3_m2_m2_p0_p8
  · exact rootnode_m3_m3_m2_m2_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p0

theorem rootnode_m3_m3_m2_m2_p1_p1 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p1

theorem rootnode_m3_m3_m2_m2_p1_p2 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p2

theorem rootnode_m3_m3_m2_m2_p1_p3 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p3

theorem rootnode_m3_m3_m2_m2_p1_p4 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p4

theorem rootnode_m3_m3_m2_m2_p1_p5 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p5

theorem rootnode_m3_m3_m2_m2_p1_p6 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p6

theorem rootnode_m3_m3_m2_m2_p1_p7 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p7

theorem rootnode_m3_m3_m2_m2_p1_p8 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p8

theorem rootnode_m3_m3_m2_m2_p1_p9 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1_p9

theorem rootnode_m3_m3_m2_m2_p1 : prunedRootCheck candidateRows [-3, -3, -2, -2, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -2, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2_p1_p1
  · exact rootnode_m3_m3_m2_m2_p1_p2
  · exact rootnode_m3_m3_m2_m2_p1_p3
  · exact rootnode_m3_m3_m2_m2_p1_p4
  · exact rootnode_m3_m3_m2_m2_p1_p5
  · exact rootnode_m3_m3_m2_m2_p1_p6
  · exact rootnode_m3_m3_m2_m2_p1_p7
  · exact rootnode_m3_m3_m2_m2_p1_p8
  · exact rootnode_m3_m3_m2_m2_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p1

theorem rootnode_m3_m3_m2_m2_p2_p2 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p2

theorem rootnode_m3_m3_m2_m2_p2_p3 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p3

theorem rootnode_m3_m3_m2_m2_p2_p4 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p4

theorem rootnode_m3_m3_m2_m2_p2_p5 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p5

theorem rootnode_m3_m3_m2_m2_p2_p6 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p6

theorem rootnode_m3_m3_m2_m2_p2_p7 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p7

theorem rootnode_m3_m3_m2_m2_p2_p8 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p8

theorem rootnode_m3_m3_m2_m2_p2_p9 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2_p9

theorem rootnode_m3_m3_m2_m2_p2 : prunedRootCheck candidateRows [-3, -3, -2, -2, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -2, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2_p2_p2
  · exact rootnode_m3_m3_m2_m2_p2_p3
  · exact rootnode_m3_m3_m2_m2_p2_p4
  · exact rootnode_m3_m3_m2_m2_p2_p5
  · exact rootnode_m3_m3_m2_m2_p2_p6
  · exact rootnode_m3_m3_m2_m2_p2_p7
  · exact rootnode_m3_m3_m2_m2_p2_p8
  · exact rootnode_m3_m3_m2_m2_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p2

theorem rootnode_m3_m3_m2_m2_p3 : prunedRootCheck candidateRows [-3, -3, -2, -2, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p3

theorem rootnode_m3_m3_m2_m2_p4 : prunedRootCheck candidateRows [-3, -3, -2, -2, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p4

theorem rootnode_m3_m3_m2_m2_p5 : prunedRootCheck candidateRows [-3, -3, -2, -2, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p5

theorem rootnode_m3_m3_m2_m2_p6 : prunedRootCheck candidateRows [-3, -3, -2, -2, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p6

theorem rootnode_m3_m3_m2_m2_p7 : prunedRootCheck candidateRows [-3, -3, -2, -2, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p7

theorem rootnode_m3_m3_m2_m2_p8 : prunedRootCheck candidateRows [-3, -3, -2, -2, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p8

theorem rootnode_m3_m3_m2_m2_p9 : prunedRootCheck candidateRows [-3, -3, -2, -2, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -2, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2_p9

theorem rootnode_m3_m3_m2_m2 : prunedRootCheck candidateRows [-3, -3, -2, -2] 4 (-2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -2] 2 (-2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2_m2
  · exact rootnode_m3_m3_m2_m2_m1
  · exact rootnode_m3_m3_m2_m2_p0
  · exact rootnode_m3_m3_m2_m2_p1
  · exact rootnode_m3_m3_m2_m2_p2
  · exact rootnode_m3_m3_m2_m2_p3
  · exact rootnode_m3_m3_m2_m2_p4
  · exact rootnode_m3_m3_m2_m2_p5
  · exact rootnode_m3_m3_m2_m2_p6
  · exact rootnode_m3_m3_m2_m2_p7
  · exact rootnode_m3_m3_m2_m2_p8
  · exact rootnode_m3_m3_m2_m2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m2

theorem rootnode_m3_m3_m2_m1_m1_m1 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_m1

theorem rootnode_m3_m3_m2_m1_m1_p0 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p0

theorem rootnode_m3_m3_m2_m1_m1_p1 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p1

theorem rootnode_m3_m3_m2_m1_m1_p2 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p2

theorem rootnode_m3_m3_m2_m1_m1_p3 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p3

theorem rootnode_m3_m3_m2_m1_m1_p4 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, -1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p4

theorem rootnode_m3_m3_m2_m1_m1_p5 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, -1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p5

theorem rootnode_m3_m3_m2_m1_m1_p6 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, -1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p6

theorem rootnode_m3_m3_m2_m1_m1_p7 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, -1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p7

theorem rootnode_m3_m3_m2_m1_m1_p8 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, -1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p8

theorem rootnode_m3_m3_m2_m1_m1_p9 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, -1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1_p9

theorem rootnode_m3_m3_m2_m1_m1 : prunedRootCheck candidateRows [-3, -3, -2, -1, -1] 3 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -1, -1] 1 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m1_m1_m1
  · exact rootnode_m3_m3_m2_m1_m1_p0
  · exact rootnode_m3_m3_m2_m1_m1_p1
  · exact rootnode_m3_m3_m2_m1_m1_p2
  · exact rootnode_m3_m3_m2_m1_m1_p3
  · exact rootnode_m3_m3_m2_m1_m1_p4
  · exact rootnode_m3_m3_m2_m1_m1_p5
  · exact rootnode_m3_m3_m2_m1_m1_p6
  · exact rootnode_m3_m3_m2_m1_m1_p7
  · exact rootnode_m3_m3_m2_m1_m1_p8
  · exact rootnode_m3_m3_m2_m1_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_m1

theorem rootnode_m3_m3_m2_m1_p0_p0 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p0

theorem rootnode_m3_m3_m2_m1_p0_p1 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p1

theorem rootnode_m3_m3_m2_m1_p0_p2 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p2

theorem rootnode_m3_m3_m2_m1_p0_p3 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p3

theorem rootnode_m3_m3_m2_m1_p0_p4 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p4

theorem rootnode_m3_m3_m2_m1_p0_p5 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p5

theorem rootnode_m3_m3_m2_m1_p0_p6 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p6

theorem rootnode_m3_m3_m2_m1_p0_p7 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p7

theorem rootnode_m3_m3_m2_m1_p0_p8 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p8

theorem rootnode_m3_m3_m2_m1_p0_p9 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0_p9

theorem rootnode_m3_m3_m2_m1_p0 : prunedRootCheck candidateRows [-3, -3, -2, -1, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -1, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m1_p0_p0
  · exact rootnode_m3_m3_m2_m1_p0_p1
  · exact rootnode_m3_m3_m2_m1_p0_p2
  · exact rootnode_m3_m3_m2_m1_p0_p3
  · exact rootnode_m3_m3_m2_m1_p0_p4
  · exact rootnode_m3_m3_m2_m1_p0_p5
  · exact rootnode_m3_m3_m2_m1_p0_p6
  · exact rootnode_m3_m3_m2_m1_p0_p7
  · exact rootnode_m3_m3_m2_m1_p0_p8
  · exact rootnode_m3_m3_m2_m1_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p0

theorem rootnode_m3_m3_m2_m1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p1

theorem rootnode_m3_m3_m2_m1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p2

theorem rootnode_m3_m3_m2_m1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p3

theorem rootnode_m3_m3_m2_m1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p4

theorem rootnode_m3_m3_m2_m1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p5

theorem rootnode_m3_m3_m2_m1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p6

theorem rootnode_m3_m3_m2_m1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p7

theorem rootnode_m3_m3_m2_m1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p8

theorem rootnode_m3_m3_m2_m1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1_p9

theorem rootnode_m3_m3_m2_m1_p1 : prunedRootCheck candidateRows [-3, -3, -2, -1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m1_p1_p1
  · exact rootnode_m3_m3_m2_m1_p1_p2
  · exact rootnode_m3_m3_m2_m1_p1_p3
  · exact rootnode_m3_m3_m2_m1_p1_p4
  · exact rootnode_m3_m3_m2_m1_p1_p5
  · exact rootnode_m3_m3_m2_m1_p1_p6
  · exact rootnode_m3_m3_m2_m1_p1_p7
  · exact rootnode_m3_m3_m2_m1_p1_p8
  · exact rootnode_m3_m3_m2_m1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p1

theorem rootnode_m3_m3_m2_m1_p2_p2 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p2

theorem rootnode_m3_m3_m2_m1_p2_p3 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p3

theorem rootnode_m3_m3_m2_m1_p2_p4 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p4

theorem rootnode_m3_m3_m2_m1_p2_p5 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p5

theorem rootnode_m3_m3_m2_m1_p2_p6 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p6

theorem rootnode_m3_m3_m2_m1_p2_p7 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p7

theorem rootnode_m3_m3_m2_m1_p2_p8 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p8

theorem rootnode_m3_m3_m2_m1_p2_p9 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2_p9

theorem rootnode_m3_m3_m2_m1_p2 : prunedRootCheck candidateRows [-3, -3, -2, -1, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -1, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m1_p2_p2
  · exact rootnode_m3_m3_m2_m1_p2_p3
  · exact rootnode_m3_m3_m2_m1_p2_p4
  · exact rootnode_m3_m3_m2_m1_p2_p5
  · exact rootnode_m3_m3_m2_m1_p2_p6
  · exact rootnode_m3_m3_m2_m1_p2_p7
  · exact rootnode_m3_m3_m2_m1_p2_p8
  · exact rootnode_m3_m3_m2_m1_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p2

theorem rootnode_m3_m3_m2_m1_p3 : prunedRootCheck candidateRows [-3, -3, -2, -1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p3

theorem rootnode_m3_m3_m2_m1_p4 : prunedRootCheck candidateRows [-3, -3, -2, -1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p4

theorem rootnode_m3_m3_m2_m1_p5 : prunedRootCheck candidateRows [-3, -3, -2, -1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p5

theorem rootnode_m3_m3_m2_m1_p6 : prunedRootCheck candidateRows [-3, -3, -2, -1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p6

theorem rootnode_m3_m3_m2_m1_p7 : prunedRootCheck candidateRows [-3, -3, -2, -1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p7

theorem rootnode_m3_m3_m2_m1_p8 : prunedRootCheck candidateRows [-3, -3, -2, -1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p8

theorem rootnode_m3_m3_m2_m1_p9 : prunedRootCheck candidateRows [-3, -3, -2, -1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, -1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1_p9

theorem rootnode_m3_m3_m2_m1 : prunedRootCheck candidateRows [-3, -3, -2, -1] 4 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, -1] 2 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m1_m1
  · exact rootnode_m3_m3_m2_m1_p0
  · exact rootnode_m3_m3_m2_m1_p1
  · exact rootnode_m3_m3_m2_m1_p2
  · exact rootnode_m3_m3_m2_m1_p3
  · exact rootnode_m3_m3_m2_m1_p4
  · exact rootnode_m3_m3_m2_m1_p5
  · exact rootnode_m3_m3_m2_m1_p6
  · exact rootnode_m3_m3_m2_m1_p7
  · exact rootnode_m3_m3_m2_m1_p8
  · exact rootnode_m3_m3_m2_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_m1

theorem rootnode_m3_m3_m2_p0_p0_p0 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p0

theorem rootnode_m3_m3_m2_p0_p0_p1 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p1

theorem rootnode_m3_m3_m2_p0_p0_p2 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p2

theorem rootnode_m3_m3_m2_p0_p0_p3 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p3

theorem rootnode_m3_m3_m2_p0_p0_p4 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p4

theorem rootnode_m3_m3_m2_p0_p0_p5 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p5

theorem rootnode_m3_m3_m2_p0_p0_p6 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p6

theorem rootnode_m3_m3_m2_p0_p0_p7 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p7

theorem rootnode_m3_m3_m2_p0_p0_p8 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p8

theorem rootnode_m3_m3_m2_p0_p0_p9 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0_p9

theorem rootnode_m3_m3_m2_p0_p0 : prunedRootCheck candidateRows [-3, -3, -2, 0, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, 0, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_p0_p0_p0
  · exact rootnode_m3_m3_m2_p0_p0_p1
  · exact rootnode_m3_m3_m2_p0_p0_p2
  · exact rootnode_m3_m3_m2_p0_p0_p3
  · exact rootnode_m3_m3_m2_p0_p0_p4
  · exact rootnode_m3_m3_m2_p0_p0_p5
  · exact rootnode_m3_m3_m2_p0_p0_p6
  · exact rootnode_m3_m3_m2_p0_p0_p7
  · exact rootnode_m3_m3_m2_p0_p0_p8
  · exact rootnode_m3_m3_m2_p0_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p0

theorem rootnode_m3_m3_m2_p0_p1_p1 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p1

theorem rootnode_m3_m3_m2_p0_p1_p2 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p2

theorem rootnode_m3_m3_m2_p0_p1_p3 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p3

theorem rootnode_m3_m3_m2_p0_p1_p4 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p4

theorem rootnode_m3_m3_m2_p0_p1_p5 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p5

theorem rootnode_m3_m3_m2_p0_p1_p6 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p6

theorem rootnode_m3_m3_m2_p0_p1_p7 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p7

theorem rootnode_m3_m3_m2_p0_p1_p8 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p8

theorem rootnode_m3_m3_m2_p0_p1_p9 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1_p9

theorem rootnode_m3_m3_m2_p0_p1 : prunedRootCheck candidateRows [-3, -3, -2, 0, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, 0, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_p0_p1_p1
  · exact rootnode_m3_m3_m2_p0_p1_p2
  · exact rootnode_m3_m3_m2_p0_p1_p3
  · exact rootnode_m3_m3_m2_p0_p1_p4
  · exact rootnode_m3_m3_m2_p0_p1_p5
  · exact rootnode_m3_m3_m2_p0_p1_p6
  · exact rootnode_m3_m3_m2_p0_p1_p7
  · exact rootnode_m3_m3_m2_p0_p1_p8
  · exact rootnode_m3_m3_m2_p0_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p1

theorem rootnode_m3_m3_m2_p0_p2_p2 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p2

theorem rootnode_m3_m3_m2_p0_p2_p3 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p3

theorem rootnode_m3_m3_m2_p0_p2_p4 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p4

theorem rootnode_m3_m3_m2_p0_p2_p5 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p5

theorem rootnode_m3_m3_m2_p0_p2_p6 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p6

theorem rootnode_m3_m3_m2_p0_p2_p7 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p7

theorem rootnode_m3_m3_m2_p0_p2_p8 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p8

theorem rootnode_m3_m3_m2_p0_p2_p9 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2_p9

theorem rootnode_m3_m3_m2_p0_p2 : prunedRootCheck candidateRows [-3, -3, -2, 0, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, 0, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_p0_p2_p2
  · exact rootnode_m3_m3_m2_p0_p2_p3
  · exact rootnode_m3_m3_m2_p0_p2_p4
  · exact rootnode_m3_m3_m2_p0_p2_p5
  · exact rootnode_m3_m3_m2_p0_p2_p6
  · exact rootnode_m3_m3_m2_p0_p2_p7
  · exact rootnode_m3_m3_m2_p0_p2_p8
  · exact rootnode_m3_m3_m2_p0_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p2

theorem rootnode_m3_m3_m2_p0_p3 : prunedRootCheck candidateRows [-3, -3, -2, 0, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p3

theorem rootnode_m3_m3_m2_p0_p4 : prunedRootCheck candidateRows [-3, -3, -2, 0, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p4

theorem rootnode_m3_m3_m2_p0_p5 : prunedRootCheck candidateRows [-3, -3, -2, 0, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p5

theorem rootnode_m3_m3_m2_p0_p6 : prunedRootCheck candidateRows [-3, -3, -2, 0, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p6

theorem rootnode_m3_m3_m2_p0_p7 : prunedRootCheck candidateRows [-3, -3, -2, 0, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p7

theorem rootnode_m3_m3_m2_p0_p8 : prunedRootCheck candidateRows [-3, -3, -2, 0, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p8

theorem rootnode_m3_m3_m2_p0_p9 : prunedRootCheck candidateRows [-3, -3, -2, 0, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 0, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0_p9

theorem rootnode_m3_m3_m2_p0 : prunedRootCheck candidateRows [-3, -3, -2, 0] 4 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, 0] 2 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_p0_p0
  · exact rootnode_m3_m3_m2_p0_p1
  · exact rootnode_m3_m3_m2_p0_p2
  · exact rootnode_m3_m3_m2_p0_p3
  · exact rootnode_m3_m3_m2_p0_p4
  · exact rootnode_m3_m3_m2_p0_p5
  · exact rootnode_m3_m3_m2_p0_p6
  · exact rootnode_m3_m3_m2_p0_p7
  · exact rootnode_m3_m3_m2_p0_p8
  · exact rootnode_m3_m3_m2_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p0

theorem rootnode_m3_m3_m2_p1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p1

theorem rootnode_m3_m3_m2_p1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p2

theorem rootnode_m3_m3_m2_p1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p3

theorem rootnode_m3_m3_m2_p1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p4

theorem rootnode_m3_m3_m2_p1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p5

theorem rootnode_m3_m3_m2_p1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p6

theorem rootnode_m3_m3_m2_p1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p7

theorem rootnode_m3_m3_m2_p1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p8

theorem rootnode_m3_m3_m2_p1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1_p9

theorem rootnode_m3_m3_m2_p1_p1 : prunedRootCheck candidateRows [-3, -3, -2, 1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, 1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_p1_p1_p1
  · exact rootnode_m3_m3_m2_p1_p1_p2
  · exact rootnode_m3_m3_m2_p1_p1_p3
  · exact rootnode_m3_m3_m2_p1_p1_p4
  · exact rootnode_m3_m3_m2_p1_p1_p5
  · exact rootnode_m3_m3_m2_p1_p1_p6
  · exact rootnode_m3_m3_m2_p1_p1_p7
  · exact rootnode_m3_m3_m2_p1_p1_p8
  · exact rootnode_m3_m3_m2_p1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p1

theorem rootnode_m3_m3_m2_p1_p2 : prunedRootCheck candidateRows [-3, -3, -2, 1, 2] 3 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 2] 1 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p2

theorem rootnode_m3_m3_m2_p1_p3 : prunedRootCheck candidateRows [-3, -3, -2, 1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p3

theorem rootnode_m3_m3_m2_p1_p4 : prunedRootCheck candidateRows [-3, -3, -2, 1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p4

theorem rootnode_m3_m3_m2_p1_p5 : prunedRootCheck candidateRows [-3, -3, -2, 1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p5

theorem rootnode_m3_m3_m2_p1_p6 : prunedRootCheck candidateRows [-3, -3, -2, 1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p6

theorem rootnode_m3_m3_m2_p1_p7 : prunedRootCheck candidateRows [-3, -3, -2, 1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p7

theorem rootnode_m3_m3_m2_p1_p8 : prunedRootCheck candidateRows [-3, -3, -2, 1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p8

theorem rootnode_m3_m3_m2_p1_p9 : prunedRootCheck candidateRows [-3, -3, -2, 1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1_p9

theorem rootnode_m3_m3_m2_p1 : prunedRootCheck candidateRows [-3, -3, -2, 1] 4 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2, 1] 2 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_p1_p1
  · exact rootnode_m3_m3_m2_p1_p2
  · exact rootnode_m3_m3_m2_p1_p3
  · exact rootnode_m3_m3_m2_p1_p4
  · exact rootnode_m3_m3_m2_p1_p5
  · exact rootnode_m3_m3_m2_p1_p6
  · exact rootnode_m3_m3_m2_p1_p7
  · exact rootnode_m3_m3_m2_p1_p8
  · exact rootnode_m3_m3_m2_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p1

theorem rootnode_m3_m3_m2_p2 : prunedRootCheck candidateRows [-3, -3, -2, 2] 4 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 2] 2 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p2

theorem rootnode_m3_m3_m2_p3 : prunedRootCheck candidateRows [-3, -3, -2, 3] 4 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 3] 2 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p3

theorem rootnode_m3_m3_m2_p4 : prunedRootCheck candidateRows [-3, -3, -2, 4] 4 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 4] 2 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p4

theorem rootnode_m3_m3_m2_p5 : prunedRootCheck candidateRows [-3, -3, -2, 5] 4 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 5] 2 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p5

theorem rootnode_m3_m3_m2_p6 : prunedRootCheck candidateRows [-3, -3, -2, 6] 4 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 6] 2 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p6

theorem rootnode_m3_m3_m2_p7 : prunedRootCheck candidateRows [-3, -3, -2, 7] 4 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 7] 2 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p7

theorem rootnode_m3_m3_m2_p8 : prunedRootCheck candidateRows [-3, -3, -2, 8] 4 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 8] 2 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p8

theorem rootnode_m3_m3_m2_p9 : prunedRootCheck candidateRows [-3, -3, -2, 9] 4 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -2, 9] 2 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2_p9

theorem rootnode_m3_m3_m2 : prunedRootCheck candidateRows [-3, -3, -2] 5 (-2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -2] 3 (-2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m2_m2
  · exact rootnode_m3_m3_m2_m1
  · exact rootnode_m3_m3_m2_p0
  · exact rootnode_m3_m3_m2_p1
  · exact rootnode_m3_m3_m2_p2
  · exact rootnode_m3_m3_m2_p3
  · exact rootnode_m3_m3_m2_p4
  · exact rootnode_m3_m3_m2_p5
  · exact rootnode_m3_m3_m2_p6
  · exact rootnode_m3_m3_m2_p7
  · exact rootnode_m3_m3_m2_p8
  · exact rootnode_m3_m3_m2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m2

theorem rootnode_m3_m3_m1_m1_m1_m1 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, -1] 2 (-1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_m1

theorem rootnode_m3_m3_m1_m1_m1_p0 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p0

theorem rootnode_m3_m3_m1_m1_m1_p1 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p1

theorem rootnode_m3_m3_m1_m1_m1_p2 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p2

theorem rootnode_m3_m3_m1_m1_m1_p3 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 3] 2 (3) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p3

theorem rootnode_m3_m3_m1_m1_m1_p4 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, -1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p4

theorem rootnode_m3_m3_m1_m1_m1_p5 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, -1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p5

theorem rootnode_m3_m3_m1_m1_m1_p6 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, -1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p6

theorem rootnode_m3_m3_m1_m1_m1_p7 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, -1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p7

theorem rootnode_m3_m3_m1_m1_m1_p8 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, -1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p8

theorem rootnode_m3_m3_m1_m1_m1_p9 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, -1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1_p9

theorem rootnode_m3_m3_m1_m1_m1 : prunedRootCheck candidateRows [-3, -3, -1, -1, -1] 3 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, -1, -1] 1 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_m1_m1_m1
  · exact rootnode_m3_m3_m1_m1_m1_p0
  · exact rootnode_m3_m3_m1_m1_m1_p1
  · exact rootnode_m3_m3_m1_m1_m1_p2
  · exact rootnode_m3_m3_m1_m1_m1_p3
  · exact rootnode_m3_m3_m1_m1_m1_p4
  · exact rootnode_m3_m3_m1_m1_m1_p5
  · exact rootnode_m3_m3_m1_m1_m1_p6
  · exact rootnode_m3_m3_m1_m1_m1_p7
  · exact rootnode_m3_m3_m1_m1_m1_p8
  · exact rootnode_m3_m3_m1_m1_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_m1

theorem rootnode_m3_m3_m1_m1_p0_p0 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p0

theorem rootnode_m3_m3_m1_m1_p0_p1 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p1

theorem rootnode_m3_m3_m1_m1_p0_p2 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p2

theorem rootnode_m3_m3_m1_m1_p0_p3 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p3

theorem rootnode_m3_m3_m1_m1_p0_p4 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p4

theorem rootnode_m3_m3_m1_m1_p0_p5 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p5

theorem rootnode_m3_m3_m1_m1_p0_p6 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p6

theorem rootnode_m3_m3_m1_m1_p0_p7 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p7

theorem rootnode_m3_m3_m1_m1_p0_p8 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p8

theorem rootnode_m3_m3_m1_m1_p0_p9 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0_p9

theorem rootnode_m3_m3_m1_m1_p0 : prunedRootCheck candidateRows [-3, -3, -1, -1, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, -1, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_m1_p0_p0
  · exact rootnode_m3_m3_m1_m1_p0_p1
  · exact rootnode_m3_m3_m1_m1_p0_p2
  · exact rootnode_m3_m3_m1_m1_p0_p3
  · exact rootnode_m3_m3_m1_m1_p0_p4
  · exact rootnode_m3_m3_m1_m1_p0_p5
  · exact rootnode_m3_m3_m1_m1_p0_p6
  · exact rootnode_m3_m3_m1_m1_p0_p7
  · exact rootnode_m3_m3_m1_m1_p0_p8
  · exact rootnode_m3_m3_m1_m1_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p0

theorem rootnode_m3_m3_m1_m1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p1

theorem rootnode_m3_m3_m1_m1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p2

theorem rootnode_m3_m3_m1_m1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p3

theorem rootnode_m3_m3_m1_m1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p4

theorem rootnode_m3_m3_m1_m1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p5

theorem rootnode_m3_m3_m1_m1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p6

theorem rootnode_m3_m3_m1_m1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p7

theorem rootnode_m3_m3_m1_m1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p8

theorem rootnode_m3_m3_m1_m1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1_p9

theorem rootnode_m3_m3_m1_m1_p1 : prunedRootCheck candidateRows [-3, -3, -1, -1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, -1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_m1_p1_p1
  · exact rootnode_m3_m3_m1_m1_p1_p2
  · exact rootnode_m3_m3_m1_m1_p1_p3
  · exact rootnode_m3_m3_m1_m1_p1_p4
  · exact rootnode_m3_m3_m1_m1_p1_p5
  · exact rootnode_m3_m3_m1_m1_p1_p6
  · exact rootnode_m3_m3_m1_m1_p1_p7
  · exact rootnode_m3_m3_m1_m1_p1_p8
  · exact rootnode_m3_m3_m1_m1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p1

theorem rootnode_m3_m3_m1_m1_p2_p2 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p2

theorem rootnode_m3_m3_m1_m1_p2_p3 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p3

theorem rootnode_m3_m3_m1_m1_p2_p4 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p4

theorem rootnode_m3_m3_m1_m1_p2_p5 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p5

theorem rootnode_m3_m3_m1_m1_p2_p6 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p6

theorem rootnode_m3_m3_m1_m1_p2_p7 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p7

theorem rootnode_m3_m3_m1_m1_p2_p8 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p8

theorem rootnode_m3_m3_m1_m1_p2_p9 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 2, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2_p9

theorem rootnode_m3_m3_m1_m1_p2 : prunedRootCheck candidateRows [-3, -3, -1, -1, 2] 3 (2) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, -1, 2] 1 (2)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_m1_p2_p2
  · exact rootnode_m3_m3_m1_m1_p2_p3
  · exact rootnode_m3_m3_m1_m1_p2_p4
  · exact rootnode_m3_m3_m1_m1_p2_p5
  · exact rootnode_m3_m3_m1_m1_p2_p6
  · exact rootnode_m3_m3_m1_m1_p2_p7
  · exact rootnode_m3_m3_m1_m1_p2_p8
  · exact rootnode_m3_m3_m1_m1_p2_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p2

theorem rootnode_m3_m3_m1_m1_p3 : prunedRootCheck candidateRows [-3, -3, -1, -1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p3

theorem rootnode_m3_m3_m1_m1_p4 : prunedRootCheck candidateRows [-3, -3, -1, -1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p4

theorem rootnode_m3_m3_m1_m1_p5 : prunedRootCheck candidateRows [-3, -3, -1, -1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p5

theorem rootnode_m3_m3_m1_m1_p6 : prunedRootCheck candidateRows [-3, -3, -1, -1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p6

theorem rootnode_m3_m3_m1_m1_p7 : prunedRootCheck candidateRows [-3, -3, -1, -1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p7

theorem rootnode_m3_m3_m1_m1_p8 : prunedRootCheck candidateRows [-3, -3, -1, -1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p8

theorem rootnode_m3_m3_m1_m1_p9 : prunedRootCheck candidateRows [-3, -3, -1, -1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, -1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1_p9

theorem rootnode_m3_m3_m1_m1 : prunedRootCheck candidateRows [-3, -3, -1, -1] 4 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, -1] 2 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_m1_m1
  · exact rootnode_m3_m3_m1_m1_p0
  · exact rootnode_m3_m3_m1_m1_p1
  · exact rootnode_m3_m3_m1_m1_p2
  · exact rootnode_m3_m3_m1_m1_p3
  · exact rootnode_m3_m3_m1_m1_p4
  · exact rootnode_m3_m3_m1_m1_p5
  · exact rootnode_m3_m3_m1_m1_p6
  · exact rootnode_m3_m3_m1_m1_p7
  · exact rootnode_m3_m3_m1_m1_p8
  · exact rootnode_m3_m3_m1_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_m1

theorem rootnode_m3_m3_m1_p0_p0_p0 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p0

theorem rootnode_m3_m3_m1_p0_p0_p1 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p1

theorem rootnode_m3_m3_m1_p0_p0_p2 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p2

theorem rootnode_m3_m3_m1_p0_p0_p3 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p3

theorem rootnode_m3_m3_m1_p0_p0_p4 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p4

theorem rootnode_m3_m3_m1_p0_p0_p5 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p5

theorem rootnode_m3_m3_m1_p0_p0_p6 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p6

theorem rootnode_m3_m3_m1_p0_p0_p7 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p7

theorem rootnode_m3_m3_m1_p0_p0_p8 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p8

theorem rootnode_m3_m3_m1_p0_p0_p9 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0_p9

theorem rootnode_m3_m3_m1_p0_p0 : prunedRootCheck candidateRows [-3, -3, -1, 0, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, 0, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_p0_p0_p0
  · exact rootnode_m3_m3_m1_p0_p0_p1
  · exact rootnode_m3_m3_m1_p0_p0_p2
  · exact rootnode_m3_m3_m1_p0_p0_p3
  · exact rootnode_m3_m3_m1_p0_p0_p4
  · exact rootnode_m3_m3_m1_p0_p0_p5
  · exact rootnode_m3_m3_m1_p0_p0_p6
  · exact rootnode_m3_m3_m1_p0_p0_p7
  · exact rootnode_m3_m3_m1_p0_p0_p8
  · exact rootnode_m3_m3_m1_p0_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p0

theorem rootnode_m3_m3_m1_p0_p1_p1 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p1

theorem rootnode_m3_m3_m1_p0_p1_p2 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p2

theorem rootnode_m3_m3_m1_p0_p1_p3 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p3

theorem rootnode_m3_m3_m1_p0_p1_p4 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p4

theorem rootnode_m3_m3_m1_p0_p1_p5 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p5

theorem rootnode_m3_m3_m1_p0_p1_p6 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p6

theorem rootnode_m3_m3_m1_p0_p1_p7 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p7

theorem rootnode_m3_m3_m1_p0_p1_p8 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p8

theorem rootnode_m3_m3_m1_p0_p1_p9 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1_p9

theorem rootnode_m3_m3_m1_p0_p1 : prunedRootCheck candidateRows [-3, -3, -1, 0, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, 0, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_p0_p1_p1
  · exact rootnode_m3_m3_m1_p0_p1_p2
  · exact rootnode_m3_m3_m1_p0_p1_p3
  · exact rootnode_m3_m3_m1_p0_p1_p4
  · exact rootnode_m3_m3_m1_p0_p1_p5
  · exact rootnode_m3_m3_m1_p0_p1_p6
  · exact rootnode_m3_m3_m1_p0_p1_p7
  · exact rootnode_m3_m3_m1_p0_p1_p8
  · exact rootnode_m3_m3_m1_p0_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p1

theorem rootnode_m3_m3_m1_p0_p2 : prunedRootCheck candidateRows [-3, -3, -1, 0, 2] 3 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 2] 1 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p2

theorem rootnode_m3_m3_m1_p0_p3 : prunedRootCheck candidateRows [-3, -3, -1, 0, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p3

theorem rootnode_m3_m3_m1_p0_p4 : prunedRootCheck candidateRows [-3, -3, -1, 0, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p4

theorem rootnode_m3_m3_m1_p0_p5 : prunedRootCheck candidateRows [-3, -3, -1, 0, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p5

theorem rootnode_m3_m3_m1_p0_p6 : prunedRootCheck candidateRows [-3, -3, -1, 0, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p6

theorem rootnode_m3_m3_m1_p0_p7 : prunedRootCheck candidateRows [-3, -3, -1, 0, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p7

theorem rootnode_m3_m3_m1_p0_p8 : prunedRootCheck candidateRows [-3, -3, -1, 0, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p8

theorem rootnode_m3_m3_m1_p0_p9 : prunedRootCheck candidateRows [-3, -3, -1, 0, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 0, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0_p9

theorem rootnode_m3_m3_m1_p0 : prunedRootCheck candidateRows [-3, -3, -1, 0] 4 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, 0] 2 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_p0_p0
  · exact rootnode_m3_m3_m1_p0_p1
  · exact rootnode_m3_m3_m1_p0_p2
  · exact rootnode_m3_m3_m1_p0_p3
  · exact rootnode_m3_m3_m1_p0_p4
  · exact rootnode_m3_m3_m1_p0_p5
  · exact rootnode_m3_m3_m1_p0_p6
  · exact rootnode_m3_m3_m1_p0_p7
  · exact rootnode_m3_m3_m1_p0_p8
  · exact rootnode_m3_m3_m1_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p0

theorem rootnode_m3_m3_m1_p1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p1

theorem rootnode_m3_m3_m1_p1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 2] 2 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 2] 0 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p2

theorem rootnode_m3_m3_m1_p1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p3

theorem rootnode_m3_m3_m1_p1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p4

theorem rootnode_m3_m3_m1_p1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p5

theorem rootnode_m3_m3_m1_p1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p6

theorem rootnode_m3_m3_m1_p1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p7

theorem rootnode_m3_m3_m1_p1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p8

theorem rootnode_m3_m3_m1_p1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1_p9

theorem rootnode_m3_m3_m1_p1_p1 : prunedRootCheck candidateRows [-3, -3, -1, 1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, 1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_p1_p1_p1
  · exact rootnode_m3_m3_m1_p1_p1_p2
  · exact rootnode_m3_m3_m1_p1_p1_p3
  · exact rootnode_m3_m3_m1_p1_p1_p4
  · exact rootnode_m3_m3_m1_p1_p1_p5
  · exact rootnode_m3_m3_m1_p1_p1_p6
  · exact rootnode_m3_m3_m1_p1_p1_p7
  · exact rootnode_m3_m3_m1_p1_p1_p8
  · exact rootnode_m3_m3_m1_p1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p1

theorem rootnode_m3_m3_m1_p1_p2 : prunedRootCheck candidateRows [-3, -3, -1, 1, 2] 3 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 2] 1 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p2

theorem rootnode_m3_m3_m1_p1_p3 : prunedRootCheck candidateRows [-3, -3, -1, 1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p3

theorem rootnode_m3_m3_m1_p1_p4 : prunedRootCheck candidateRows [-3, -3, -1, 1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p4

theorem rootnode_m3_m3_m1_p1_p5 : prunedRootCheck candidateRows [-3, -3, -1, 1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p5

theorem rootnode_m3_m3_m1_p1_p6 : prunedRootCheck candidateRows [-3, -3, -1, 1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p6

theorem rootnode_m3_m3_m1_p1_p7 : prunedRootCheck candidateRows [-3, -3, -1, 1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p7

theorem rootnode_m3_m3_m1_p1_p8 : prunedRootCheck candidateRows [-3, -3, -1, 1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p8

theorem rootnode_m3_m3_m1_p1_p9 : prunedRootCheck candidateRows [-3, -3, -1, 1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1_p9

theorem rootnode_m3_m3_m1_p1 : prunedRootCheck candidateRows [-3, -3, -1, 1] 4 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1, 1] 2 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_p1_p1
  · exact rootnode_m3_m3_m1_p1_p2
  · exact rootnode_m3_m3_m1_p1_p3
  · exact rootnode_m3_m3_m1_p1_p4
  · exact rootnode_m3_m3_m1_p1_p5
  · exact rootnode_m3_m3_m1_p1_p6
  · exact rootnode_m3_m3_m1_p1_p7
  · exact rootnode_m3_m3_m1_p1_p8
  · exact rootnode_m3_m3_m1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p1

theorem rootnode_m3_m3_m1_p2 : prunedRootCheck candidateRows [-3, -3, -1, 2] 4 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 2] 2 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p2

theorem rootnode_m3_m3_m1_p3 : prunedRootCheck candidateRows [-3, -3, -1, 3] 4 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 3] 2 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p3

theorem rootnode_m3_m3_m1_p4 : prunedRootCheck candidateRows [-3, -3, -1, 4] 4 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 4] 2 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p4

theorem rootnode_m3_m3_m1_p5 : prunedRootCheck candidateRows [-3, -3, -1, 5] 4 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 5] 2 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p5

theorem rootnode_m3_m3_m1_p6 : prunedRootCheck candidateRows [-3, -3, -1, 6] 4 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 6] 2 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p6

theorem rootnode_m3_m3_m1_p7 : prunedRootCheck candidateRows [-3, -3, -1, 7] 4 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 7] 2 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p7

theorem rootnode_m3_m3_m1_p8 : prunedRootCheck candidateRows [-3, -3, -1, 8] 4 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 8] 2 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p8

theorem rootnode_m3_m3_m1_p9 : prunedRootCheck candidateRows [-3, -3, -1, 9] 4 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, -1, 9] 2 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1_p9

theorem rootnode_m3_m3_m1 : prunedRootCheck candidateRows [-3, -3, -1] 5 (-1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, -1] 3 (-1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m1_m1
  · exact rootnode_m3_m3_m1_p0
  · exact rootnode_m3_m3_m1_p1
  · exact rootnode_m3_m3_m1_p2
  · exact rootnode_m3_m3_m1_p3
  · exact rootnode_m3_m3_m1_p4
  · exact rootnode_m3_m3_m1_p5
  · exact rootnode_m3_m3_m1_p6
  · exact rootnode_m3_m3_m1_p7
  · exact rootnode_m3_m3_m1_p8
  · exact rootnode_m3_m3_m1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_m1

theorem rootnode_m3_m3_p0_p0_p0_p0 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 0] 2 (0) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p0

theorem rootnode_m3_m3_p0_p0_p0_p1 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p1

theorem rootnode_m3_m3_p0_p0_p0_p2 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 2] 2 (2) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p2

theorem rootnode_m3_m3_p0_p0_p0_p3 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p3

theorem rootnode_m3_m3_p0_p0_p0_p4 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p4

theorem rootnode_m3_m3_p0_p0_p0_p5 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p5

theorem rootnode_m3_m3_p0_p0_p0_p6 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p6

theorem rootnode_m3_m3_p0_p0_p0_p7 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p7

theorem rootnode_m3_m3_p0_p0_p0_p8 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p8

theorem rootnode_m3_m3_p0_p0_p0_p9 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 0, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0_p9

theorem rootnode_m3_m3_p0_p0_p0 : prunedRootCheck candidateRows [-3, -3, 0, 0, 0] 3 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 0, 0, 0] 1 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p0_p0_p0_p0
  · exact rootnode_m3_m3_p0_p0_p0_p1
  · exact rootnode_m3_m3_p0_p0_p0_p2
  · exact rootnode_m3_m3_p0_p0_p0_p3
  · exact rootnode_m3_m3_p0_p0_p0_p4
  · exact rootnode_m3_m3_p0_p0_p0_p5
  · exact rootnode_m3_m3_p0_p0_p0_p6
  · exact rootnode_m3_m3_p0_p0_p0_p7
  · exact rootnode_m3_m3_p0_p0_p0_p8
  · exact rootnode_m3_m3_p0_p0_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p0

theorem rootnode_m3_m3_p0_p0_p1_p1 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p1

theorem rootnode_m3_m3_p0_p0_p1_p2 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 2] 2 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 2] 0 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p2

theorem rootnode_m3_m3_p0_p0_p1_p3 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p3

theorem rootnode_m3_m3_p0_p0_p1_p4 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p4

theorem rootnode_m3_m3_p0_p0_p1_p5 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p5

theorem rootnode_m3_m3_p0_p0_p1_p6 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p6

theorem rootnode_m3_m3_p0_p0_p1_p7 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p7

theorem rootnode_m3_m3_p0_p0_p1_p8 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p8

theorem rootnode_m3_m3_p0_p0_p1_p9 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1_p9

theorem rootnode_m3_m3_p0_p0_p1 : prunedRootCheck candidateRows [-3, -3, 0, 0, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 0, 0, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p0_p0_p1_p1
  · exact rootnode_m3_m3_p0_p0_p1_p2
  · exact rootnode_m3_m3_p0_p0_p1_p3
  · exact rootnode_m3_m3_p0_p0_p1_p4
  · exact rootnode_m3_m3_p0_p0_p1_p5
  · exact rootnode_m3_m3_p0_p0_p1_p6
  · exact rootnode_m3_m3_p0_p0_p1_p7
  · exact rootnode_m3_m3_p0_p0_p1_p8
  · exact rootnode_m3_m3_p0_p0_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p1

theorem rootnode_m3_m3_p0_p0_p2 : prunedRootCheck candidateRows [-3, -3, 0, 0, 2] 3 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 2] 1 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p2

theorem rootnode_m3_m3_p0_p0_p3 : prunedRootCheck candidateRows [-3, -3, 0, 0, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p3

theorem rootnode_m3_m3_p0_p0_p4 : prunedRootCheck candidateRows [-3, -3, 0, 0, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p4

theorem rootnode_m3_m3_p0_p0_p5 : prunedRootCheck candidateRows [-3, -3, 0, 0, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p5

theorem rootnode_m3_m3_p0_p0_p6 : prunedRootCheck candidateRows [-3, -3, 0, 0, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p6

theorem rootnode_m3_m3_p0_p0_p7 : prunedRootCheck candidateRows [-3, -3, 0, 0, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p7

theorem rootnode_m3_m3_p0_p0_p8 : prunedRootCheck candidateRows [-3, -3, 0, 0, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p8

theorem rootnode_m3_m3_p0_p0_p9 : prunedRootCheck candidateRows [-3, -3, 0, 0, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 0, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0_p9

theorem rootnode_m3_m3_p0_p0 : prunedRootCheck candidateRows [-3, -3, 0, 0] 4 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 0, 0] 2 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p0_p0_p0
  · exact rootnode_m3_m3_p0_p0_p1
  · exact rootnode_m3_m3_p0_p0_p2
  · exact rootnode_m3_m3_p0_p0_p3
  · exact rootnode_m3_m3_p0_p0_p4
  · exact rootnode_m3_m3_p0_p0_p5
  · exact rootnode_m3_m3_p0_p0_p6
  · exact rootnode_m3_m3_p0_p0_p7
  · exact rootnode_m3_m3_p0_p0_p8
  · exact rootnode_m3_m3_p0_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p0

theorem rootnode_m3_m3_p0_p1_p1_p1 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p1

theorem rootnode_m3_m3_p0_p1_p1_p2 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 2] 2 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 2] 0 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p2

theorem rootnode_m3_m3_p0_p1_p1_p3 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p3

theorem rootnode_m3_m3_p0_p1_p1_p4 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p4

theorem rootnode_m3_m3_p0_p1_p1_p5 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p5

theorem rootnode_m3_m3_p0_p1_p1_p6 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p6

theorem rootnode_m3_m3_p0_p1_p1_p7 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p7

theorem rootnode_m3_m3_p0_p1_p1_p8 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p8

theorem rootnode_m3_m3_p0_p1_p1_p9 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1_p9

theorem rootnode_m3_m3_p0_p1_p1 : prunedRootCheck candidateRows [-3, -3, 0, 1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 0, 1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p0_p1_p1_p1
  · exact rootnode_m3_m3_p0_p1_p1_p2
  · exact rootnode_m3_m3_p0_p1_p1_p3
  · exact rootnode_m3_m3_p0_p1_p1_p4
  · exact rootnode_m3_m3_p0_p1_p1_p5
  · exact rootnode_m3_m3_p0_p1_p1_p6
  · exact rootnode_m3_m3_p0_p1_p1_p7
  · exact rootnode_m3_m3_p0_p1_p1_p8
  · exact rootnode_m3_m3_p0_p1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p1

theorem rootnode_m3_m3_p0_p1_p2 : prunedRootCheck candidateRows [-3, -3, 0, 1, 2] 3 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 2] 1 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p2

theorem rootnode_m3_m3_p0_p1_p3 : prunedRootCheck candidateRows [-3, -3, 0, 1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p3

theorem rootnode_m3_m3_p0_p1_p4 : prunedRootCheck candidateRows [-3, -3, 0, 1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p4

theorem rootnode_m3_m3_p0_p1_p5 : prunedRootCheck candidateRows [-3, -3, 0, 1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p5

theorem rootnode_m3_m3_p0_p1_p6 : prunedRootCheck candidateRows [-3, -3, 0, 1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p6

theorem rootnode_m3_m3_p0_p1_p7 : prunedRootCheck candidateRows [-3, -3, 0, 1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p7

theorem rootnode_m3_m3_p0_p1_p8 : prunedRootCheck candidateRows [-3, -3, 0, 1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p8

theorem rootnode_m3_m3_p0_p1_p9 : prunedRootCheck candidateRows [-3, -3, 0, 1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1_p9

theorem rootnode_m3_m3_p0_p1 : prunedRootCheck candidateRows [-3, -3, 0, 1] 4 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 0, 1] 2 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p0_p1_p1
  · exact rootnode_m3_m3_p0_p1_p2
  · exact rootnode_m3_m3_p0_p1_p3
  · exact rootnode_m3_m3_p0_p1_p4
  · exact rootnode_m3_m3_p0_p1_p5
  · exact rootnode_m3_m3_p0_p1_p6
  · exact rootnode_m3_m3_p0_p1_p7
  · exact rootnode_m3_m3_p0_p1_p8
  · exact rootnode_m3_m3_p0_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p1

theorem rootnode_m3_m3_p0_p2 : prunedRootCheck candidateRows [-3, -3, 0, 2] 4 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 2] 2 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p2

theorem rootnode_m3_m3_p0_p3 : prunedRootCheck candidateRows [-3, -3, 0, 3] 4 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 3] 2 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p3

theorem rootnode_m3_m3_p0_p4 : prunedRootCheck candidateRows [-3, -3, 0, 4] 4 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 4] 2 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p4

theorem rootnode_m3_m3_p0_p5 : prunedRootCheck candidateRows [-3, -3, 0, 5] 4 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 5] 2 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p5

theorem rootnode_m3_m3_p0_p6 : prunedRootCheck candidateRows [-3, -3, 0, 6] 4 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 6] 2 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p6

theorem rootnode_m3_m3_p0_p7 : prunedRootCheck candidateRows [-3, -3, 0, 7] 4 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 7] 2 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p7

theorem rootnode_m3_m3_p0_p8 : prunedRootCheck candidateRows [-3, -3, 0, 8] 4 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 8] 2 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p8

theorem rootnode_m3_m3_p0_p9 : prunedRootCheck candidateRows [-3, -3, 0, 9] 4 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 0, 9] 2 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0_p9

theorem rootnode_m3_m3_p0 : prunedRootCheck candidateRows [-3, -3, 0] 5 (0) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 0] 3 (0)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p0_p0
  · exact rootnode_m3_m3_p0_p1
  · exact rootnode_m3_m3_p0_p2
  · exact rootnode_m3_m3_p0_p3
  · exact rootnode_m3_m3_p0_p4
  · exact rootnode_m3_m3_p0_p5
  · exact rootnode_m3_m3_p0_p6
  · exact rootnode_m3_m3_p0_p7
  · exact rootnode_m3_m3_p0_p8
  · exact rootnode_m3_m3_p0_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p0

theorem rootnode_m3_m3_p1_p1_p1_p1 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 1] 2 (1) = true := by
  decide +kernel
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p1

theorem rootnode_m3_m3_p1_p1_p1_p2 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 2] 2 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 2] 0 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p2

theorem rootnode_m3_m3_p1_p1_p1_p3 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 3] 2 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 3] 0 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p3

theorem rootnode_m3_m3_p1_p1_p1_p4 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 4] 2 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 4] 0 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p4

theorem rootnode_m3_m3_p1_p1_p1_p5 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 5] 2 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 5] 0 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p5

theorem rootnode_m3_m3_p1_p1_p1_p6 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 6] 2 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 6] 0 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p6

theorem rootnode_m3_m3_p1_p1_p1_p7 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 7] 2 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 7] 0 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p7

theorem rootnode_m3_m3_p1_p1_p1_p8 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 8] 2 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 8] 0 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p8

theorem rootnode_m3_m3_p1_p1_p1_p9 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1, 9] 2 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 1, 9] 0 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1_p9

theorem rootnode_m3_m3_p1_p1_p1 : prunedRootCheck candidateRows [-3, -3, 1, 1, 1] 3 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 1, 1, 1] 1 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p1_p1_p1_p1
  · exact rootnode_m3_m3_p1_p1_p1_p2
  · exact rootnode_m3_m3_p1_p1_p1_p3
  · exact rootnode_m3_m3_p1_p1_p1_p4
  · exact rootnode_m3_m3_p1_p1_p1_p5
  · exact rootnode_m3_m3_p1_p1_p1_p6
  · exact rootnode_m3_m3_p1_p1_p1_p7
  · exact rootnode_m3_m3_p1_p1_p1_p8
  · exact rootnode_m3_m3_p1_p1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p1

theorem rootnode_m3_m3_p1_p1_p2 : prunedRootCheck candidateRows [-3, -3, 1, 1, 2] 3 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 2] 1 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p2

theorem rootnode_m3_m3_p1_p1_p3 : prunedRootCheck candidateRows [-3, -3, 1, 1, 3] 3 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 3] 1 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p3

theorem rootnode_m3_m3_p1_p1_p4 : prunedRootCheck candidateRows [-3, -3, 1, 1, 4] 3 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 4] 1 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p4

theorem rootnode_m3_m3_p1_p1_p5 : prunedRootCheck candidateRows [-3, -3, 1, 1, 5] 3 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 5] 1 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p5

theorem rootnode_m3_m3_p1_p1_p6 : prunedRootCheck candidateRows [-3, -3, 1, 1, 6] 3 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 6] 1 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p6

theorem rootnode_m3_m3_p1_p1_p7 : prunedRootCheck candidateRows [-3, -3, 1, 1, 7] 3 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 7] 1 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p7

theorem rootnode_m3_m3_p1_p1_p8 : prunedRootCheck candidateRows [-3, -3, 1, 1, 8] 3 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 8] 1 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p8

theorem rootnode_m3_m3_p1_p1_p9 : prunedRootCheck candidateRows [-3, -3, 1, 1, 9] 3 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 1, 9] 1 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1_p9

theorem rootnode_m3_m3_p1_p1 : prunedRootCheck candidateRows [-3, -3, 1, 1] 4 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 1, 1] 2 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p1_p1_p1
  · exact rootnode_m3_m3_p1_p1_p2
  · exact rootnode_m3_m3_p1_p1_p3
  · exact rootnode_m3_m3_p1_p1_p4
  · exact rootnode_m3_m3_p1_p1_p5
  · exact rootnode_m3_m3_p1_p1_p6
  · exact rootnode_m3_m3_p1_p1_p7
  · exact rootnode_m3_m3_p1_p1_p8
  · exact rootnode_m3_m3_p1_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p1

theorem rootnode_m3_m3_p1_p2 : prunedRootCheck candidateRows [-3, -3, 1, 2] 4 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 2] 2 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p2

theorem rootnode_m3_m3_p1_p3 : prunedRootCheck candidateRows [-3, -3, 1, 3] 4 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 3] 2 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p3

theorem rootnode_m3_m3_p1_p4 : prunedRootCheck candidateRows [-3, -3, 1, 4] 4 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 4] 2 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p4

theorem rootnode_m3_m3_p1_p5 : prunedRootCheck candidateRows [-3, -3, 1, 5] 4 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 5] 2 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p5

theorem rootnode_m3_m3_p1_p6 : prunedRootCheck candidateRows [-3, -3, 1, 6] 4 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 6] 2 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p6

theorem rootnode_m3_m3_p1_p7 : prunedRootCheck candidateRows [-3, -3, 1, 7] 4 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 7] 2 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p7

theorem rootnode_m3_m3_p1_p8 : prunedRootCheck candidateRows [-3, -3, 1, 8] 4 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 8] 2 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p8

theorem rootnode_m3_m3_p1_p9 : prunedRootCheck candidateRows [-3, -3, 1, 9] 4 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 1, 9] 2 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1_p9

theorem rootnode_m3_m3_p1 : prunedRootCheck candidateRows [-3, -3, 1] 5 (1) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3, 1] 3 (1)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_p1_p1
  · exact rootnode_m3_m3_p1_p2
  · exact rootnode_m3_m3_p1_p3
  · exact rootnode_m3_m3_p1_p4
  · exact rootnode_m3_m3_p1_p5
  · exact rootnode_m3_m3_p1_p6
  · exact rootnode_m3_m3_p1_p7
  · exact rootnode_m3_m3_p1_p8
  · exact rootnode_m3_m3_p1_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p1

theorem rootnode_m3_m3_p2 : prunedRootCheck candidateRows [-3, -3, 2] 5 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 2] 3 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p2

theorem rootnode_m3_m3_p3 : prunedRootCheck candidateRows [-3, -3, 3] 5 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 3] 3 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p3

theorem rootnode_m3_m3_p4 : prunedRootCheck candidateRows [-3, -3, 4] 5 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 4] 3 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p4

theorem rootnode_m3_m3_p5 : prunedRootCheck candidateRows [-3, -3, 5] 5 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 5] 3 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p5

theorem rootnode_m3_m3_p6 : prunedRootCheck candidateRows [-3, -3, 6] 5 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 6] 3 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p6

theorem rootnode_m3_m3_p7 : prunedRootCheck candidateRows [-3, -3, 7] 5 (7) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 7] 3 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p7

theorem rootnode_m3_m3_p8 : prunedRootCheck candidateRows [-3, -3, 8] 5 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 8] 3 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p8

theorem rootnode_m3_m3_p9 : prunedRootCheck candidateRows [-3, -3, 9] 5 (9) = true := by
  exact prunedRootCheck_prune candidateRows [-3, -3, 9] 3 (9) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3_p9

theorem rootnode_m3_m3 : prunedRootCheck candidateRows [-3, -3] 6 (-3) = true := by
  apply prunedRootCheck_join candidateRows [-3, -3] 4 (-3)
  intro z hz _hlo
  simp only [rootChoices_literal, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact rootnode_m3_m3_m3
  · exact rootnode_m3_m3_m2
  · exact rootnode_m3_m3_m1
  · exact rootnode_m3_m3_p0
  · exact rootnode_m3_m3_p1
  · exact rootnode_m3_m3_p2
  · exact rootnode_m3_m3_p3
  · exact rootnode_m3_m3_p4
  · exact rootnode_m3_m3_p5
  · exact rootnode_m3_m3_p6
  · exact rootnode_m3_m3_p7
  · exact rootnode_m3_m3_p8
  · exact rootnode_m3_m3_p9
#print axioms Paper7CycleThreeCertificate.rootnode_m3_m3

end Paper7CycleThreeCertificate
