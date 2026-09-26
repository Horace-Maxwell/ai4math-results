import Research.ICGGeneralSwap

/-! Statement audit for the general ICG formalisation (q3-proof.md). -/

-- definitions
#print ICGGeneral.phiX
#print ICGGeneral.ramX
#print ICGGeneral.Tent
#print ICGGeneral.Tv
#print ICGGeneral.L1
#print ICGGeneral.sgnv
#print ICGGeneral.Mentry
#print ICGGeneral.L1mat
#print ICGGeneral.DstarPQ
#print ICGBridge.icgAdj
#print ICGBridge.energy
-- Lemmas 1-2
#check @ICGGeneral.L1_path
#check @ICGGeneral.L1_sign
#check @ICGGeneral.L1_le_sgnv
#check @ICGGeneral.L1_eq_sgnv
#check @ICGGeneral.Tv_sgnv_last_pos
-- Lemma 3-4
#check @ICGGeneral.hcell_le
#check @ICGGeneral.local_ineq
#check @ICGGeneral.local_ineq_strict
-- Theorem 5
#check @ICGGeneral.thm5_le
#check @ICGGeneral.thm5_eq
#check @ICGGeneral.L1mat_sgnv
#check @ICGGeneral.thm5_le_swap
#check @ICGGeneral.thm5_eq_swap
-- bridge
#check @ICGGeneral.energy_icgAdj_pq
-- corollaries
#check @ICGGeneral.checkerboard_unique_max
#check @ICGGeneral.energy_DstarPQ
#check @ICGGeneral.jiang_yang_q3
#check @ICGGeneral.jiang_yang_q3_value
#check @ICGGeneral.DstarPQ_admissible
#check @ICGGeneral.checkerboard_unique_max_odd
#check @ICGGeneral.jiang_yang_thmA
#check @ICGGeneral.DstarPQ_roldan
#print axioms ICGGeneral.thm5_le
#print axioms ICGGeneral.thm5_eq
#print axioms ICGGeneral.energy_icgAdj_pq
#print axioms ICGGeneral.jiang_yang_q3
#print axioms ICGGeneral.jiang_yang_q3_value
#print axioms ICGGeneral.checkerboard_unique_max_odd
#print axioms ICGGeneral.jiang_yang_thmA
#print axioms ICGGeneral.DstarPQ_roldan
