import Research.Backfill.Paper8.Proof.Tests.Crit
import Research.Backfill.Paper8.Proof.Tests.Spectral

/-!
# Paper 8, known-answer tests (agent `tests`): final module

Known-answer tests of the definitions of the statement file (version 2) that its own test file
`ChallengeTests.lean` leaves untested: `AllEigenvaluesMain`, `adjT`, `secVec`, `sc`, `sig`, `lam`,
`Sb`, `Lamb`, `Ab`, `Gs`, `Ps`, `condS`, `condL`, `condZ`, `NI`, `NII`, `Nei`, `QAdj`, `Ufun`,
`Ubeta`, `IsLeafRowMember`, `FailsAtPair`, `FailsAtOrbit`, `IsBareRowMember`, `CritAat`, `CritA`,
`CritB`, `InRegion`, `regionR`, `sw56a`, `sw56b`, and the data of the version-2 statements. The
tests are in `Research.Backfill.Paper8.Proof.Tests.Poly`, `Counts`, `Crit`, `Vec`, `Switch`, `Cond` and `Spectral`; each block
there names the sentence of the paper or of a review that it reproduces. The lines below print
the foundations used by every named test.
-/


-- `Research.Backfill.Paper8.Proof.Tests.Poly`
#print axioms P8Tests.test_secular_3
#print axioms P8Tests.test_secular_22
#print axioms P8Tests.test_secular_5
#print axioms P8Tests.test_secular_1
#print axioms P8Tests.test_secular_2
#print axioms P8Tests.test_secular_15
#print axioms P8Tests.test_secular_200
#print axioms P8Tests.test_secular_3000
#print axioms P8Tests.test_secular_20
#print axioms P8Tests.test_secular_1800
#print axioms P8Tests.test_secular_5_ne
#print axioms P8Tests.test_R2_15
#print axioms P8Tests.test_R2_1800
#print axioms P8Tests.test_R2_3000
#print axioms P8Tests.test_R2_1
#print axioms P8Tests.test_orbit_15
#print axioms P8Tests.test_noneven_15
#print axioms P8Tests.test_mirror_15
#print axioms P8Tests.test_not_orbit_15_sq
#print axioms P8Tests.test_orbit_1
#print axioms P8Tests.test_even_1
#print axioms P8Tests.test_orbit_3000
#print axioms P8Tests.test_mirror_3000
#print axioms P8Tests.test_noneven_3000
#print axioms P8Tests.test_pair_3000
#print axioms P8Tests.test_mirror_18
#print axioms P8Tests.test_natDegree_18
#print axioms P8Tests.test_noneven_18
#print axioms P8Tests.test_orbit_18
#print axioms P8Tests.test_pair_18
#print axioms P8Tests.test_U1_tight_15

-- `Research.Backfill.Paper8.Proof.Tests.Counts`
#print axioms P8Tests.test_NI_3
#print axioms P8Tests.test_NI_3_direct
#print axioms P8Tests.test_NI_22
#print axioms P8Tests.test_NI_15
#print axioms P8Tests.test_NI_200
#print axioms P8Tests.test_NI_5
#print axioms P8Tests.test_NI_2
#print axioms P8Tests.test_NI_3000
#print axioms P8Tests.test_NI_20
#print axioms P8Tests.test_NII_3
#print axioms P8Tests.test_NII_22
#print axioms P8Tests.test_NII_15
#print axioms P8Tests.test_NII_5
#print axioms P8Tests.test_NII_2
#print axioms P8Tests.test_NII_1
#print axioms P8Tests.test_NII_200
#print axioms P8Tests.test_NII_20
#print axioms P8Tests.test_NII_3000
#print axioms P8Tests.test_NI_1800
#print axioms P8Tests.test_NII_1800
#print axioms P8Tests.test_NI_NII_5
#print axioms P8Tests.test_NI_ne_NII_3000
#print axioms P8Tests.test_Nei_5
#print axioms P8Tests.test_Nei_1
#print axioms P8Tests.test_Nei_3
#print axioms P8Tests.test_Nei_22
#print axioms P8Tests.test_Nei_2
#print axioms P8Tests.test_Nei_200
#print axioms P8Tests.test_Nei_20
#print axioms P8Tests.test_Nei_3000
#print axioms P8Tests.test_count_3000
#print axioms P8Tests.test_count_200
#print axioms P8Tests.test_count_1

-- `Research.Backfill.Paper8.Proof.Tests.Crit`
#print axioms P8Tests.test_not_critA_22
#print axioms P8Tests.test_not_critB_22
#print axioms P8Tests.test_not_critA_200
#print axioms P8Tests.test_not_critB_200
#print axioms P8Tests.test_not_critA_3
#print axioms P8Tests.test_not_critB_3
#print axioms P8Tests.test_exception_22
#print axioms P8Tests.test_exception_200
#print axioms P8Tests.test_exception_3
#print axioms P8Tests.test_CritAat_2
#print axioms P8Tests.test_critA_2
#print axioms P8Tests.test_crit_2
#print axioms P8Tests.test_not_CritAat_3
#print axioms P8Tests.test_critB_20
#print axioms P8Tests.test_region_2
#print axioms P8Tests.test_region_20
#print axioms P8Tests.test_region_22
#print axioms P8Tests.test_region_200
#print axioms P8Tests.test_region_3
#print axioms P8Tests.test_not_region_13
#print axioms P8Tests.test_not_region_222
#print axioms P8Tests.test_not_region_20000
#print axioms P8Tests.test_regionR

-- `Research.Backfill.Paper8.Proof.Tests.Switch`
#print axioms P8Tests.test_adjT_200
#print axioms P8Tests.test_adjT_200_zero
#print axioms P8Tests.test_adjT_degrees_200
#print axioms P8Tests.test_secVec_3
#print axioms P8Tests.test_secVec_eigen_3
#print axioms P8Tests.test_secVec_not_eigen_3
#print axioms P8Tests.test_sw56a
#print axioms P8Tests.test_isSwitching_56a
#print axioms P8Tests.test_sw56b
#print axioms P8Tests.test_isSwitching_56b
#print axioms P8Tests.test_sw56b_ne_one
#print axioms P8Tests.test_isSecular_22
#print axioms P8Tests.test_isSecular_200
#print axioms P8Tests.test_lam_56a
#print axioms P8Tests.test_data_56a
#print axioms P8Tests.test_Gs_56a
#print axioms P8Tests.test_sc_sig_56b
#print axioms P8Tests.test_lam_56b
#print axioms P8Tests.test_Sb_56b
#print axioms P8Tests.test_Lamb_56b
#print axioms P8Tests.test_Ab_56b
#print axioms P8Tests.test_Gs_56b
#print axioms P8Tests.test_Ps_56b
#print axioms P8Tests.test_Sb_56b_ne
#print axioms P8Tests.test_data_56c
#print axioms P8Tests.test_Gs_56c
#print axioms P8Tests.test_Ps_56c
#print axioms P8Tests.test_lemma34_56c
#print axioms P8Tests.test_secVec_dot_56c
#print axioms P8Tests.test_Ufun_31
#print axioms P8Tests.test_Ubeta_31
#print axioms P8Tests.test_Ufun_22
#print axioms P8Tests.test_Ubeta_22
#print axioms P8Tests.test_leafG_56c

-- `Research.Backfill.Paper8.Proof.Tests.Cond`
#print axioms P8Tests.test_condS_56c
#print axioms P8Tests.test_condS_56a
#print axioms P8Tests.test_condS_56b
#print axioms P8Tests.test_not_condS_sL3
#print axioms P8Tests.test_not_condS_K2
#print axioms P8Tests.test_condL_56a
#print axioms P8Tests.test_not_condL_22
#print axioms P8Tests.test_condZ_56a
#print axioms P8Tests.test_condL_56b
#print axioms P8Tests.test_condZ_56b
#print axioms P8Tests.test_condL_56c
#print axioms P8Tests.test_condZ_56c
#print axioms P8Tests.test_condZ_s00
#print axioms P8Tests.test_not_condZ_00
#print axioms P8Tests.test_not_condZ_2
#print axioms P8Tests.test_failsAtOrbit_sL3
#print axioms P8Tests.test_not_failsAtOrbit_sL3
#print axioms P8Tests.test_failsAtPair_sL3
#print axioms P8Tests.test_not_failsAtPair_56c
#print axioms P8Tests.test_leafRow_56c
#print axioms P8Tests.test_leafRow_sL3
#print axioms P8Tests.test_not_leafRow_sL3
#print axioms P8Tests.test_not_leafRow_56a
#print axioms P8Tests.test_bareRow_sB
#print axioms P8Tests.test_not_bareRow_sB
#print axioms P8Tests.test_not_bareRow_56b

-- `Research.Backfill.Paper8.Proof.Tests.Spectral`
#print axioms P8Tests.test_small_trees
#print axioms P8Tests.test_allMain_K1
#print axioms P8Tests.test_not_allMain_K2
#print axioms P8Tests.test_allMain_s00
#print axioms P8Tests.test_not_allMain_00
#print axioms P8Tests.test_QAdj_sqrt2
#print axioms P8Tests.test_QAdj_3_9
#print axioms P8Tests.test_QAdj_pair_3000
#print axioms P8Tests.test_isTree_200
#print axioms P8Tests.test_ediam_200
#print axioms P8Tests.test_ediam_3
