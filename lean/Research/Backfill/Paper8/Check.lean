import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Lin.Main
import Research.Backfill.Paper8.Proof.Main.Main
import Research.Backfill.Paper8.Proof.Orb.Main
import Research.Backfill.Paper8.Proof.Real.Main
import Research.Backfill.Paper8.Proof.Region.Main
import Research.Backfill.Paper8.Proof.Rows.Main
import Research.Backfill.Paper8.Proof.Small.Main
import Research.Backfill.Paper8.Proof.Spec.Main
import Research.Backfill.Paper8.Proof.Tree.Main

/-!
# Paper 8, version 2: the 38 statements of the frozen statement file are proved

Frozen statement file `Research/Backfill/Paper8/Challenge.lean`, SHA-256
`69332eca957449e7613a6c95fa6bda906ecb2fbf688e0dc6ae4bba59fedec715`.
Every theorem below has as its type exactly one frozen `def … : Prop` of that file. The proofs are
in `Research/Backfill/Paper8/Proof/`. Most use other frozen statements through the modules that
prove them; the proofs of `Lemma_4_2`, `Lemma_4_3`, `Cor_4_4`, `Prop_5_1`, `Lemma_5_2`, `Prop_5_3`, `Theorem1`, `Theorem1_mathlib`, `Theorem1_signed` take other
frozen statements as explicit hypotheses, which are supplied here from their check theorems.
Proofs written by Claude Code agents, 29 September 2026.
-/

set_option autoImplicit false

namespace BackfillPaper8.Check

open BackfillPaper8

theorem check_Lemma_2_1 : Challenge.Lemma_2_1 := P8Lin.check_Lemma_2_1
theorem check_Lemma_2_1_good : Challenge.Lemma_2_1_good := P8Lin.check_Lemma_2_1_good
theorem check_Lemma_2_2 : Challenge.Lemma_2_2 := P8Lin.check_Lemma_2_2
theorem check_Secular_monic : Challenge.Secular_monic := P8Spec.check_Secular_monic
theorem check_TreeStructure : Challenge.TreeStructure := P8Tree.check_TreeStructure
theorem check_Lemma_3_1_i : Challenge.Lemma_3_1_i := P8Spec.check_Lemma_3_1_i
theorem check_Lemma_3_1_ii : Challenge.Lemma_3_1_ii := P8Spec.check_Lemma_3_1_ii
theorem check_Lemma_3_1_iii : Challenge.Lemma_3_1_iii := P8Spec.check_Lemma_3_1_iii
theorem check_Lemma_3_1_iv : Challenge.Lemma_3_1_iv := P8Spec.check_Lemma_3_1_iv
theorem check_Lemma_3_2 : Challenge.Lemma_3_2 := P8Main.check_Lemma_3_2
theorem check_Lemma_3_3_a : Challenge.Lemma_3_3_a := P8Orb.check_Lemma_3_3_a
theorem check_Lemma_3_3_b : Challenge.Lemma_3_3_b := P8Orb.check_Lemma_3_3_b
theorem check_Lemma_3_3_c : Challenge.Lemma_3_3_c := P8Orb.check_Lemma_3_3_c
theorem check_Lemma_3_3_d : Challenge.Lemma_3_3_d := P8Orb.check_Lemma_3_3_d
theorem check_Lemma_3_3_e : Challenge.Lemma_3_3_e := P8Orb.check_Lemma_3_3_e
theorem check_Lemma_3_4 : Challenge.Lemma_3_4 := P8Orb.check_Lemma_3_4
theorem check_StdLeafSums : Challenge.StdLeafSums := P8Real.check_StdLeafSums
theorem check_Lemma_4_1 : Challenge.Lemma_4_1 := P8Real.check_Lemma_4_1
theorem check_Lemma_4_2 : Challenge.Lemma_4_2 := P8Rows.check_Lemma_4_2 check_Lemma_3_3_a check_Lemma_3_3_b check_Lemma_3_3_e
theorem check_Lemma_4_3 : Challenge.Lemma_4_3 := P8Rows.check_Lemma_4_3 check_Lemma_3_3_a check_Lemma_3_3_b check_Lemma_3_3_e
theorem check_Cor_4_4 : Challenge.Cor_4_4 := P8Rows.check_Cor_4_4 check_Lemma_3_3_a check_Lemma_3_3_b check_Lemma_3_3_e
theorem check_Prop_5_1 : Challenge.Prop_5_1 := P8Small.check_Prop_5_1 check_Lemma_3_2
theorem check_Lemma_5_2 : Challenge.Lemma_5_2 := P8Real.check_Lemma_5_2 check_Lemma_3_1_i check_Lemma_3_3_b check_Lemma_3_3_d
theorem check_Prop_5_3 : Challenge.Prop_5_3 := P8Real.check_Prop_5_3 check_Lemma_3_1_i check_Lemma_3_3_b check_Lemma_3_3_d check_Cor_4_4
theorem check_Lemma_5_4 : Challenge.Lemma_5_4 := P8Region.check_Lemma_5_4
theorem check_Prop_5_5 : Challenge.Prop_5_5 := P8Region.check_Prop_5_5
theorem check_Prop_5_6 : Challenge.Prop_5_6 := P8Main.check_Prop_5_6
theorem check_Theorem1 : Challenge.Theorem1 := P8Tree.check_Theorem1 check_Lemma_2_1_good check_Prop_5_3 check_Cor_4_4 check_Lemma_5_4 check_Prop_5_5
theorem check_Theorem1_mathlib : Challenge.Theorem1_mathlib := P8Tree.check_Theorem1_mathlib check_Lemma_2_1_good check_Prop_5_3 check_Cor_4_4 check_Lemma_5_4 check_Prop_5_5
theorem check_Remark_8_3 : Challenge.Remark_8_3 := P8Lin.check_Remark_8_3
theorem check_GoodNeg : Challenge.GoodNeg := P8Lin.check_GoodNeg
theorem check_DiamRadius : Challenge.DiamRadius := P8Tree.check_DiamRadius
theorem check_Theorem1_signed : Challenge.Theorem1_signed := P8Tree.check_Theorem1_signed check_Lemma_2_1_good check_Prop_5_3 check_Cor_4_4 check_Lemma_5_4 check_Prop_5_5
theorem check_Lemma_U1 : Challenge.Lemma_U1 := P8Spec.check_Lemma_U1
theorem check_Lemma_3_2_pointwise : Challenge.Lemma_3_2_pointwise := P8Main.check_Lemma_3_2_pointwise
theorem check_Sharp_T15 : Challenge.Sharp_T15 := P8Rows.check_Sharp_T15
theorem check_Sharp_T18 : Challenge.Sharp_T18 := P8Rows.check_Sharp_T18
theorem check_Remark_8_2 : Challenge.Remark_8_2 := P8Lin.check_Remark_8_2

#print axioms check_Lemma_2_1
#print axioms check_Lemma_2_1_good
#print axioms check_Lemma_2_2
#print axioms check_Secular_monic
#print axioms check_TreeStructure
#print axioms check_Lemma_3_1_i
#print axioms check_Lemma_3_1_ii
#print axioms check_Lemma_3_1_iii
#print axioms check_Lemma_3_1_iv
#print axioms check_Lemma_3_2
#print axioms check_Lemma_3_3_a
#print axioms check_Lemma_3_3_b
#print axioms check_Lemma_3_3_c
#print axioms check_Lemma_3_3_d
#print axioms check_Lemma_3_3_e
#print axioms check_Lemma_3_4
#print axioms check_StdLeafSums
#print axioms check_Lemma_4_1
#print axioms check_Lemma_4_2
#print axioms check_Lemma_4_3
#print axioms check_Cor_4_4
#print axioms check_Prop_5_1
#print axioms check_Lemma_5_2
#print axioms check_Prop_5_3
#print axioms check_Lemma_5_4
#print axioms check_Prop_5_5
#print axioms check_Prop_5_6
#print axioms check_Theorem1
#print axioms check_Theorem1_mathlib
#print axioms check_Remark_8_3
#print axioms check_GoodNeg
#print axioms check_DiamRadius
#print axioms check_Theorem1_signed
#print axioms check_Lemma_U1
#print axioms check_Lemma_3_2_pointwise
#print axioms check_Sharp_T15
#print axioms check_Sharp_T18
#print axioms check_Remark_8_2

end BackfillPaper8.Check
