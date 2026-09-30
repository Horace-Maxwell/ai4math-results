import Research.Backfill.Paper8.Proof.Tree.Signed

/-!
# Paper 8, agent `tree`: deliverables

`check_TreeStructure` and `check_DiamRadius` (no hypotheses); `check_Theorem1`,
`check_Theorem1_mathlib` and `check_Theorem1_signed` from `Lemma_2_1_good`, `Prop_5_3`,
`Cor_4_4`, `Lemma_5_4` and `Prop_5_5`. Proposition 5.6 is `P8Main.check_Prop_5_6` and
Proposition 5.1 is `P8Small.check_Prop_5_1 P8Main.check_Lemma_3_2` (imported modules of agents
`main` and `small`, no hypotheses).
-/

set_option autoImplicit false

namespace P8Tree

theorem check_TreeStructure : BackfillPaper8.Challenge.TreeStructure :=
  treeStructure

#print axioms check_TreeStructure

theorem check_DiamRadius : BackfillPaper8.Challenge.DiamRadius :=
  diamRadius

#print axioms check_DiamRadius

theorem check_Theorem1 (h21 : BackfillPaper8.Challenge.Lemma_2_1_good)
    (h53 : BackfillPaper8.Challenge.Prop_5_3) (h44 : BackfillPaper8.Challenge.Cor_4_4)
    (h54 : BackfillPaper8.Challenge.Lemma_5_4) (h55 : BackfillPaper8.Challenge.Prop_5_5) : BackfillPaper8.Challenge.Theorem1 :=
  theorem1 h21 h53 h44 h54 h55

#print axioms check_Theorem1

theorem check_Theorem1_mathlib (h21 : BackfillPaper8.Challenge.Lemma_2_1_good)
    (h53 : BackfillPaper8.Challenge.Prop_5_3) (h44 : BackfillPaper8.Challenge.Cor_4_4)
    (h54 : BackfillPaper8.Challenge.Lemma_5_4) (h55 : BackfillPaper8.Challenge.Prop_5_5) : BackfillPaper8.Challenge.Theorem1_mathlib :=
  theorem1_mathlib_of (theorem1 h21 h53 h44 h54 h55)

#print axioms check_Theorem1_mathlib

theorem check_Theorem1_signed (h21 : BackfillPaper8.Challenge.Lemma_2_1_good)
    (h53 : BackfillPaper8.Challenge.Prop_5_3) (h44 : BackfillPaper8.Challenge.Cor_4_4)
    (h54 : BackfillPaper8.Challenge.Lemma_5_4) (h55 : BackfillPaper8.Challenge.Prop_5_5) : BackfillPaper8.Challenge.Theorem1_signed :=
  theorem1_signed h21 h53 h44 h54 h55

#print axioms check_Theorem1_signed

end P8Tree
