import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Lin.Switch
import Research.Backfill.Paper8.Proof.Lin.Krylov
import Research.Backfill.Paper8.Proof.Lin.Bipartite

/-!
# Paper 8 back-fill (agent `lin`): deliverables

`check_Lemma_2_1`, `check_Lemma_2_1_good`, `check_GoodNeg` and `check_Remark_8_3` come from
`Research.Backfill.Paper8.Proof.Lin.Switch`, `check_Lemma_2_2` from `Research.Backfill.Paper8.Proof.Lin.Krylov` (with `Research.Backfill.Paper8.Proof.Lin.Spectral` and
`Research.Backfill.Paper8.Proof.Lin.BaseChange`), `check_Remark_8_2` from `Research.Backfill.Paper8.Proof.Lin.Bipartite` (statement file version 2).
No other statement of the challenge is used as a hypothesis.
-/

set_option autoImplicit false

namespace P8Lin

theorem check_Lemma_2_1 : BackfillPaper8.Challenge.Lemma_2_1 := lemma_2_1
#print axioms check_Lemma_2_1

theorem check_Lemma_2_1_good : BackfillPaper8.Challenge.Lemma_2_1_good := lemma_2_1_good
#print axioms check_Lemma_2_1_good

theorem check_GoodNeg : BackfillPaper8.Challenge.GoodNeg := goodNeg_body
#print axioms check_GoodNeg

theorem check_Remark_8_3 : BackfillPaper8.Challenge.Remark_8_3 := remark_8_3
#print axioms check_Remark_8_3

theorem check_Lemma_2_2 : BackfillPaper8.Challenge.Lemma_2_2 := lemma_2_2
#print axioms check_Lemma_2_2

theorem check_Remark_8_2 : BackfillPaper8.Challenge.Remark_8_2 := remark_8_2_body
#print axioms check_Remark_8_2

end P8Lin
