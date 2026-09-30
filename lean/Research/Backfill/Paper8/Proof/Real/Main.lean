import Research.Backfill.Paper8.Proof.Real.StdLeaf
import Research.Backfill.Paper8.Proof.Real.Lset
import Research.Backfill.Paper8.Proof.Real.Count
import Research.Backfill.Paper8.Proof.Real.Large

/-!
# Paper 8, agent `real`: final checks

`StdLeafSums` (module `Research.Backfill.Paper8.Proof.Real.StdLeaf`) and Lemma 4.1 (module `Research.Backfill.Paper8.Proof.Real.Lset`) without
hypotheses; Lemma 5.2 (module `Research.Backfill.Paper8.Proof.Real.Count`) from Lemmas 3.1(i), 3.3(b), 3.3(d); Proposition 5.3
(module `Research.Backfill.Paper8.Proof.Real.Large`) from Lemmas 3.1(i), 3.3(b), 3.3(d) and Corollary 4.4.
-/

set_option autoImplicit false

namespace P8Real

theorem check_StdLeafSums : BackfillPaper8.Challenge.StdLeafSums := stdLeafSums

#print axioms check_StdLeafSums

theorem check_Lemma_4_1 : BackfillPaper8.Challenge.Lemma_4_1 := lemma_4_1

#print axioms check_Lemma_4_1

theorem check_Lemma_5_2 (h31 : BackfillPaper8.Challenge.Lemma_3_1_i)
    (h33b : BackfillPaper8.Challenge.Lemma_3_3_b) (h33d : BackfillPaper8.Challenge.Lemma_3_3_d) :
    BackfillPaper8.Challenge.Lemma_5_2 :=
  lemma_5_2 h31 h33b h33d

#print axioms check_Lemma_5_2

theorem check_Prop_5_3 (h31 : BackfillPaper8.Challenge.Lemma_3_1_i)
    (h33b : BackfillPaper8.Challenge.Lemma_3_3_b) (h33d : BackfillPaper8.Challenge.Lemma_3_3_d)
    (h44 : BackfillPaper8.Challenge.Cor_4_4) : BackfillPaper8.Challenge.Prop_5_3 :=
  prop_5_3 h31 h33b h33d h44

#print axioms check_Prop_5_3

end P8Real
