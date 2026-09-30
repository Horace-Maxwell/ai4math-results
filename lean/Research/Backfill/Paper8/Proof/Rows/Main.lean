import Research.Backfill.Paper8.Proof.Rows.Lemmas
import Research.Backfill.Paper8.Proof.Rows.CorMain
import Research.Backfill.Paper8.Proof.Rows.Sharp
import Research.Backfill.Paper8.Proof.Real.Main
import Research.Backfill.Paper8.Proof.Main.Main

/-!
# Paper 8, agent `rows`: deliverables

Lemma 4.2 (leaf row), Lemma 4.3 (bare row) and Corollary 4.4 from Lemma 3.3(a), (b), (e) (taken
as hypotheses; agent `orb`), with `StdLeafSums` (`P8Real.check_StdLeafSums`) and Lemma 3.2
(`P8Main.check_Lemma_3_2`) used as proved. `Sharp_T15` and `Sharp_T18` (statement file,
version 2) by explicit computation, without hypotheses.
-/

set_option autoImplicit false

namespace P8Rows

theorem check_Lemma_4_2 (h3a : BackfillPaper8.Challenge.Lemma_3_3_a)
    (h3b : BackfillPaper8.Challenge.Lemma_3_3_b) (h3e : BackfillPaper8.Challenge.Lemma_3_3_e) :
    BackfillPaper8.Challenge.Lemma_4_2 :=
  lemma_4_2 P8Real.check_StdLeafSums h3a h3b h3e

#print axioms check_Lemma_4_2

theorem check_Lemma_4_3 (h3a : BackfillPaper8.Challenge.Lemma_3_3_a)
    (h3b : BackfillPaper8.Challenge.Lemma_3_3_b) (h3e : BackfillPaper8.Challenge.Lemma_3_3_e) :
    BackfillPaper8.Challenge.Lemma_4_3 :=
  lemma_4_3 P8Real.check_StdLeafSums h3a h3b h3e

#print axioms check_Lemma_4_3

theorem check_Cor_4_4 (h3a : BackfillPaper8.Challenge.Lemma_3_3_a)
    (h3b : BackfillPaper8.Challenge.Lemma_3_3_b) (h3e : BackfillPaper8.Challenge.Lemma_3_3_e) :
    BackfillPaper8.Challenge.Cor_4_4 :=
  cor_4_4 P8Real.check_StdLeafSums P8Main.check_Lemma_3_2 h3a h3b h3e

#print axioms check_Cor_4_4

theorem check_Sharp_T15 : BackfillPaper8.Challenge.Sharp_T15 :=
  sharp_T15 P8Real.check_StdLeafSums

#print axioms check_Sharp_T15

theorem check_Sharp_T18 : BackfillPaper8.Challenge.Sharp_T18 :=
  sharp_T18 P8Real.check_StdLeafSums

#print axioms check_Sharp_T18

end P8Rows
