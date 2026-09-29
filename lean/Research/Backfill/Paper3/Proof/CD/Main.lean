import Research.Backfill.Paper3.Proof.CD.PropC
import Research.Backfill.Paper3.Proof.CD.ThmD
import Research.Backfill.Paper3.Proof.CD.Remark10
import Research.Backfill.Paper3.Proof.CD.Remark10c

/-!
# Proposition C, Theorem D, Remarks 9, 10(a), 10(c), 11 and reading R6

Each statement `X` below is proved as `check_X`. The frozen statements `SSSZBound`, `Lemma8`,
`Lemma6`, `Lemma7`, `TheoremBprime` and `QuestionTrueZero`, proved in other modules, enter as
explicit hypotheses; they are supplied in `Check.lean`.
-/

set_option autoImplicit false

namespace P3CD

open BackfillPaper3.Challenge

theorem check_Rho_bddBelow : Rho_bddBelow := rho_bddBelow

#print axioms check_Rho_bddBelow

theorem check_Remark9 : Remark9 := remark9

#print axioms check_Remark9

theorem check_PropositionC (hS : SSSZBound) (h8 : Lemma8) : PropositionC := propositionC hS h8

#print axioms check_PropositionC

theorem check_TheoremD (hB : TheoremBprime) (h8 : Lemma8) (h6 : Lemma6) (h7 : Lemma7) :
    TheoremD :=
  theoremD hB h8 h6 h7

#print axioms check_TheoremD

theorem check_Remark10a : Remark10a := remark10a

#print axioms check_Remark10a

theorem check_Remark10c (h6 : Lemma6) : Remark10c := remark10c h6

#print axioms check_Remark10c

theorem check_Remark11 (h8 : Lemma8) (h6 : Lemma6) (h7 : Lemma7) : Remark11 := remark11 h8 h6 h7

#print axioms check_Remark11

theorem check_ReadingR6 (hQ : QuestionTrueZero) : ReadingR6 := readingR6 hQ

#print axioms check_ReadingR6

end P3CD
