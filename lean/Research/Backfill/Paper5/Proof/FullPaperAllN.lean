import Research.Backfill.Paper5.Proof.MainC
import Research.Backfill.Paper5.Supplement.FullPaperStatement

set_option autoImplicit false

namespace CodexPaper5.FullPaperAllN

open BackfillPaper5

theorem check_AllNClassification : FullPaperStatement.AllNClassification := by
  intro n
  have hB : Challenge.SubsetHasCM Challenge.dmul (Challenge.B n) ↔
      Challenge.HasCM (Challenge.Sym n) :=
    MainC.diagram_subsetHasCM_iff_sym Challenge.Fam.B n
  have hPB : Challenge.SubsetHasCM Challenge.dmul (Challenge.PB n) ↔
      Challenge.HasCM (Challenge.Sym n) :=
    MainC.diagram_subsetHasCM_iff_sym Challenge.Fam.PB n
  exact ⟨hB.trans hPB.symm, hPB, CodexPaper5.check_SymCM n⟩

end CodexPaper5.FullPaperAllN

#print axioms CodexPaper5.FullPaperAllN.check_AllNClassification
