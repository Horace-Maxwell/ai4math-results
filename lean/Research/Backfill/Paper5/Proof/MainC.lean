import Research.Backfill.Paper5.Proof.DiagramCMSufficiency
import Research.Backfill.Paper5.Proof.DiagramCMNecessity
import Research.Backfill.Paper5.Proof.SymmetricClassification

set_option autoImplicit false

namespace CodexPaper5.MainC

open BackfillPaper5

/-- Both directions for the actual diagrams and actual diagram multiplication. -/
theorem diagram_subsetHasCM_iff_sym (D : Challenge.Fam) (n : ℕ) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Dset D n) ↔
      Challenge.HasCM (Challenge.Sym n) :=
  ⟨DiagramCMNecessity.subsetHasCM_implies_symHasCM D n,
    DiagramCMSufficiency.subsetHasCM_of_symHasCM D n⟩

theorem check_Thm11c : Challenge.Thm11c := by
  intro n hn
  have hB : Challenge.SubsetHasCM Challenge.dmul (Challenge.B n) ↔
      Challenge.HasCM (Challenge.Sym n) :=
    diagram_subsetHasCM_iff_sym Challenge.Fam.B n
  have hPB : Challenge.SubsetHasCM Challenge.dmul (Challenge.PB n) ↔
      Challenge.HasCM (Challenge.Sym n) :=
    diagram_subsetHasCM_iff_sym Challenge.Fam.PB n
  refine ⟨hB.trans hPB.symm, hPB, ?_⟩
  constructor
  · intro hgroup
    have hsmall : n ≠ 2 ∧ n ≠ 3 := (CodexPaper5.check_SymCM n).mp hgroup
    omega
  · intro hsize
    apply (CodexPaper5.check_SymCM n).mpr
    omega

#print axioms CodexPaper5.MainC.diagram_subsetHasCM_iff_sym
#print axioms CodexPaper5.MainC.check_Thm11c

end CodexPaper5.MainC
