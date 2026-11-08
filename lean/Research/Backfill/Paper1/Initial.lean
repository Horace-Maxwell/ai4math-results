import Research.Backfill.Paper1.Challenge
import Research.ICGGeneralThm5
import Research.ICGEqualParityBCol

/-! Exact checks against the independently reviewed Paper 1 v2 contract.
This is a first subset, not a claim of complete Paper 1 formalization. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1

theorem check_Lemma10 : Challenge.Lemma10 := by
  intro P μ hP h0 h1 A B
  exact ICGGeneral.hcell_le h0 h1 hP A B

theorem check_Lemma27 : Challenge.Lemma27 := by
  intro R P h
  have hh : ICGEqualParityB.PQok R P := h
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [ICGEqualParityB.poly_I1 hh]
  · nlinarith only [ICGEqualParityB.poly_I2 hh]
  · nlinarith only [ICGEqualParityB.poly_I3 hh]
  · nlinarith only [ICGEqualParityB.poly_I4 hh]
  · nlinarith only [ICGEqualParityB.poly_I5b hh]
  · intro _
    nlinarith only [ICGEqualParityB.poly_I5 hh]
  · nlinarith only [ICGEqualParityB.poly_I6 hh]
  · nlinarith only [ICGEqualParityB.poly_I7 hh]

#print axioms check_Lemma10
#print axioms check_Lemma27
end CodexPaper1
