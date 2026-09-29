import Research.Backfill.Paper4.Proof.TriangleFreeRepresentativeFingerprint
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationValidity
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationLayers

/-! Complete frozen seven-vertex ClassCount, assembled from actual graph representatives,
pairwise non-isomorphism, and coverage of every finite seven-vertex graph.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4 TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem check_Sec4_count_triangleFree7 : Challenge.Sec4_count_triangleFree7 := by
  refine ⟨reps 7, ?_, ?_, ?_⟩
  · exact TriangleFreeEnumerationValidity.representatives_valid 7 (by decide) (by decide)
  · intro i j h
    exact TriangleFreeRepresentativeFingerprint.representatives_pairwise i j h
  · intro W _ G hcard hG
    have hcovers : Covers (reps 7) :=
      covers_through_seven repCount reps (covers_one (reps 1) 0)
        TriangleFreeEnumerationLayers.layers 7 (by decide) (by decide)
    exact hcovers W G hcard hG.1 hG.2

#print axioms check_Sec4_count_triangleFree7

end CodexPaper4
