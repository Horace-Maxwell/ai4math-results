import Research.Backfill.Paper4.Proof.SmallMedianClassification
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationLayers
import Research.Backfill.Paper4.Proof.MedianMetricTransport
import Research.Backfill.Paper4.Proof.ReductionBasics

/-! Complete frozen minimality statements for Theorems A and B.
The same finite representative classification is transported to every finite vertex type.
Compilation and formal acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4 TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

namespace SmallMedianMinimality

/-- Connectedness within IsMedian supplies the positive cardinality used by the enumeration.
The conclusion keeps all three weak questions, including their singleton cases. -/
theorem small_median_questions (V : Type) [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 7) (hm : Challenge.IsMedian G) :
    Challenge.Question3' G ∧ Challenge.Question4 G ∧ Challenge.Question4' G := by
  have hn : 1 ≤ Fintype.card V :=
    Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr hm.1.nonempty)
  have ht : G.CliqueFree 3 := check_Sec4_median_triangleFree V G hm
  have hcoverage : Covers (reps (Fintype.card V)) :=
    covers_through_seven repCount reps (covers_one (reps 1) 0)
      TriangleFreeEnumerationLayers.layers (Fintype.card V) hn hcard
  obtain ⟨i, ⟨e⟩⟩ := hcoverage V G rfl hm.1 ht
  rcases SmallMedianClassification.all_small (Fintype.card V) hn hcard i with hnot | hq
  · exact (hnot ((MedianMetricTransport.isMedian_iff e).mp hm)).elim
  · have h3 : Challenge.Question3' G :=
      (MedianMetricTransport.question3'_iff e hm.1).mpr hq.1
    have h4 : Challenge.Question4 G :=
      (MedianMetricTransport.question4_iff e hm.1).mpr hq.2
    exact ⟨h3, h4, check_Sec2_Q4_imp_Q4' V G hm.1 h4⟩

end SmallMedianMinimality

theorem check_TheoremA_min : Challenge.TheoremA_min := by
  intro V _ G hcard hm
  exact (SmallMedianMinimality.small_median_questions V G hcard hm).1

theorem check_TheoremB_min : Challenge.TheoremB_min := by
  intro V _ G hcard hm
  exact (SmallMedianMinimality.small_median_questions V G hcard hm).2

#print axioms check_TheoremA_min
#print axioms check_TheoremB_min

end CodexPaper4
