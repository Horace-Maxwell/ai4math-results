import Research.Backfill.Paper7.CandidateRootCoverage
import Research.Backfill.Paper7.PrunedFactorizationCoverage
import Research.Backfill.Paper7.ResidualTableRejection

/-! PENDING IMPORT: CandidateRootCoverage has not been generated or proved.
Its required theorem is Paper7CycleThreeCertificate.rootnode_empty, with the
exact type prunedRootCheck candidateRows [] 8 (-9) = true. No local substitute
for that proof is supplied. This wrapper is blocked until full G1A is checked. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open BackfillPaper7.Challenge
open Paper7CycleThreeCertificate
open scoped BigOperators

theorem triangle_low_degree_exclusion : TriangleLowDegreeExclusion := by
  intro p q hpos hn hq2
  have hp : 0 < (p 0 + q 0) + (p 1 + q 1) + (p 2 + q 2) := by
    simpa only [Fin.sum_univ_three] using hpos
  have hbudget : 3 + (p 0 + p 1 + p 2) + 2 * (q 0 + q 1 + q 2) ≤ 49 := by
    simpa only [nOf, Fin.sum_univ_three] using hn
  refine ⟨?_, ?_, ?_⟩
  · intro hq1 hF
    have hsmall : 3 + p 0 + p 1 + p 2 + 2 * q 0 ≤ 49 := by omega
    have hpositive : 0 < p 0 + p 1 + p 2 + q 0 := by omega
    obtain ⟨a, ha, hpoly⟩ := checked_pruned_table_covers_factorization
      candidateRows rootnode_empty _ hF (triangle_oneQ_residual_data p q hq1 hq2).2.1
      (oneQ_certificate_pattern p (q 0) hsmall)
    exact oneQ_reject_candidate_row p (q 0) hpositive a ha hpoly
  · intro hp0 hF
    have hsmall : 3 + p 1 + p 2 + 2 * (q 0 + q 1) ≤ 49 := by omega
    have hpositive : 0 < p 1 + p 2 + q 0 + q 1 := by omega
    obtain ⟨a, ha, hpoly⟩ := checked_pruned_table_covers_factorization
      candidateRows rootnode_empty _ hF (triangle_offZero_residual_data p q hp0 hq2).2.1
      (offZero_certificate_pattern (p 1) (p 2) (q 0) (q 1) hsmall)
    exact offZero_reject_candidate_row (p 1) (p 2) (q 0) (q 1) hpositive a ha hpoly
  · intro hp2 hF
    have hsmall : 3 + p 0 + p 1 + 2 * (q 0 + q 1) ≤ 49 := by omega
    have hpositive : 0 < p 0 + p 1 + q 0 + q 1 := by omega
    obtain ⟨a, ha, hpoly⟩ := checked_pruned_table_covers_factorization
      candidateRows rootnode_empty _ hF (triangle_atZero_residual_data p q hp2 hq2).2.1
      (atZero_certificate_pattern (p 0) (p 1) (q 0) (q 1) hsmall)
    exact atZero_reject_candidate_row (p 0) (p 1) (q 0) (q 1) hpositive a ha hpoly
#print axioms Paper7CycleThree.triangle_low_degree_exclusion

theorem check_Section6CycleThree : BackfillPaper7.Challenge.Section6CycleThree := by
  exact section6_cycle_three_iff_low_degree_exclusion.mpr triangle_low_degree_exclusion
#print axioms Paper7CycleThree.check_Section6CycleThree

end Paper7CycleThree
