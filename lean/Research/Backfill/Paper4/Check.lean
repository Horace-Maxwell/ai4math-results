import Research.Backfill.Paper4.Challenge
import Research.Backfill.Paper4.Proof.BasicCorollaries
import Research.Backfill.Paper4.Proof.ConcreteCore
import Research.Backfill.Paper4.Proof.ConcreteRemarks
import Research.Backfill.Paper4.Proof.DHExtension
import Research.Backfill.Paper4.Proof.DHFourPoint
import Research.Backfill.Paper4.Proof.DHFourPointConsequences
import Research.Backfill.Paper4.Proof.F1DistanceHereditary
import Research.Backfill.Paper4.Proof.Foundation
import Research.Backfill.Paper4.Proof.FourPointConsequences
import Research.Backfill.Paper4.Proof.G2DistanceHereditary
import Research.Backfill.Paper4.Proof.GraphAutomorphisms
import Research.Backfill.Paper4.Proof.GridExamples
import Research.Backfill.Paper4.Proof.GridInterval
import Research.Backfill.Paper4.Proof.GridMonotone
import Research.Backfill.Paper4.Proof.H11AssemblyDraft
import Research.Backfill.Paper4.Proof.HKOFig2Remark
import Research.Backfill.Paper4.Proof.MedianEight
import Research.Backfill.Paper4.Proof.MedianEightLabelled
import Research.Backfill.Paper4.Proof.MetricBounds
import Research.Backfill.Paper4.Proof.NonDHExamples
import Research.Backfill.Paper4.Proof.Readings
import Research.Backfill.Paper4.Proof.Reduction
import Research.Backfill.Paper4.Proof.ReductionBasics
import Research.Backfill.Paper4.Proof.SmallMedianCounts
import Research.Backfill.Paper4.Proof.SmallMedianMinimality
import Research.Backfill.Paper4.Proof.TheoremCFP
import Research.Backfill.Paper4.Proof.TriangleFreeCandidates
import Research.Backfill.Paper4.Proof.TriangleFreeClassification

/-!
# Paper 4: every frozen statement is proved

Frozen statement file `Research/Backfill/Paper4/Challenge.lean`, version 2, SHA-256
`9f1b0c95f35addf03f54c330ea0cd63324154d17e1cc8e707c8bf830da4a0785`. Each theorem below has as
its type exactly one frozen `def … : Prop` of that file. The proofs of 46 statements were written
by OpenAI Codex; those of `TheoremA_unique`, `TheoremB_unique`, `Sec4_count_median` and
`Sec4_count_labelled` by Claude (Anthropic) while Codex was out of quota.
-/

set_option autoImplicit false

namespace BackfillPaper4.Check

theorem check_Sec5_FP_symm : BackfillPaper4.Challenge.Sec5_FP_symm :=
  CodexPaper4.check_Sec5_FP_symm

theorem check_Sec5_FP_iff_viii : BackfillPaper4.Challenge.Sec5_FP_iff_viii :=
  CodexPaper4.check_Sec5_FP_iff_viii

theorem check_Lemma2 : BackfillPaper4.Challenge.Lemma2 :=
  CodexPaper4.check_Lemma2

theorem check_Sec2_bounds : BackfillPaper4.Challenge.Sec2_bounds :=
  CodexPaper4.check_Sec2_bounds

theorem check_Proposition3 : BackfillPaper4.Challenge.Proposition3 :=
  CodexPaper4.check_Proposition3

theorem check_Sec2_peripheral_iff : BackfillPaper4.Challenge.Sec2_peripheral_iff :=
  CodexPaper4.check_Sec2_peripheral_iff

theorem check_Sec2_Q3_imp_Q3' : BackfillPaper4.Challenge.Sec2_Q3_imp_Q3' :=
  CodexPaper4.check_Sec2_Q3_imp_Q3'

theorem check_Sec2_Q4_imp_Q4' : BackfillPaper4.Challenge.Sec2_Q4_imp_Q4' :=
  CodexPaper4.check_Sec2_Q4_imp_Q4'

theorem check_Sec2_repeated : BackfillPaper4.Challenge.Sec2_repeated :=
  CodexPaper4.check_Sec2_repeated

theorem check_Sec2_readings_Q3 : BackfillPaper4.Challenge.Sec2_readings_Q3 :=
  CodexPaper4.check_Sec2_readings_Q3

theorem check_Sec2_readings_Q4 : BackfillPaper4.Challenge.Sec2_readings_Q4 :=
  CodexPaper4.check_Sec2_readings_Q4

theorem check_TheoremC_FP : BackfillPaper4.Challenge.TheoremC_FP :=
  CodexPaper4.check_TheoremC_FP

theorem check_Sec4_median_triangleFree : BackfillPaper4.Challenge.Sec4_median_triangleFree :=
  CodexPaper4.check_Sec4_median_triangleFree

theorem check_Sec4_nonCutVertex : BackfillPaper4.Challenge.Sec4_nonCutVertex :=
  CodexPaper4.check_Sec4_nonCutVertex

theorem check_Sec4_reduction : BackfillPaper4.Challenge.Sec4_reduction :=
  CodexPaper4.check_Sec4_reduction

theorem check_TheoremA_i : BackfillPaper4.Challenge.TheoremA_i :=
  CodexPaper4.check_TheoremA_i

theorem check_TheoremA_ii : BackfillPaper4.Challenge.TheoremA_ii :=
  CodexPaper4.check_TheoremA_ii

theorem check_TheoremB_ii : BackfillPaper4.Challenge.TheoremB_ii :=
  CodexPaper4.check_TheoremB_ii

theorem check_Remark4_ii : BackfillPaper4.Challenge.Remark4_ii :=
  CodexPaper4.check_Remark4_ii

theorem check_Sec8_open : BackfillPaper4.Challenge.Sec8_open :=
  CodexPaper4.check_Sec8_open

theorem check_Sec2_problem2_altReading : BackfillPaper4.Challenge.Sec2_problem2_altReading :=
  CodexPaper4.check_Sec2_problem2_altReading

theorem check_Remark4_iii : BackfillPaper4.Challenge.Remark4_iii :=
  CodexPaper4.check_Remark4_iii

theorem check_Remark5_i : BackfillPaper4.Challenge.Remark5_i :=
  CodexPaper4.check_Remark5_i

theorem check_Released_fourPoint_facts : BackfillPaper4.Challenge.Released_fourPoint_facts :=
  CodexPaper4.check_Released_fourPoint_facts

theorem check_TheoremB_i : BackfillPaper4.Challenge.TheoremB_i :=
  CodexPaper4.check_TheoremB_i

theorem check_Sec3_medianDH_noQ4 : BackfillPaper4.Challenge.Sec3_medianDH_noQ4 :=
  CodexPaper4.check_Sec3_medianDH_noQ4

theorem check_Remark4_i : BackfillPaper4.Challenge.Remark4_i :=
  CodexPaper4.check_Remark4_i

theorem check_Sec2_classReading : BackfillPaper4.Challenge.Sec2_classReading :=
  CodexPaper4.check_Sec2_classReading

theorem check_Sec3_MO_notDH : BackfillPaper4.Challenge.Sec3_MO_notDH :=
  CodexPaper4.check_Sec3_MO_notDH

theorem check_Remark5_ii : BackfillPaper4.Challenge.Remark5_ii :=
  CodexPaper4.check_Remark5_ii

theorem check_Remark5_iii : BackfillPaper4.Challenge.Remark5_iii :=
  CodexPaper4.check_Remark5_iii

theorem check_Sec6_DHtests : BackfillPaper4.Challenge.Sec6_DHtests :=
  CodexPaper4.check_Sec6_DHtests

theorem check_Lemma1 : BackfillPaper4.Challenge.Lemma1 :=
  CodexPaper4.check_Lemma1

theorem check_TheoremA_grid : BackfillPaper4.Challenge.TheoremA_grid :=
  CodexPaper4.check_TheoremA_grid

theorem check_TheoremB_grid : BackfillPaper4.Challenge.TheoremB_grid :=
  CodexPaper4.check_TheoremB_grid

theorem check_Sec3_monotonePath : BackfillPaper4.Challenge.Sec3_monotonePath :=
  CodexPaper4.check_Sec3_monotonePath

theorem check_BandeltMulder_extension : BackfillPaper4.Challenge.BandeltMulder_extension :=
  CodexPaper4.check_BandeltMulder_extension

theorem check_BandeltMulder_DH_fourPoint : BackfillPaper4.Challenge.BandeltMulder_DH_fourPoint :=
  CodexPaper4.check_BandeltMulder_DH_fourPoint

theorem check_TheoremC_i : BackfillPaper4.Challenge.TheoremC_i :=
  CodexPaper4.check_TheoremC_i

theorem check_TheoremC_ii : BackfillPaper4.Challenge.TheoremC_ii :=
  CodexPaper4.check_TheoremC_ii

theorem check_Sec3_DH_noQ4_imp_Q3 : BackfillPaper4.Challenge.Sec3_DH_noQ4_imp_Q3 :=
  CodexPaper4.check_Sec3_DH_noQ4_imp_Q3

theorem check_Sec4_aut : BackfillPaper4.Challenge.Sec4_aut :=
  CodexPaper4.check_Sec4_aut

theorem check_Sec4_count_triangleFree7 : BackfillPaper4.Challenge.Sec4_count_triangleFree7 :=
  CodexPaper4.check_Sec4_count_triangleFree7

theorem check_Sec4_count_candidates : BackfillPaper4.Challenge.Sec4_count_candidates :=
  CodexPaper4.check_Sec4_count_candidates

theorem check_TheoremA_min : BackfillPaper4.Challenge.TheoremA_min :=
  CodexPaper4.check_TheoremA_min

theorem check_TheoremB_min : BackfillPaper4.Challenge.TheoremB_min :=
  CodexPaper4.check_TheoremB_min

theorem check_TheoremA_unique : BackfillPaper4.Challenge.TheoremA_unique :=
  ClaudePaper4.check_TheoremA_unique

theorem check_TheoremB_unique : BackfillPaper4.Challenge.TheoremB_unique :=
  ClaudePaper4.check_TheoremB_unique

theorem check_Sec4_count_median : BackfillPaper4.Challenge.Sec4_count_median :=
  ClaudePaper4.check_Sec4_count_median

theorem check_Sec4_count_labelled : BackfillPaper4.Challenge.Sec4_count_labelled :=
  ClaudePaper4.check_Sec4_count_labelled

#print axioms check_Sec5_FP_symm
#print axioms check_Sec5_FP_iff_viii
#print axioms check_Lemma2
#print axioms check_Sec2_bounds
#print axioms check_Proposition3
#print axioms check_Sec2_peripheral_iff
#print axioms check_Sec2_Q3_imp_Q3'
#print axioms check_Sec2_Q4_imp_Q4'
#print axioms check_Sec2_repeated
#print axioms check_Sec2_readings_Q3
#print axioms check_Sec2_readings_Q4
#print axioms check_TheoremC_FP
#print axioms check_Sec4_median_triangleFree
#print axioms check_Sec4_nonCutVertex
#print axioms check_Sec4_reduction
#print axioms check_TheoremA_i
#print axioms check_TheoremA_ii
#print axioms check_TheoremB_ii
#print axioms check_Remark4_ii
#print axioms check_Sec8_open
#print axioms check_Sec2_problem2_altReading
#print axioms check_Remark4_iii
#print axioms check_Remark5_i
#print axioms check_Released_fourPoint_facts
#print axioms check_TheoremB_i
#print axioms check_Sec3_medianDH_noQ4
#print axioms check_Remark4_i
#print axioms check_Sec2_classReading
#print axioms check_Sec3_MO_notDH
#print axioms check_Remark5_ii
#print axioms check_Remark5_iii
#print axioms check_Sec6_DHtests
#print axioms check_Lemma1
#print axioms check_TheoremA_grid
#print axioms check_TheoremB_grid
#print axioms check_Sec3_monotonePath
#print axioms check_BandeltMulder_extension
#print axioms check_BandeltMulder_DH_fourPoint
#print axioms check_TheoremC_i
#print axioms check_TheoremC_ii
#print axioms check_Sec3_DH_noQ4_imp_Q3
#print axioms check_Sec4_aut
#print axioms check_Sec4_count_triangleFree7
#print axioms check_Sec4_count_candidates
#print axioms check_TheoremA_min
#print axioms check_TheoremB_min
#print axioms check_TheoremA_unique
#print axioms check_TheoremB_unique
#print axioms check_Sec4_count_median
#print axioms check_Sec4_count_labelled

end BackfillPaper4.Check
