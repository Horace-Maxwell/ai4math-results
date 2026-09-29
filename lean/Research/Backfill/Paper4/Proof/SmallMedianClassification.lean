import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock00
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock01
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock02
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock03
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock04
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock05
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock06
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock07
import Research.Backfill.Paper4.Proof.SmallMedianClassificationBlock08

/-! Exhaustive assembly for all90 actual representatives on one through seven vertices.
This statement has no median assumption and retains the negative classification branch.
It is not itself the frozen minimality theorem over arbitrary vertex types. -/
set_option autoImplicit false

namespace CodexPaper4.SmallMedianClassification
open BackfillPaper4 TriangleFreeEnumerationFamily

theorem all_small (n : ℕ) (hn : 1 ≤ n) (h7 : n ≤ 7) (i : Fin (repCount n)) :
    ¬ Challenge.IsMedian (reps n i) ∨
      (Challenge.Question3' (reps n i) ∧ Challenge.Question4 (reps n i)) := by
  interval_cases n
  · fin_cases i
    · exact SmallMedianClassificationBlock00.classify_1_00
  · fin_cases i
    · exact SmallMedianClassificationBlock00.classify_2_00
  · fin_cases i
    · exact SmallMedianClassificationBlock00.classify_3_00
  · fin_cases i
    · exact SmallMedianClassificationBlock00.classify_4_00
    · exact SmallMedianClassificationBlock00.classify_4_01
    · exact SmallMedianClassificationBlock00.classify_4_02
  · fin_cases i
    · exact SmallMedianClassificationBlock00.classify_5_00
    · exact SmallMedianClassificationBlock00.classify_5_01
    · exact SmallMedianClassificationBlock00.classify_5_02
    · exact SmallMedianClassificationBlock00.classify_5_03
    · exact SmallMedianClassificationBlock00.classify_5_04
    · exact SmallMedianClassificationBlock00.classify_5_05
  · fin_cases i
    · exact SmallMedianClassificationBlock01.classify_6_00
    · exact SmallMedianClassificationBlock01.classify_6_01
    · exact SmallMedianClassificationBlock01.classify_6_02
    · exact SmallMedianClassificationBlock01.classify_6_03
    · exact SmallMedianClassificationBlock01.classify_6_04
    · exact SmallMedianClassificationBlock01.classify_6_05
    · exact SmallMedianClassificationBlock01.classify_6_06
    · exact SmallMedianClassificationBlock01.classify_6_07
    · exact SmallMedianClassificationBlock01.classify_6_08
    · exact SmallMedianClassificationBlock01.classify_6_09
    · exact SmallMedianClassificationBlock02.classify_6_10
    · exact SmallMedianClassificationBlock02.classify_6_11
    · exact SmallMedianClassificationBlock02.classify_6_12
    · exact SmallMedianClassificationBlock02.classify_6_13
    · exact SmallMedianClassificationBlock02.classify_6_14
    · exact SmallMedianClassificationBlock02.classify_6_15
    · exact SmallMedianClassificationBlock02.classify_6_16
    · exact SmallMedianClassificationBlock02.classify_6_17
    · exact SmallMedianClassificationBlock02.classify_6_18
  · fin_cases i
    · exact SmallMedianClassificationBlock03.classify_7_00
    · exact SmallMedianClassificationBlock03.classify_7_01
    · exact SmallMedianClassificationBlock03.classify_7_02
    · exact SmallMedianClassificationBlock03.classify_7_03
    · exact SmallMedianClassificationBlock03.classify_7_04
    · exact SmallMedianClassificationBlock03.classify_7_05
    · exact SmallMedianClassificationBlock03.classify_7_06
    · exact SmallMedianClassificationBlock03.classify_7_07
    · exact SmallMedianClassificationBlock03.classify_7_08
    · exact SmallMedianClassificationBlock03.classify_7_09
    · exact SmallMedianClassificationBlock04.classify_7_10
    · exact SmallMedianClassificationBlock04.classify_7_11
    · exact SmallMedianClassificationBlock04.classify_7_12
    · exact SmallMedianClassificationBlock04.classify_7_13
    · exact SmallMedianClassificationBlock04.classify_7_14
    · exact SmallMedianClassificationBlock04.classify_7_15
    · exact SmallMedianClassificationBlock04.classify_7_16
    · exact SmallMedianClassificationBlock04.classify_7_17
    · exact SmallMedianClassificationBlock04.classify_7_18
    · exact SmallMedianClassificationBlock04.classify_7_19
    · exact SmallMedianClassificationBlock05.classify_7_20
    · exact SmallMedianClassificationBlock05.classify_7_21
    · exact SmallMedianClassificationBlock05.classify_7_22
    · exact SmallMedianClassificationBlock05.classify_7_23
    · exact SmallMedianClassificationBlock05.classify_7_24
    · exact SmallMedianClassificationBlock05.classify_7_25
    · exact SmallMedianClassificationBlock05.classify_7_26
    · exact SmallMedianClassificationBlock05.classify_7_27
    · exact SmallMedianClassificationBlock05.classify_7_28
    · exact SmallMedianClassificationBlock05.classify_7_29
    · exact SmallMedianClassificationBlock06.classify_7_30
    · exact SmallMedianClassificationBlock06.classify_7_31
    · exact SmallMedianClassificationBlock06.classify_7_32
    · exact SmallMedianClassificationBlock06.classify_7_33
    · exact SmallMedianClassificationBlock06.classify_7_34
    · exact SmallMedianClassificationBlock06.classify_7_35
    · exact SmallMedianClassificationBlock06.classify_7_36
    · exact SmallMedianClassificationBlock06.classify_7_37
    · exact SmallMedianClassificationBlock06.classify_7_38
    · exact SmallMedianClassificationBlock06.classify_7_39
    · exact SmallMedianClassificationBlock07.classify_7_40
    · exact SmallMedianClassificationBlock07.classify_7_41
    · exact SmallMedianClassificationBlock07.classify_7_42
    · exact SmallMedianClassificationBlock07.classify_7_43
    · exact SmallMedianClassificationBlock07.classify_7_44
    · exact SmallMedianClassificationBlock07.classify_7_45
    · exact SmallMedianClassificationBlock07.classify_7_46
    · exact SmallMedianClassificationBlock07.classify_7_47
    · exact SmallMedianClassificationBlock07.classify_7_48
    · exact SmallMedianClassificationBlock07.classify_7_49
    · exact SmallMedianClassificationBlock08.classify_7_50
    · exact SmallMedianClassificationBlock08.classify_7_51
    · exact SmallMedianClassificationBlock08.classify_7_52
    · exact SmallMedianClassificationBlock08.classify_7_53
    · exact SmallMedianClassificationBlock08.classify_7_54
    · exact SmallMedianClassificationBlock08.classify_7_55
    · exact SmallMedianClassificationBlock08.classify_7_56
    · exact SmallMedianClassificationBlock08.classify_7_57
    · exact SmallMedianClassificationBlock08.classify_7_58

#print axioms all_small

end CodexPaper4.SmallMedianClassification
