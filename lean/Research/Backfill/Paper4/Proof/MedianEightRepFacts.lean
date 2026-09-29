import Research.Backfill.Paper4.Proof.MedianEightRepFacts0
import Research.Backfill.Paper4.Proof.MedianEightRepFacts1
import Research.Backfill.Paper4.Proof.MedianEightRepFacts2
import Research.Backfill.Paper4.Proof.MedianEightRepFacts3
import Research.Backfill.Paper4.Proof.MedianEightRepFacts4
import Research.Backfill.Paper4.Proof.MedianEightRepFacts5
import Research.Backfill.Paper4.Proof.MedianEightRepFacts6

/-! All 69 representatives: median, and (Q3' and Q4) or G1 or G2 (Claude, 2026-09-28). -/
set_option autoImplicit false
set_option maxRecDepth 8192

namespace ClaudePaper4
open BackfillPaper4

theorem L8_median (j : Fin 69) : Challenge.IsMedian (L8 j) := by
  fin_cases j
  · exact MedianEightRepFacts0.median_00
  · exact MedianEightRepFacts0.median_01
  · exact MedianEightRepFacts0.median_02
  · exact MedianEightRepFacts0.median_03
  · exact MedianEightRepFacts0.median_04
  · exact MedianEightRepFacts0.median_05
  · exact MedianEightRepFacts0.median_06
  · exact MedianEightRepFacts0.median_07
  · exact MedianEightRepFacts0.median_08
  · exact MedianEightRepFacts0.median_09
  · exact MedianEightRepFacts1.median_10
  · exact MedianEightRepFacts1.median_11
  · exact MedianEightRepFacts1.median_12
  · exact MedianEightRepFacts1.median_13
  · exact MedianEightRepFacts1.median_14
  · exact MedianEightRepFacts1.median_15
  · exact MedianEightRepFacts1.median_16
  · exact MedianEightRepFacts1.median_17
  · exact MedianEightRepFacts1.median_18
  · exact MedianEightRepFacts1.median_19
  · exact MedianEightRepFacts2.median_20
  · exact MedianEightRepFacts2.median_21
  · exact MedianEightRepFacts2.median_22
  · exact MedianEightRepFacts2.median_23
  · exact MedianEightRepFacts2.median_24
  · exact MedianEightRepFacts2.median_25
  · exact MedianEightRepFacts2.median_26
  · exact MedianEightRepFacts2.median_27
  · exact MedianEightRepFacts2.median_28
  · exact MedianEightRepFacts2.median_29
  · exact MedianEightRepFacts3.median_30
  · exact MedianEightRepFacts3.median_31
  · exact MedianEightRepFacts3.median_32
  · exact MedianEightRepFacts3.median_33
  · exact MedianEightRepFacts3.median_34
  · exact MedianEightRepFacts3.median_35
  · exact MedianEightRepFacts3.median_36
  · exact MedianEightRepFacts3.median_37
  · exact MedianEightRepFacts3.median_38
  · exact MedianEightRepFacts3.median_39
  · exact MedianEightRepFacts4.median_40
  · exact MedianEightRepFacts4.median_41
  · exact MedianEightRepFacts4.median_42
  · exact MedianEightRepFacts4.median_43
  · exact MedianEightRepFacts4.median_44
  · exact MedianEightRepFacts4.median_45
  · exact MedianEightRepFacts4.median_46
  · exact MedianEightRepFacts4.median_47
  · exact MedianEightRepFacts4.median_48
  · exact MedianEightRepFacts4.median_49
  · exact MedianEightRepFacts5.median_50
  · exact MedianEightRepFacts5.median_51
  · exact MedianEightRepFacts5.median_52
  · exact MedianEightRepFacts5.median_53
  · exact MedianEightRepFacts5.median_54
  · exact MedianEightRepFacts5.median_55
  · exact MedianEightRepFacts5.median_56
  · exact MedianEightRepFacts5.median_57
  · exact MedianEightRepFacts5.median_58
  · exact MedianEightRepFacts5.median_59
  · exact MedianEightRepFacts6.median_60
  · exact MedianEightRepFacts6.median_61
  · exact MedianEightRepFacts6.median_62
  · exact MedianEightRepFacts6.median_63
  · exact MedianEightRepFacts6.median_64
  · exact MedianEightRepFacts6.median_65
  · exact MedianEightRepFacts6.median_66
  · exact MedianEightRepFacts6.median_67
  · exact MedianEightRepFacts6.median_68

theorem L8_q (j : Fin 69) : (Challenge.Question3' (L8 j) ∧ Challenge.Question4 (L8 j)) ∨
    Nonempty (L8 j ≃g Challenge.G1) ∨ Nonempty (L8 j ≃g Challenge.G2) := by
  fin_cases j
  · exact MedianEightRepFacts0.q_00
  · exact MedianEightRepFacts0.q_01
  · exact MedianEightRepFacts0.q_02
  · exact MedianEightRepFacts0.q_03
  · exact MedianEightRepFacts0.q_04
  · exact MedianEightRepFacts0.q_05
  · exact MedianEightRepFacts0.q_06
  · exact MedianEightRepFacts0.q_07
  · exact MedianEightRepFacts0.q_08
  · exact MedianEightRepFacts0.q_09
  · exact MedianEightRepFacts1.q_10
  · exact MedianEightRepFacts1.q_11
  · exact MedianEightRepFacts1.q_12
  · exact MedianEightRepFacts1.q_13
  · exact MedianEightRepFacts1.q_14
  · exact MedianEightRepFacts1.q_15
  · exact MedianEightRepFacts1.q_16
  · exact MedianEightRepFacts1.q_17
  · exact MedianEightRepFacts1.q_18
  · exact MedianEightRepFacts1.q_19
  · exact MedianEightRepFacts2.q_20
  · exact MedianEightRepFacts2.q_21
  · exact MedianEightRepFacts2.q_22
  · exact MedianEightRepFacts2.q_23
  · exact MedianEightRepFacts2.q_24
  · exact MedianEightRepFacts2.q_25
  · exact MedianEightRepFacts2.q_26
  · exact MedianEightRepFacts2.q_27
  · exact MedianEightRepFacts2.q_28
  · exact MedianEightRepFacts2.q_29
  · exact MedianEightRepFacts3.q_30
  · exact MedianEightRepFacts3.q_31
  · exact MedianEightRepFacts3.q_32
  · exact MedianEightRepFacts3.q_33
  · exact MedianEightRepFacts3.q_34
  · exact MedianEightRepFacts3.q_35
  · exact MedianEightRepFacts3.q_36
  · exact MedianEightRepFacts3.q_37
  · exact MedianEightRepFacts3.q_38
  · exact MedianEightRepFacts3.q_39
  · exact MedianEightRepFacts4.q_40
  · exact MedianEightRepFacts4.q_41
  · exact MedianEightRepFacts4.q_42
  · exact MedianEightRepFacts4.q_43
  · exact MedianEightRepFacts4.q_44
  · exact MedianEightRepFacts4.q_45
  · exact MedianEightRepFacts4.q_46
  · exact MedianEightRepFacts4.q_47
  · exact MedianEightRepFacts4.q_48
  · exact MedianEightRepFacts4.q_49
  · exact MedianEightRepFacts5.q_50
  · exact MedianEightRepFacts5.q_51
  · exact MedianEightRepFacts5.q_52
  · exact MedianEightRepFacts5.q_53
  · exact MedianEightRepFacts5.q_54
  · exact MedianEightRepFacts5.q_55
  · exact MedianEightRepFacts5.q_56
  · exact MedianEightRepFacts5.q_57
  · exact MedianEightRepFacts5.q_58
  · exact MedianEightRepFacts5.q_59
  · exact MedianEightRepFacts6.q_60
  · exact MedianEightRepFacts6.q_61
  · exact MedianEightRepFacts6.q_62
  · exact MedianEightRepFacts6.q_63
  · exact MedianEightRepFacts6.q_64
  · exact MedianEightRepFacts6.q_65
  · exact MedianEightRepFacts6.q_66
  · exact MedianEightRepFacts6.q_67
  · exact MedianEightRepFacts6.q_68

#print axioms L8_median
#print axioms L8_q

end ClaudePaper4
