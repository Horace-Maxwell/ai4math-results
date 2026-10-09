import Research.Backfill.Paper6.PairLeaves0_00
import Research.Backfill.Paper6.PairLeaves1_00
import Research.Backfill.Paper6.PairLeaves2_00
import Research.Backfill.Paper6.PairAssembly3_0
import Research.Backfill.Paper6.PairAssembly3_1
import Research.Backfill.Paper6.PairAssembly3_2
import Research.Backfill.Paper6.PairAssembly3_3
import Research.Backfill.Paper6.PairAssembly3_4
import Research.Backfill.Paper6.PairAssembly3_5
import Research.Backfill.Paper6.PairAssembly3_6
import Research.Backfill.Paper6.PairAssembly3_7

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

theorem all_pairs0 : checkPairs0 = true := by
  unfold checkPairs0
  exact pair_leaf0_root

theorem all_pairs1 : checkPairs1 = true := by
  unfold checkPairs1
  exact pair_leaf1_root

theorem all_pairs2 : checkPairs2 = true := by
  unfold checkPairs2
  unfold pairSuffix2Depth0
  apply allLe_intro
  intro a3 ha3
  norm_num at ha3
  have ha3_cases_upper : a3 ≤ 7 := by omega
  interval_cases a3
  · exact pair_leaf2_0
  · exact pair_leaf2_1
  · exact pair_leaf2_2
  · exact pair_leaf2_3
  · exact pair_leaf2_4
  · exact pair_leaf2_5
  · exact pair_leaf2_6
  · exact pair_leaf2_7

theorem all_pairs3 : checkPairs3 = true := by
  unfold checkPairs3
  unfold pairSuffix3Depth0
  apply allLe_intro
  intro a7 ha7
  norm_num at ha7
  have ha7_cases_upper : a7 ≤ 7 := by omega
  interval_cases a7
  · exact assembled_pair3_0
  · exact assembled_pair3_1
  · exact assembled_pair3_2
  · exact assembled_pair3_3
  · exact assembled_pair3_4
  · exact assembled_pair3_5
  · exact assembled_pair3_6
  · exact assembled_pair3_7

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.all_pairs0
#print axioms Paper6FiveExclusion.all_pairs1
#print axioms Paper6FiveExclusion.all_pairs2
#print axioms Paper6FiveExclusion.all_pairs3
