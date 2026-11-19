import Research.TaskJ.Grid.GridFinish
import Research.TaskJ.Grid.GridLowerNormalized

namespace Proof

theorem LengthUpperBound : Challenge.LengthUpperBound := Grid.upper_complete
theorem LengthAttained : Challenge.LengthAttained := Grid.Finish.restore Grid.Attainment.normalized_attained
theorem YuanGapAtLongest : Challenge.YuanGapAtLongest := Grid.Finish.gap_of_bounds LengthUpperBound LengthAttained

end Proof

#print axioms Proof.LengthUpperBound
#print axioms Proof.LengthAttained
#print axioms Proof.YuanGapAtLongest
