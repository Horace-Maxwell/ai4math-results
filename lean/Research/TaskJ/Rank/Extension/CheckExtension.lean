import Research.TaskJ.Rank.Extension.Proof

namespace TaskJ.Rank.Extension

-- The frozen file declares Extension.UnboundedGap directly. Export the same
-- declaration under the conventional Challenge prefix for the exact test.
namespace Challenge
export TaskJ.Rank.Extension (UnboundedGap)
end Challenge

theorem check_UnboundedGap : Challenge.UnboundedGap := Proof.UnboundedGap

-- Check the original, fully qualified type directly as well.
example : TaskJ.Rank.Extension.UnboundedGap := check_UnboundedGap

end TaskJ.Rank.Extension

#print axioms TaskJ.Rank.Extension.check_UnboundedGap
