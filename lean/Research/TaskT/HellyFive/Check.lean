import Research.TaskT.HellyFive.Proof

namespace TaskT.HellyFive
namespace Challenge
export TaskT.HellyFive (ExactHellyFive ExactVertexFive)
end Challenge

theorem check_ExactHellyFive : Challenge.ExactHellyFive := Proof.ExactHellyFive
theorem check_ExactVertexFive : Challenge.ExactVertexFive := Proof.ExactVertexFive

#print axioms Proof.ExactHellyFive
#print axioms Proof.ExactVertexFive
#print axioms check_ExactHellyFive
#print axioms check_ExactVertexFive

end TaskT.HellyFive
