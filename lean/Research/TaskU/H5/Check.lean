import Research.TaskU.H5.Audit
import Research.TaskU.H5.CheckWitness
import Research.TaskU.H5.CycPos
import Research.TaskU.H5.Minimum

namespace TaskU.H5.Check

theorem check_witnessValue : Challenge.witnessValue := Proof.witnessValue
theorem check_leastPositiveMultiple : Challenge.leastPositiveMultiple := Proof.leastPositiveMultiple

#print axioms check_witnessValue
#print axioms check_leastPositiveMultiple

end TaskU.H5.Check
