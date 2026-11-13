import Research.TaskG.Main
set_option autoImplicit false
namespace TaskG.Check

theorem check_ShpectorovAnswer : TaskG.Challenge.ShpectorovAnswer := TaskG.Proof.answer

theorem check_StrongShpectorovAnswer : TaskG.Challenge.StrongShpectorovAnswer :=
  TaskG.Proof.strong_answer

#print TaskG.Challenge.ShpectorovAnswer
#print TaskG.Challenge.StrongShpectorovAnswer
#print TaskG.Challenge.WitnessConditions
#print TaskG.Challenge.DirectlyIndecomposable
#print TaskG.Challenge.FormSpaceOneDimensional
#print TaskG.Proof.T
#print TaskG.Proof.F
#print TaskG.Proof.β
#print TaskG.Proof.g
#print TaskG.Proof.X
#print TaskG.Check.check_ShpectorovAnswer
#print TaskG.Check.check_StrongShpectorovAnswer
#print axioms TaskG.Check.check_ShpectorovAnswer
#print axioms TaskG.Check.check_StrongShpectorovAnswer
end TaskG.Check
