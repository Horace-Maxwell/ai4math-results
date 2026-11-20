import Research.TaskL.Semigroup.Proof

namespace TaskL.Semigroup

theorem check_LengthsExist : Challenge.LengthsExist := Proof.LengthsExist
theorem check_LengthsInterval : Challenge.LengthsInterval := Proof.LengthsInterval
theorem check_PositiveLengthsInterval : Challenge.PositiveLengthsInterval := Proof.PositiveLengthsInterval
theorem check_EvenMultiplicityDescent : Challenge.EvenMultiplicityDescent := Proof.EvenMultiplicityDescent

#print axioms Proof.LengthsExist
#print axioms Proof.LengthsInterval
#print axioms Proof.PositiveLengthsInterval
#print axioms Proof.EvenMultiplicityDescent
#print axioms check_LengthsExist
#print axioms check_LengthsInterval
#print axioms check_PositiveLengthsInterval
#print axioms check_EvenMultiplicityDescent

end TaskL.Semigroup
