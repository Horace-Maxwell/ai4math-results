import Research.TaskL.Semigroup.Interval
import Research.TaskL.Semigroup.Even

namespace TaskL.Semigroup.Proof

theorem LengthsExist : Challenge.LengthsExist := lengthsExist
theorem LengthsInterval : Challenge.LengthsInterval := lengthsInterval

theorem PositiveLengthsInterval : Challenge.PositiveLengthsInterval := by
  intro S hS a b j ha hb haj hjb
  exact ⟨lt_of_lt_of_le ha.1 haj, lengthsInterval S hS a b j ha.2 hb.2 haj hjb⟩

theorem EvenMultiplicityDescent : Challenge.EvenMultiplicityDescent :=
  even_of_interval lengthsInterval

end TaskL.Semigroup.Proof
