import Research.TaskJ.Rank.Proof

namespace TaskJ.Rank

theorem check_TwoPointParameters : Challenge.TwoPointParameters := Proof.TwoPointParameters
theorem check_FivePointParameters : Challenge.FivePointParameters := Proof.FivePointParameters
theorem check_TwoPointRank : Challenge.TwoPointRank := Proof.TwoPointRank
theorem check_FivePointRank : Challenge.FivePointRank := Proof.FivePointRank
theorem check_TwoPointCounterexample : Challenge.TwoPointCounterexample :=
  Proof.TwoPointCounterexample
theorem check_FivePointCounterexample : Challenge.FivePointCounterexample :=
  Proof.FivePointCounterexample

end TaskJ.Rank

#print axioms TaskJ.Rank.check_TwoPointParameters
#print axioms TaskJ.Rank.check_FivePointParameters
#print axioms TaskJ.Rank.check_TwoPointRank
#print axioms TaskJ.Rank.check_FivePointRank
#print axioms TaskJ.Rank.check_TwoPointCounterexample
#print axioms TaskJ.Rank.check_FivePointCounterexample
