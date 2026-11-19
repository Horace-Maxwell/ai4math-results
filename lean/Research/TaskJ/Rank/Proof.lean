import Research.TaskJ.Rank.Parameters
import Research.TaskJ.Rank.RankValues

namespace TaskJ.Rank.Proof

theorem TwoPointParameters : Challenge.TwoPointParameters := Parameters.two

theorem FivePointParameters : Challenge.FivePointParameters := Parameters.five

theorem TwoPointRank : Challenge.TwoPointRank := Values.two

theorem FivePointRank : Challenge.FivePointRank := Values.five

theorem TwoPointCounterexample : Challenge.TwoPointCounterexample := by
  refine ⟨Parameters.twoAction, Parameters.equivariance _, Parameters.twoBases,
    TwoPointParameters, TwoPointRank, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, bound, _, _⟩ := TwoPointParameters
  have rankExact : Group.rank (Challenge.equivariantGroup Challenge.twoSwap) = 1 := TwoPointRank
  rw [rankExact, bound]
  decide

theorem FivePointCounterexample : Challenge.FivePointCounterexample := by
  refine ⟨Parameters.fiveAction, Parameters.equivariance _, Parameters.fiveBases,
    FivePointParameters, FivePointRank, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, preprint, journal⟩ := FivePointParameters
  have rankExact : Group.rank (Challenge.equivariantGroup Challenge.fiveSwap) = 2 := FivePointRank
  rw [rankExact, preprint, journal]
  decide

end TaskJ.Rank.Proof

#print axioms TaskJ.Rank.Proof.TwoPointParameters
#print axioms TaskJ.Rank.Proof.FivePointParameters
#print axioms TaskJ.Rank.Proof.TwoPointRank
#print axioms TaskJ.Rank.Proof.FivePointRank
#print axioms TaskJ.Rank.Proof.TwoPointCounterexample
#print axioms TaskJ.Rank.Proof.FivePointCounterexample
