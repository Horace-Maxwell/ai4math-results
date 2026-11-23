import Research.TaskT.HellyFive.LowerTransfer
import Research.TaskT.HellyFive.WitnessThree
import Research.TaskT.HellyFive.WitnessFour

namespace TaskT.HellyFive

/-- Applied to the original convex-family definition, the three-dimensional
certificate forces every admissible bound to be at least eighteen. -/
theorem helly_three_lower {b : ℕ} (h : PreservesFive 3 b) : 18 ≤ b :=
  attainableCount_le_preservingBound FiniteGeometry.WitnessThree.attainable h

/-- The analogous lower bound forced by the four-dimensional lattice polytope. -/
theorem helly_four_lower {b : ℕ} (h : PreservesFive 4 b) : 37 ≤ b :=
  attainableCount_le_preservingBound FiniteGeometry.WitnessFour.attainable h

end TaskT.HellyFive
