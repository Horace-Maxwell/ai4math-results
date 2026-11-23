import Research.TaskT.HellyFive.DimensionOne
import Research.TaskT.HellyFive.WitnessTwo
import Research.TaskT.HellyFive.WitnessThree
import Research.TaskT.HellyFive.LiftAttainable
import Research.TaskT.HellyFive.PlanarUpper
import Research.TaskT.HellyFive.UpperThree
import Research.TaskT.HellyFive.UpperTransfer
import Research.TaskT.HellyFive.LowerTransfer

namespace TaskT.HellyFive.Proof
open FiniteGeometry UpperFive

theorem attained (n : ℕ) (hn : 0 < n) : value n ∈ attainableCounts n := by
  by_cases h : 4 ≤ n
  · exact Lift.attainable_ge_four n h
  · rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl
    · exact DimensionOne.attainable
    · exact WitnessTwo.attainable
    · exact WitnessThree.attainable

theorem poly_bound (n : ℕ) (hn : 0 < n) : UpperTransfer.PolyBound n (value n) := by
  intro V
  change (otherGrid V).ncard ≤ 5 →
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ value n + 5
  intro hk
  by_cases h : 3 ≤ n
  · exact upper_of_poly h V hk
  · rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · exact Nat.add_le_add (DimensionOne.extreme_card_le V) hk
    · exact PlanarUpper.upper V hk

theorem ExactHellyFive : TaskT.HellyFive.ExactHellyFive := by
  intro n hn
  exact ⟨preservesFive_of_polyBound (poly_bound n hn),
    fun _ h => attainableCount_le_preservingBound (attained n hn) h⟩

theorem ExactVertexFive : TaskT.HellyFive.ExactVertexFive := by
  intro n hn
  refine ⟨attained n hn, ?_⟩
  rintro t ⟨V,hE,hX⟩
  change ((poly V).extremePoints ℝ).encard = (t : ℕ∞) at hE
  change (otherGrid V).encard = 5 at hX
  have hcE : ((poly V).extremePoints ℝ).ncard = t := by simp [Set.ncard_def,hE]
  have hcX : (otherGrid V).ncard = 5 := by simp [Set.ncard_def,hX]
  have hb : ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ value n + 5 :=
    poly_bound n hn V hcX.le
  omega

end TaskT.HellyFive.Proof
