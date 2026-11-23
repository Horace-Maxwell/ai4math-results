import Research.TaskT.HellyFive.WitnessThree
import Research.TaskT.HellyFive.WitnessFour
import Research.TaskT.HellyFive.CorePositive
import Research.TaskT.HellyFive.CoreNegative

namespace TaskT.HellyFive.FiniteGeometry

private theorem core_subset_aux {c : Finset (Grid 4)}
    (h : ∀ p ∈ c, p ∈ WitnessFour.vertices ∨ p ∈ WitnessFour.centers) :
    poly c ⊆ poly WitnessFour.vertices := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro _ ⟨p,hp,rfl⟩
  rcases h p hp with hV | hX
  · exact subset_convexHull ℝ _ ⟨p,hV,rfl⟩
  · have hM : p ∈ {z : Grid 4 | embed z ∈ poly WitnessFour.vertices ∧
        embed z ∉ (poly WitnessFour.vertices).extremePoints ℝ} := WitnessFour.geometry.2.symm ▸ hX
    exact hM.1

theorem positive_subset : poly CorePositive.vertices ⊆ poly WitnessFour.vertices :=
  core_subset_aux (by decide)

theorem negative_subset : poly CoreNegative.vertices ⊆ poly WitnessFour.vertices :=
  core_subset_aux (by decide)

private theorem empty_core_membership {c : Finset (Grid 4)}
    (he : (poly c).extremePoints ℝ = embed '' (c : Set (Grid 4)))
    (hx : {z : Grid 4 | embed z ∈ poly c ∧ embed z ∉ (poly c).extremePoints ℝ} = ∅)
    {z : Grid 4} : embed z ∈ poly c ↔ z ∈ c := by
  refine ⟨fun hz => ?_, fun h => subset_convexHull ℝ _ ⟨z,h,rfl⟩⟩
  by_cases h : embed z ∈ (poly c).extremePoints ℝ
  · rw [he] at h
    obtain ⟨w,hw,heq⟩ := h
    exact embed_inj heq ▸ hw
  · have hm : z ∈ {p : Grid 4 | embed p ∈ poly c ∧ embed p ∉ (poly c).extremePoints ℝ} := ⟨hz,h⟩
    rw [hx] at hm
    exact hm.elim

theorem positive_grid {z : Grid 4} : embed z ∈ poly CorePositive.vertices ↔ z ∈ CorePositive.vertices :=
  empty_core_membership CorePositive.geometry.1 (by simpa [CorePositive.centers] using CorePositive.geometry.2)

theorem negative_grid {z : Grid 4} : embed z ∈ poly CoreNegative.vertices ↔ z ∈ CoreNegative.vertices :=
  empty_core_membership CoreNegative.geometry.1 (by simpa [CoreNegative.centers] using CoreNegative.geometry.2)

theorem disjoint_at_old_extreme {p : Space 4}
    (hp : p ∈ (poly WitnessFour.vertices).extremePoints ℝ) :
    ¬ (p ∈ poly CorePositive.vertices ∧ p ∈ poly CoreNegative.vertices) := by
  rw [WitnessFour.geometry.1] at hp
  obtain ⟨z,hz,rfl⟩ := hp
  rintro ⟨hp,hm⟩
  have hn : ∀ p ∈ WitnessFour.vertices, p ∈ CorePositive.vertices → p ∉ CoreNegative.vertices := by decide
  exact hn z hz (positive_grid.mp hp) (negative_grid.mp hm)

end TaskT.HellyFive.FiniteGeometry
