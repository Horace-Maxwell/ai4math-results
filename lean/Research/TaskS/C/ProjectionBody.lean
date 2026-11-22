import Research.TaskS.C.Coordinates

namespace TaskS.C
open Set Challenge
open scoped BigOperators

/-- A linear map killing a vertex sends the simplex onto the image of the
opposite facet. Strict interior ensures that the omitted vertex's image is a
convex combination of the projected facet vertices, including in dimension one. -/
theorem image_simplex_eq_image_opposite {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : Fin (n+2) → Space (n+1)) (hi : (0 : Space (n+1)) ∈ interior (simplex v))
    (i : Fin (n+2)) (p : Space (n+1) →ₗ[ℝ] E) (hp : p (v i) = 0) :
    p '' simplex v = p '' convexHull ℝ (range fun k => v (i.succAbove k)) := by
  classical
  obtain ⟨β,hβ,_hs,hz,_⟩ := coordinates v hi
  let w := fun k => β (i.succAbove k)
  let S := ∑ k, w k
  have hS : 0 < S := Finset.sum_pos (fun k _ => hβ (i.succAbove k)) Finset.univ_nonempty
  let f := fun k => p (v (i.succAbove k))
  have hzero : ∑ k, w k • f k = 0 := by
    have h := congrArg p hz
    rw [map_sum, Fin.sum_univ_succAbove _ i] at h
    simpa [hp,w,f] using h
  have hn : ∑ k, (S⁻¹ * w k) = 1 := by
    rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hS.ne'
  have hsum : ∑ k, (S⁻¹ * w k) • f k = 0 := by
    simp only [← smul_smul, ← Finset.smul_sum, hzero, smul_zero]
  have h0 : (0:E) ∈ convexHull ℝ (range f) := by
    rw [← hsum]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => mul_nonneg (inv_nonneg.mpr hS.le) (hβ _).le)
      hn (fun k _ => subset_convexHull ℝ _ ⟨k,rfl⟩)
  rw [simplex,p.image_convexHull,p.image_convexHull,← Set.range_comp,← Set.range_comp]
  change convexHull ℝ (range (p ∘ v)) = convexHull ℝ (range f)
  refine Set.Subset.antisymm (convexHull_min ?_ (convex_convexHull ℝ _)) (convexHull_mono ?_)
  · rintro _ ⟨k,rfl⟩
    by_cases hk : k = i
    · subst k; simpa [hp] using h0
    · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
      exact subset_convexHull ℝ _ ⟨l,rfl⟩
  · rintro _ ⟨l,rfl⟩
    exact ⟨i.succAbove l,rfl⟩

#print axioms image_simplex_eq_image_opposite

end TaskS.C
