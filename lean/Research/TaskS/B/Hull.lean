import Research.TaskS.B.Challenge

namespace TaskS.B.Hull

open scoped BigOperators
open TaskS.B.Challenge

theorem sum_vertex (n : ℕ) : ∑ j, vertex n j = 0 := by
  classical
  ext k
  rw [Fin.sum_univ_succ]
  simp [vertex, Finset.sum_apply, Pi.single_apply]

theorem scaled {n : ℕ} (u : Fin (n+1) → ℝ) (hu : ∀ j, 0 ≤ u j) {r : ℝ}
    (hr : 0 < r) (hs : ∑ j, u j ≤ r) :
    ∃ y ∈ terminal n, r • y = ∑ j, u j • vertex n j := by
  classical
  let a := (r - ∑ j, u j) / (n+1 : ℝ)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hs) (by positivity)
  let w := fun j => (u j + a) / r
  have hc : (n : ℝ) + 1 ≠ 0 := by positivity
  have hw : ∑ j, w j = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, a]
    field_simp [hr.ne', hc]
    ring
  refine ⟨∑ j, w j • vertex n j, ?_, ?_⟩
  · exact (convex_convexHull ℝ _).sum_mem (fun j _ => div_nonneg (add_nonneg (hu j) ha) hr.le)
      hw (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)
  · rw [Finset.smul_sum]
    calc
      ∑ j, r • w j • vertex n j = ∑ j, (u j + a) • vertex n j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
        congr 1
        change r * ((u j + a) / r) = _
        field_simp
      _ = _ := by simp_rw [add_smul]; rw [Finset.sum_add_distrib, ← Finset.smul_sum, sum_vertex, smul_zero, add_zero]

end TaskS.B.Hull
