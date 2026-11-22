import Research.TaskS.C.Coordinates

namespace TaskS.C

open Challenge
open scoped BigOperators

/-- Absolute maximal minors of the integer ray matrix. -/
def frequency {d : ℕ} (u : Fin (d+1) → Lattice d) (i : Fin (d+1)) : ℕ :=
  (Matrix.of fun j : Fin d => u (i.succAbove j)).det.natAbs

private theorem replaced_minor {d : ℕ} (v : Fin (d+1) → Space d) (i : Fin (d+1)) :
    |((Matrix.of fun j => Fin.cons (1 : ℝ) (v j)).updateRow i
      (Fin.cons (1 : ℝ) (0 : Space d))).det| =
      |(Matrix.of fun k => v (i.succAbove k)).det| := by
  let H : Matrix (Fin (d+1)) (Fin (d+1)) ℝ := Matrix.of fun j => Fin.cons (1 : ℝ) (v j)
  change |(H.updateRow i _).det| = _
  rw [Matrix.det_succ_row _ i, Fin.sum_univ_succ]
  simp [H, Matrix.updateRow_apply, Fin.succAbove_ne, abs_mul,
    Matrix.submatrix, Finset.sum_const_zero]

theorem frequency_ratio {d : ℕ} (u : Fin (d+1) → Lattice d) (ω β : Fin (d+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hβ : ∀ i, 0 < β i) (hs : ∑ i, β i = 1)
    (hz : ∑ i, β i • vertices u ω i = 0) (i : Fin (d+1)) :
    (frequency u i : ℝ) * (∏ j, ω j) =
      volume (vertices u ω) * β i * ω i := by
  let v := vertices u ω
  let H : Matrix (Fin (d+1)) (Fin (d+1)) ℝ := Matrix.of fun j => Fin.cons (1 : ℝ) (v j)
  have hrow : (H.updateRow i (Fin.cons (1 : ℝ) (0 : Space d))).det = β i * H.det := by
    rw [← origin_row v β hs hz]
    exact Matrix.det_updateRow_sum H i β
  have hminor : |(Matrix.of fun k => v (i.succAbove k)).det| = β i * volume v := by
    rw [← replaced_minor v i]
    change |(H.updateRow i _).det| = β i * |H.det|
    rw [hrow, abs_mul, abs_of_pos (hβ i)]
  let U : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun k => u (i.succAbove k))
  have hcast : (((U.det : ℤ) : ℝ)) = ((Int.castRingHom ℝ).mapMatrix U).det :=
    (Int.castRingHom ℝ).map_det U
  have hvdet : (Matrix.of fun k => v (i.succAbove k)).det =
      (∏ k, ω (i.succAbove k)) * (U.det : ℝ) := by
    rw [hcast]
    exact Matrix.det_mul_column _ _
  have hfreq : (frequency u i : ℝ) = |(U.det : ℝ)| := by
    simp [frequency, U, Nat.cast_natAbs, Int.cast_abs]
  rw [hvdet, abs_mul, abs_of_pos (Finset.prod_pos fun k _ => hω _), ← hfreq] at hminor
  rw [Fin.prod_univ_succAbove ω i]
  change _ = volume v * β i * ω i
  calc
    _ = ((∏ k, ω (i.succAbove k)) * (frequency u i : ℝ)) * ω i := by ring
    _ = _ := by rw [hminor]; ring

end TaskS.C
