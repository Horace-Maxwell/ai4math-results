import Research.TaskR.CSS.Challenge

namespace TaskR.CSS.VolumeCalc

open TaskR.CSS.Challenge Set MeasureTheory
open scoped ENNReal

private noncomputable def edges : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3, 2, 2, 2; 1, 2, 1, 1; 1, 1, 2, 1; 1, 1, 1, 2]

private theorem det_edges : edges.det = 6 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, edges, Fin.succAbove]

private noncomputable def placement : Space →ᵃ[ℝ] Space :=
  (AffineEquiv.constVAdd ℝ Space (embed (-weight))).toAffineMap.comp edges.toLin'.toAffineMap

private theorem placement_basic (i : Fin 4) : placement (embed (e i)) = embed (e i) := by
  ext j
  change embed (-weight) j + (edges.mulVec (embed (e i))) j = _
  fin_cases i <;> fin_cases j <;>
    norm_num [embed, e, weight, edges, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply]

private theorem placement_zero : placement 0 = embed (-weight) := by
  change embed (-weight) + edges.toLin' 0 = _
  simp

private theorem image_body : placement '' unitSimplex = P := by
  unfold unitSimplex P vertices
  rw [placement.image_convexHull, Set.image_insert_eq, placement_zero, ← Set.range_comp]
  congr 3
  funext i
  exact placement_basic i

theorem volume_from_nonHollow (hn : NonHollow) : Volume := by
  have image_eq : placement '' unitSimplex =
      (fun x : Space => embed (-weight) + x) '' (edges.toLin' '' unitSimplex) := by
    rw [Set.image_image]
    rfl
  have hv : volume P = 6 * volume unitSimplex := by
    rw [← image_body, image_eq, image_add_left, measure_preimage_add,
      Measure.addHaar_image_linearMap, LinearMap.det_toLin', det_edges]
    norm_num
  have hfinite : volume unitSimplex ≠ ∞ :=
    (((Set.finite_range (fun i : Fin 4 => embed (e i))).insert (0 : Space)).isCompact_convexHull ℝ).measure_lt_top.ne
  have hunit : volume unitSimplex ≠ 0 := by
    intro h
    have hp : 0 < volume P := lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨0, hn⟩)
      (measure_mono interior_subset)
    rw [hv, h, mul_zero] at hp
    exact lt_irrefl _ hp
  unfold Volume normalizedVolume
  rw [hv, ENNReal.mul_div_cancel_right hunit hfinite]

end TaskR.CSS.VolumeCalc
