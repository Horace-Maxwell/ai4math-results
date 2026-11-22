import Research.TaskS.C.Challenge

noncomputable section
namespace TaskS.C.MeasureModel
open Set MeasureTheory
open scoped ENNReal BigOperators
open Challenge

def unit (n : ℕ) : Set (Space n) :=
  convexHull ℝ (insert 0 (range fun j : Fin n => (Pi.basisFun ℝ (Fin n)) j))

def edges {n : ℕ} (v : Fin (n+1) → Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i => v i.succ - v 0

theorem volume_edges {n : ℕ} (v : Fin (n+1) → Space n) :
    Challenge.volume v = |(edges v).det| := by
  let A := Matrix.of (fun i => Fin.cons (1 : ℝ) (v i))
  let T := Matrix.of (Fin.cons (Fin.cons (1 : ℝ) (v 0))
    (fun j : Fin n => Fin.cons (0 : ℝ) (v j.succ - v 0)))
  have he : T.det = A.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const (Fin.cons (0 : ℝ) (fun _ => -1)) 0 (by simp)
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [T,A,sub_eq_add_neg]
  have ht : T.det = (edges v).det := by
    rw [Matrix.det_succ_column_zero]
    simp [T, Fin.sum_univ_succ, edges, Matrix.submatrix]
    rfl
  change |A.det| = _
  rw [← he, ht]

theorem measure_simplex {n : ℕ} (v : Fin (n+1) → Space n) :
    MeasureTheory.volume (simplex v) =
      ENNReal.ofReal (Challenge.volume v) * MeasureTheory.volume (unit n) := by
  let A := (edges v).transpose
  let F : Space n →ᵃ[ℝ] Space n :=
    (AffineEquiv.constVAdd ℝ _ (v 0)).toAffineMap.comp A.toLin'.toAffineMap
  have h0 : F 0 = v 0 := by change v 0 + A.toLin' 0 = _; simp
  have h1 (j : Fin n) : F (Pi.basisFun ℝ (Fin n) j) = v j.succ := by
    change v 0 + A.mulVec _ = _
    rw [Pi.basisFun_apply, Matrix.mulVec_single_one]
    ext k
    simp [A, edges, Matrix.col]
  have hi : F '' unit n = simplex v := by
    rw [unit, F.image_convexHull, image_insert_eq, h0, ← range_comp, simplex]
    congr 1
    ext z
    constructor
    · rintro (rfl | ⟨j,hj⟩)
      · exact mem_range_self _
      · exact ⟨j.succ, (h1 j).symm.trans hj⟩
    · rintro ⟨j,rfl⟩
      refine Fin.cases (by exact mem_insert _ _) (fun k => ?_) j
      exact mem_insert_of_mem _ ⟨k,h1 k⟩
  have ha : F '' unit n = (fun w : Space n => v 0 + w) '' (A.toLin' '' unit n) := by
    rw [image_image]; rfl
  rw [← hi, ha, image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', Matrix.det_transpose, volume_edges]

theorem normalized_measure {n : ℕ} (v : Fin (n+1) → Space n) :
    MeasureTheory.volume (simplex v) / MeasureTheory.volume (unit n) =
      ENNReal.ofReal (Challenge.volume v) := by
  have hf : MeasureTheory.volume (unit n) ≠ ∞ :=
    ((finite_range ((Pi.basisFun ℝ (Fin n)) : Fin n → Space n)).insert 0).isCompact_convexHull ℝ
      |>.measure_lt_top.ne
  have ha : affineSpan ℝ (insert (0 : Space n) (range (Pi.basisFun ℝ (Fin n)))) = ⊤ := by
    apply SetLike.coe_injective
    rw [affineSpan_insert_zero, (Pi.basisFun ℝ (Fin n)).span_eq]
    rfl
  have hpos : 0 < MeasureTheory.volume (unit n) :=
    (isOpen_interior.measure_pos MeasureTheory.volume
      (interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr ha)).trans_le
        (measure_mono interior_subset)
  rw [measure_simplex, ENNReal.mul_div_cancel_right hpos.ne' hf]

end TaskS.C.MeasureModel
