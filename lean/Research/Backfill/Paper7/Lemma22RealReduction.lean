import Research.Backfill.Paper7.OrdinaryReducedMultiplicity

/-! Genuine real-parameter reduction. No integer approximation or integrality
assumption is used. This is a source-only helper, not the full Lemma22. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace Paper7Lemma22

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared Paper7Reduced
open scoped Matrix

theorem mult_eq_real_shift_nullity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    mult G m = matrixNullity (m • (1 : Matrix V V ℝ) - G.adjMatrix ℝ) := by
  have h := Paper7Spectrum.realHermitian_count_eq_shift_nullity
    (G.adjMatrix ℝ) (Paper7Spectrum.realAdjHermitian G) m
  change mult G m = matrixNullity (G.adjMatrix ℝ - m • (1 : Matrix V V ℝ)) at h
  rw [h]
  have hneg : G.adjMatrix ℝ - m • (1 : Matrix V V ℝ) =
      (-1 : ℝ) • (m • (1 : Matrix V V ℝ) - G.adjMatrix ℝ) := by
    simp only [neg_one_smul, neg_sub]
  rw [hneg]
  exact nullity_smul_of_ne_zero _ (-1 : ℝ) (by norm_num)

#print axioms Paper7Lemma22.mult_eq_real_shift_nullity

theorem square_sub_one_ne_zero (m : ℝ) (hmn : m ≠ -1) (hm1 : m ≠ 1) :
    m ^ 2 - 1 ≠ 0 := by
  intro h
  have hf : (m - 1) * (m + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · exact hm1 (by linarith)
  · exact hmn (by linarith)

#print axioms Paper7Lemma22.square_sub_one_ne_zero

theorem smat_eq_negative_schur (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    Smat b p q m = (-1 : ℝ) •
      (cycleShift b m - Matrix.diagonal (fun k =>
        (p k : ℝ) / m + (q k : ℝ) * m / (m ^ 2 - 1))) := by
  unfold Smat Cyc cycleShift fk
  simp only [neg_one_smul, neg_sub]
  abel

#print axioms Paper7Lemma22.smat_eq_negative_schur

theorem ordinary_mult_eq_smat_nullity (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (m : ℝ) (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    mult (SG b p q) m = matrixNullity (Smat b p q m) := by
  classical
  have hquad := square_sub_one_ne_zero m hmn hm1
  let : Invertible (pendantShift (K := ℝ) b (pq b p q) m) :=
    Matrix.invertibleOfIsUnitDet _ (pendantShift_isUnit_det b p q m hm0 hquad)
  calc
    mult (SG b p q) m =
        matrixNullity (m • (1 : Matrix (SunV b (pq b p q))
          (SunV b (pq b p q)) ℝ) - (SG b p q).adjMatrix ℝ) :=
      mult_eq_real_shift_nullity (SG b p q) m
    _ = matrixNullity (Matrix.fromBlocks (cycleShift b m)
        (attachment (K := ℝ) b (pq b p q))
        (attachment (K := ℝ) b (pq b p q)).transpose
        (pendantShift (K := ℝ) b (pq b p q) m)) := by
      rw [sun_shift_fromBlocks b (pq b p q) hb m]
    _ = matrixNullity (cycleShift b m - Matrix.diagonal (fun k =>
        (p k : ℝ) / m + (q k : ℝ) * m / (m ^ 2 - 1))) := by
      rw [nullity_fromBlocks_eq_schur, attachment_inverse_coupling b p q m hm0 hquad]
    _ = matrixNullity (Smat b p q m) := by
      rw [smat_eq_negative_schur]
      exact (nullity_smul_of_ne_zero _ (-1 : ℝ) (by norm_num)).symm

#print axioms Paper7Lemma22.ordinary_mult_eq_smat_nullity

theorem transfer_det_one (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) (k : Fin b) :
    (Tk b p q m k).det = 1 := by
  simp [Tk, Matrix.det_fin_two]

#print axioms Paper7Lemma22.transfer_det_one

theorem monodromy_det_one (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    (Mono b p q m).det = 1 := by
  have hprod (l : List (Fin b)) : ((l.map (Tk b p q m)).prod).det = 1 := by
    induction l with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Matrix.det_mul,
        transfer_det_one, ih, one_mul]
  exact hprod (List.finRange b).reverse

#print axioms Paper7Lemma22.monodromy_det_one

end Paper7Lemma22
