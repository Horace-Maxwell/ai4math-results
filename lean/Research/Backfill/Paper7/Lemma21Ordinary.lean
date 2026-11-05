import Research.Backfill.Paper7.Lemma21SchurInertia
import Research.Backfill.Paper7.SunSchurInertia
import Research.Backfill.Paper7.Lemma22RealReduction
import Research.Backfill.Paper7.PQArmCoordinates

/-! Exact ordinary Schur inertia for every real x outside [-1,1]. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators
namespace Paper7Lemma21
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared Paper7Reduced Paper7Inertia Paper7Comparison Paper7Lemma22

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem nNeg_zero_of_nonnegative (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (h : ∀ v, 0 ≤ D.toQuadraticForm' v) : nNeg D = 0 := by
  have hz : nNeg (0 : Matrix ι ι ℝ) = 0 := by
    simpa using (inertia_diagonal (fun _ : ι => (0 : ℝ))).2
  have hi := (inertia_mono (0 : Matrix ι ι ℝ) D (by simp) hD (by
    intro v
    simpa [quadratic_apply] using h v)).2
  omega
#print axioms Paper7Lemma21.nNeg_zero_of_nonnegative

theorem nPos_zero_of_nonpositive (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (h : ∀ v, D.toQuadraticForm' v ≤ 0) : nPos D = 0 := by
  have hz : nPos (0 : Matrix ι ι ℝ) = 0 := by
    simpa using (inertia_diagonal (fun _ : ι => (0 : ℝ))).1
  have hi := (inertia_mono D (0 : Matrix ι ι ℝ) hD (by simp) (by
    intro v
    simpa [quadratic_apply] using h v)).1
  omega
#print axioms Paper7Lemma21.nPos_zero_of_nonpositive

theorem pathShift_isHermitian (x : ℝ) (t : ℕ) : (pathShift x t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [pathShift, eq_comm, or_comm]
#print axioms Paper7Lemma21.pathShift_isHermitian

theorem pendantShift_isHermitian (b : ℕ) (L : Fin b → List ℕ) (x : ℝ) :
    (pendantShift b L x).IsHermitian := by
  unfold pendantShift
  apply Matrix.isHermitian_blockDiagonal'_iff.mpr
  intro k
  apply Matrix.isHermitian_blockDiagonal'_iff.mpr
  intro j
  exact pathShift_isHermitian x _
#print axioms Paper7Lemma21.pendantShift_isHermitian

theorem pathShift_nonnegative (x : ℝ) (hx : 1 < x) (t : ℕ)
    (ht : t = 1 ∨ t = 2) (v : Fin t → ℝ) : 0 ≤ (pathShift x t).toQuadraticForm' v := by
  rcases ht with rfl | rfl
  · have hp := mul_nonneg (show 0 ≤ x by linarith) (sq_nonneg (v 0))
    simpa [quadratic_apply, pathShift, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, pow_two, mul_left_comm, mul_assoc] using hp
  · have hp := mul_nonneg (show 0 ≤ x - 1 by linarith)
      (add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v 1)))
    simp [quadratic_apply, pathShift, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 - v 1)]
#print axioms Paper7Lemma21.pathShift_nonnegative

theorem pathShift_nonpositive (x : ℝ) (hx : x < -1) (t : ℕ)
    (ht : t = 1 ∨ t = 2) (v : Fin t → ℝ) : (pathShift x t).toQuadraticForm' v ≤ 0 := by
  rcases ht with rfl | rfl
  · have hp := mul_nonpos_of_nonpos_of_nonneg (show x ≤ 0 by linarith) (sq_nonneg (v 0))
    simpa [quadratic_apply, pathShift, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, pow_two, mul_left_comm, mul_assoc] using hp
  · have hp := mul_nonpos_of_nonpos_of_nonneg (show x + 1 ≤ 0 by linarith)
      (add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v 1)))
    simp [quadratic_apply, pathShift, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 + v 1)]
#print axioms Paper7Lemma21.pathShift_nonpositive

theorem pendant_quadratic_sum (b : ℕ) (L : Fin b → List ℕ) (x : ℝ)
    (v : ArmV b L → ℝ) :
    (pendantShift b L x).toQuadraticForm' v =
      ∑ k : Fin b, ∑ j : Fin (L k).length,
        (pathShift x ((L k).get j)).toQuadraticForm' (fun i => v ⟨k,j,i⟩) := by
  simp only [quadratic_apply, dotProduct, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold pendantShift
  rw [blockDiagonal_mulVec, blockDiagonal_mulVec]
#print axioms Paper7Lemma21.pendant_quadratic_sum

theorem pendant_inertia_sign (b : ℕ) (p q : Fin b → ℕ) (x : ℝ) :
    (1 < x → nNeg (pendantShift b (pq b p q) x) = 0) ∧
      (x < -1 → nPos (pendantShift b (pq b p q) x) = 0) := by
  constructor
  · intro hx
    apply nNeg_zero_of_nonnegative _ (pendantShift_isHermitian _ _ _)
    intro v
    rw [pendant_quadratic_sum]
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro j _
    exact pathShift_nonnegative x hx _ (pq_length_one_or_two b p q k j) _
  · intro hx
    apply nPos_zero_of_nonpositive _ (pendantShift_isHermitian _ _ _)
    intro v
    rw [pendant_quadratic_sum]
    apply Finset.sum_nonpos
    intro k _
    apply Finset.sum_nonpos
    intro j _
    exact pathShift_nonpositive x hx _ (pq_length_one_or_two b p q k j) _
#print axioms Paper7Lemma21.pendant_inertia_sign

theorem ordinary_shift_inertia (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (x : ℝ) (hx0 : x ≠ 0) (hxq : x ^ 2 - 1 ≠ 0) :
    Ngt (SG b p q) x = nPos (Smat b p q x) + nNeg (pendantShift b (pq b p q) x) ∧
    Nlt (SG b p q) x = nNeg (Smat b p q x) + nPos (pendantShift b (pq b p q) x) := by
  let D := pendantShift (K := ℝ) b (pq b p q) x
  let B := attachment (K := ℝ) b (pq b p q)
  let A := cycleShift b x
  let : Invertible D := Matrix.invertibleOfIsUnitDet _
    (pendantShift_isUnit_det b p q x hx0 hxq)
  have hA : A.IsHermitian := by
    change (cycleShift b x).IsHermitian
    rw [cycleShift, Matrix.smul_one_eq_diagonal]
    exact (Matrix.isHermitian_diagonal _).sub
      ((SimpleGraph.cycleGraph b).isHermitian_adjMatrix ℝ)
  have hD : D.IsHermitian := pendantShift_isHermitian _ _ _
  have hi := schur_inertia A B D hA hD
  have hs : A - B * D⁻¹ * Bᵀ = -(Smat b p q x) := by
    change cycleShift b x - attachment b (pq b p q) *
      (pendantShift (K := ℝ) b (pq b p q) x)⁻¹ * (attachment b (pq b p q)).transpose = _
    rw [attachment_inverse_coupling b p q x hx0 hxq]
    have hh := smat_eq_negative_schur b p q x
    simpa only [neg_one_smul, neg_neg] using (congrArg Neg.neg hh).symm
  have hm : Matrix.fromBlocks A B Bᵀ D =
      -((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) x) := by
    rw [show Matrix.fromBlocks A B Bᵀ D =
      x • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℝ) -
        (SG b p q).adjMatrix ℝ from (sun_shift_fromBlocks b (pq b p q) hb x).symm]
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    abel
  rw [hs, hm, nPos_neg _ (shifted_adj_isHermitian _ _),
    nNeg_neg _ (shifted_adj_isHermitian _ _),
    nPos_neg _ (smat_isHermitian _ _ _ _), nNeg_neg _ (smat_isHermitian _ _ _ _),
    nPos_shift_eq_Ngt, nNeg_shift_eq_Nlt] at hi
  exact ⟨hi.2, hi.1⟩
#print axioms Paper7Lemma21.ordinary_shift_inertia

theorem nZero_shift_eq_mult (G : SimpleGraph ι) [DecidableRel G.Adj] (x : ℝ) :
    nZero (G.adjMatrix ℝ - Matrix.scalar ι x) = mult G x := by
  rw [nZero, eigs_real_shift]
  have h := Multiset.count_map_eq_count' (fun y : ℝ => y - x)
    (eigs (G.adjMatrix ℝ)) (fun a b hab => by linarith) x
  simpa only [sub_self, mult, spec] using h
#print axioms Paper7Lemma21.nZero_shift_eq_mult

theorem ordinary_nZero (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (x : ℝ) (hxn : x ≠ -1) (hx0 : x ≠ 0) (hxp : x ≠ 1) :
    nZero ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) x) =
      nZero (Smat b p q x) := by
  rw [nZero_shift_eq_mult, ordinary_mult_eq_smat_nullity b p q hb x hxn hx0 hxp]
  have h := Paper7Spectrum.realHermitian_count_eq_shift_nullity
    (Smat b p q x) (smat_isHermitian b p q x) 0
  simpa [nZero, eigs] using h.symm
#print axioms Paper7Lemma21.ordinary_nZero

theorem lemma21_ordinary (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    (∀ x : ℝ, 1 < x → Ngt (SG b p q) x = nPos (Smat b p q x) ∧
      Nge (SG b p q) x = nPos (Smat b p q x) + nZero (Smat b p q x)) ∧
    (∀ x : ℝ, x < -1 → Nlt (SG b p q) x = nNeg (Smat b p q x) ∧
      Nle (SG b p q) x = nNeg (Smat b p q x) + nZero (Smat b p q x)) := by
  constructor
  · intro x hx
    have hxn : x ≠ -1 := by linarith
    have hx0 : x ≠ 0 := by linarith
    have hxp : x ≠ 1 := by linarith
    have hi := (ordinary_shift_inertia b p q hb x hx0
      (square_sub_one_ne_zero x hxn hxp)).1
    rw [(pendant_inertia_sign b p q x).1 hx, add_zero] at hi
    refine ⟨hi, ?_⟩
    rw [← nonneg_shift_eq_Nge, nPos_shift_eq_Ngt,
      ordinary_nZero b p q hb x hxn hx0 hxp, hi]
  · intro x hx
    have hxn : x ≠ -1 := by linarith
    have hx0 : x ≠ 0 := by linarith
    have hxp : x ≠ 1 := by linarith
    have hi := (ordinary_shift_inertia b p q hb x hx0
      (square_sub_one_ne_zero x hxn hxp)).2
    rw [(pendant_inertia_sign b p q x).2 hx, add_zero] at hi
    refine ⟨hi, ?_⟩
    rw [← nonpos_shift_eq_Nle, nNeg_shift_eq_Nlt,
      ordinary_nZero b p q hb x hxn hx0 hxp, hi]
#print axioms Paper7Lemma21.lemma21_ordinary

end Paper7Lemma21
