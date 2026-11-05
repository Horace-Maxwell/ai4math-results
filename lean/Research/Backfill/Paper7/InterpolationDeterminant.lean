import Research.Backfill.Paper7.ChallengeV3

/-! The interpolation specialization only needs an upper degree bound. It is
proved directly from the frozen matrix, independently of the still separate
characteristic-polynomial identity and its monicity/exact-degree claims. -/

set_option autoImplicit false

open Polynomial Finset
open BackfillPaper7.Challenge.Legacy.Algebra

namespace Paper7Interpolation

theorem clearedMatrix_entry_natDegree_le (b : ℕ) (p q : Fin b → ℕ) (i j : Fin b) :
    (clearedMatrix b p q i j).natDegree ≤ 4 := by
  classical
  unfold clearedMatrix
  split_ifs <;> compute_degree
  norm_num

theorem clearedF_natDegree_le (b : ℕ) (p q : Fin b → ℕ) :
    (clearedF b p q).natDegree ≤ 4 * b := by
  classical
  unfold clearedF
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i : Fin b, clearedMatrix b p q (σ i) i).natDegree ≤
        (∏ i : Fin b, clearedMatrix b p q (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
      · rw [hσ, one_smul]
      · rw [hσ, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i : Fin b, (clearedMatrix b p q (σ i) i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin b, 4 :=
      Finset.sum_le_sum fun i _ => clearedMatrix_entry_natDegree_le b p q (σ i) i
    _ = 4 * b := by simp [Nat.mul_comm]

theorem reduce_clearedF_natDegree_le (ℓ b : ℕ) (p q : Fin b → ℕ) :
    (reducePolynomial ℓ (clearedF b p q)).natDegree ≤ 4 * b :=
  (Polynomial.natDegree_map_le).trans (clearedF_natDegree_le b p q)

/-- Evaluation after coefficient reduction is a ring homomorphism, so it
commutes with the actual determinant for every sample index, not only the
interpolation indices. -/
theorem determinantSample_eq_eval (ℓ b : ℕ) (p q : Fin b → ℕ) (i : ℕ) :
    determinantSample ℓ b p q i =
      (reducePolynomial ℓ (clearedF b p q)).eval (interpolationNode ℓ i) := by
  let E : Polynomial ℤ →+* ZMod ℓ :=
    (Polynomial.evalRingHom (interpolationNode ℓ i)).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ)))
  change ((clearedMatrix b p q).map E).det = E (clearedMatrix b p q).det
  exact (E.map_det (clearedMatrix b p q)).symm

end Paper7Interpolation

#print axioms Paper7Interpolation.clearedMatrix_entry_natDegree_le
#print axioms Paper7Interpolation.clearedF_natDegree_le
#print axioms Paper7Interpolation.reduce_clearedF_natDegree_le
#print axioms Paper7Interpolation.determinantSample_eq_eval
