import Research.Backfill.Paper7.SunPendantAssembly

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open BackfillPaper7.Challenge

def endpointCorrection {K : Type*} [Field K] (x : K) (t : ℕ) : K :=
  ∑ a : Fin t, (∑ c : Fin t, if c.val = 0 then -pathInverse x t c a else 0) *
    (if a.val = 0 then -1 else 0)

#print axioms Paper7Cleared.endpointCorrection

theorem attachment_mul_pendantInverse_entry {K : Type*} [Field K]
    (b : ℕ) (L : Fin b → List ℕ) (x : K) (u k : Fin b)
    (j : Fin (L k).length) (a : Fin ((L k).get j)) :
    ((attachment (K := K) b L * pendantInverse (K := K) b L x :
      Matrix (Fin b) (ArmV b L) K)) u ⟨k, j, a⟩ =
      if k = u then (∑ c : Fin ((L k).get j),
        if c.val = 0 then -pathInverse x ((L k).get j) c a else 0) else 0 := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · rw [Fintype.sum_eq_single j]
    · simp only [pendantInverse, Matrix.blockDiagonal'_apply_eq]
      by_cases hk : k = u
      · rw [ite_eq_left hk]
        apply Finset.sum_congr rfl
        intro c _hc
        simp only [attachment]
        by_cases hpos : c.val = 0
        · rw [ite_eq_left ⟨hk, hpos⟩, ite_eq_left hpos]
          exact neg_one_mul _
        · rw [ite_eq_right (show ¬(k = u ∧ c.val = 0) from fun h => hpos h.2),
            ite_eq_right hpos, zero_mul]
      · rw [ite_eq_right hk]
        apply Finset.sum_eq_zero
        intro c _hc
        simp only [attachment]
        rw [ite_eq_right (show ¬(k = u ∧ c.val = 0) from fun h => hk h.1), zero_mul]
    · intro j' hj'
      apply Finset.sum_eq_zero
      intro c _hc
      rw [show pendantInverse (K := K) b L x ⟨k, j', c⟩ ⟨k, j, a⟩ = 0 by
        unfold pendantInverse
        rw [Matrix.blockDiagonal'_apply_eq]
        exact Matrix.blockDiagonal'_apply_ne _ _ _ hj']
      exact mul_zero _
  · intro k' hk'
    apply Finset.sum_eq_zero
    intro j' _hj'
    apply Finset.sum_eq_zero
    intro c _hc
    rw [show pendantInverse (K := K) b L x ⟨k', j', c⟩ ⟨k, j, a⟩ = 0 by
      unfold pendantInverse
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hk']
    exact mul_zero _

#print axioms Paper7Cleared.attachment_mul_pendantInverse_entry

theorem attachment_pendantInverse_contraction {K : Type*} [Field K]
    (b : ℕ) (L : Fin b → List ℕ) (x : K) :
    (((attachment (K := K) b L * pendantInverse (K := K) b L x :
        Matrix (Fin b) (ArmV b L) K) * (attachment (K := K) b L).transpose) :
      Matrix (Fin b) (Fin b) K) =
      Matrix.diagonal (fun u : Fin b => ∑ j : Fin (L u).length,
        endpointCorrection x ((L u).get j)) := by
  classical
  ext u v
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single v]
  · by_cases huv : u = v
    · subst v
      simp only [attachment_mul_pendantInverse_entry, eq_self, ite_true,
        Matrix.transpose_apply, attachment, true_and, Matrix.diagonal_apply_eq,
        endpointCorrection]
    · have hvu : v ≠ u := Ne.symm huv
      simp [attachment_mul_pendantInverse_entry, hvu, huv]
  · intro k hk
    apply Finset.sum_eq_zero
    intro j _hj
    apply Finset.sum_eq_zero
    intro a _ha
    have hz : (attachment (K := K) b L).transpose ⟨k, j, a⟩ v = 0 := by
      simp [Matrix.transpose_apply, attachment, hk]
    rw [hz, mul_zero]

#print axioms Paper7Cleared.attachment_pendantInverse_contraction

theorem endpointCorrection_eq {K : Type*} [Field K] (x : K) (t : ℕ)
    (ht : t = 1 ∨ t = 2) :
    endpointCorrection x t = if t = 1 then x⁻¹ else x / (x ^ 2 - 1) := by
  rcases ht with rfl | rfl <;>
    simp [endpointCorrection, pathInverse]

#print axioms Paper7Cleared.endpointCorrection_eq

theorem endpointCorrection_sum {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (k : Fin b) :
    (∑ j : Fin ((pq b p q k).length), endpointCorrection x ((pq b p q k).get j)) =
      (p k : K) / x + (q k : K) * x / (x ^ 2 - 1) := by
  calc
    _ = ∑ j : Fin ((pq b p q k).length),
        if (pq b p q k).get j = 1 then x⁻¹ else x / (x ^ 2 - 1) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact endpointCorrection_eq x _ (pq_length_one_or_two b p q k j)
    _ = ((pq b p q k).map (fun t => if t = 1 then x⁻¹ else x / (x ^ 2 - 1))).sum := by
      change (∑ j : Fin ((pq b p q k).length),
        (fun t => if t = 1 then x⁻¹ else x / (x ^ 2 - 1)) (pq b p q k)[j.val]) = _
      exact Fin.sum_univ_fun_getElem (M := K) (pq b p q k)
        (fun t : ℕ => if t = 1 then x⁻¹ else x / (x ^ 2 - 1))
    _ = _ := by simp [pq, nsmul_eq_mul, div_eq_mul_inv, mul_assoc]

#print axioms Paper7Cleared.endpointCorrection_sum

theorem attachment_inverse_coupling {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    (((attachment (K := K) b (pq b p q) * (pendantShift (K := K) b (pq b p q) x)⁻¹ :
        Matrix (Fin b) (ArmV b (pq b p q)) K) *
          (attachment (K := K) b (pq b p q)).transpose) : Matrix (Fin b) (Fin b) K) =
      Matrix.diagonal (fun k : Fin b => (p k : K) / x + (q k : K) * x / (x ^ 2 - 1)) := by
  rw [pendantShift_nonsing_inverse b p q x hx hquad,
    attachment_pendantInverse_contraction]
  congr 1
  funext k
  exact endpointCorrection_sum b p q x k

#print axioms Paper7Cleared.attachment_inverse_coupling

end Paper7Cleared
