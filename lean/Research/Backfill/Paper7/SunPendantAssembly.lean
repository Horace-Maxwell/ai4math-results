import Research.Backfill.Paper7.PathBlockResolvent
import Research.Backfill.Paper7.DependentBlockDet
import Research.Backfill.Paper7.SunPQCardinality

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem pq_length_one_or_two (b : ℕ) (p q : Fin b → ℕ) (k : Fin b)
    (j : Fin ((pq b p q k).length)) :
    (pq b p q k).get j = 1 ∨ (pq b p q k).get j = 2 := by
  have hm : (pq b p q k).get j ∈ pq b p q k := List.getElem_mem j.isLt
  change (pq b p q k).get j ∈ List.replicate (p k) 1 ++ List.replicate (q k) 2 at hm
  rcases List.mem_append.mp hm with h | h
  · exact Or.inl (List.eq_of_mem_replicate h)
  · exact Or.inr (List.eq_of_mem_replicate h)

#print axioms Paper7Cleared.pq_length_one_or_two

def pendantInverse {K : Type*} [Field K] (b : ℕ) (L : Fin b → List ℕ) (x : K) :
    Matrix (ArmV b L) (ArmV b L) K :=
  Matrix.blockDiagonal' fun k => Matrix.blockDiagonal' fun j => pathInverse x ((L k).get j)

#print axioms Paper7Cleared.pendantInverse

theorem path_determinants_product {K : Type*} [CommRing K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (k : Fin b) :
    (∏ j : Fin ((pq b p q k).length), (pathShift x ((pq b p q k).get j)).det) =
      x ^ p k * (x ^ 2 - 1) ^ q k := by
  calc
    _ = ∏ j : Fin ((pq b p q k).length),
        if (pq b p q k).get j = 1 then x else x ^ 2 - 1 := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact pathShift_det x _ (pq_length_one_or_two b p q k j)
    _ = ((pq b p q k).map (fun t => if t = 1 then x else x ^ 2 - 1)).prod := by
      change (∏ j : Fin ((pq b p q k).length),
        (fun t => if t = 1 then x else x ^ 2 - 1) (pq b p q k)[j.val]) = _
      exact Fin.prod_univ_fun_getElem (M := K) (pq b p q k)
        (fun t : ℕ => if t = 1 then x else x ^ 2 - 1)
    _ = _ := by simp [pq]

#print axioms Paper7Cleared.path_determinants_product

theorem pendantShift_det {K : Type*} [CommRing K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) :
    (pendantShift b (pq b p q) x).det =
      x ^ totalP b p * (x ^ 2 - 1) ^ totalQ b q := by
  unfold pendantShift
  rw [det_blockDiagonal']
  simp_rw [det_blockDiagonal', path_determinants_product]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rfl

#print axioms Paper7Cleared.pendantShift_det

theorem pendantInverse_mul_shift {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    pendantInverse b (pq b p q) x * pendantShift b (pq b p q) x = 1 := by
  have hinner (k : Fin b) :
      (Matrix.blockDiagonal' fun j : Fin ((pq b p q k).length) =>
        pathInverse x ((pq b p q k).get j)) *
      (Matrix.blockDiagonal' fun j : Fin ((pq b p q k).length) =>
        pathShift x ((pq b p q k).get j)) = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    have hf : (fun j : Fin ((pq b p q k).length) =>
        pathInverse x ((pq b p q k).get j) * pathShift x ((pq b p q k).get j)) =
        (fun j : Fin ((pq b p q k).length) =>
          (1 : Matrix (Fin ((pq b p q k).get j)) (Fin ((pq b p q k).get j)) K)) := by
      funext j
      exact pathInverse_mul_shift x _ (pq_length_one_or_two b p q k j) hx hquad
    rw [hf]
    simpa only using! (Matrix.blockDiagonal'_one (α := K)
      (m' := fun j : Fin ((pq b p q k).length) => Fin ((pq b p q k).get j)))
  unfold pendantInverse pendantShift
  rw [← Matrix.blockDiagonal'_mul]
  simp_rw [hinner]
  simpa only using! (Matrix.blockDiagonal'_one (α := K)
    (m' := fun k : Fin b => Σ j : Fin ((pq b p q k).length),
      Fin ((pq b p q k).get j)))

#print axioms Paper7Cleared.pendantInverse_mul_shift

theorem pendantShift_nonsing_inverse {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    (pendantShift b (pq b p q) x)⁻¹ = pendantInverse b (pq b p q) x := by
  apply Matrix.inv_eq_left_inv
  exact pendantInverse_mul_shift b p q x hx hquad

#print axioms Paper7Cleared.pendantShift_nonsing_inverse

theorem pendantShift_isUnit_det {K : Type*} [Field K]
    (b : ℕ) (p q : Fin b → ℕ) (x : K) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    IsUnit (pendantShift b (pq b p q) x).det :=
  Matrix.isUnit_det_of_left_inverse (pendantInverse_mul_shift b p q x hx hquad)

#print axioms Paper7Cleared.pendantShift_isUnit_det

end Paper7Cleared
