import Research.Backfill.Paper7.ThreeRepresentativesBridge

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped Matrix

namespace Paper7Veras

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

def verasP (a : ℕ) : Fin 4 → ℕ := ![0, a, 2 * a, a]
#print axioms Paper7Veras.verasP

theorem veras_parameters (a : ℕ) :
    pq 4 (verasP a) (fun _ => 0) = VerasSquare a := by
  funext k
  fin_cases k <;> simp [pq, verasP, VerasSquare]
#print axioms Paper7Veras.veras_parameters

theorem veras_totalP (a : ℕ) : totalP 4 (verasP a) = 4 * a := by
  simp [totalP, verasP, Fin.sum_univ_succ]
  omega
#print axioms Paper7Veras.veras_totalP

theorem veras_order (a : ℕ) : order 4 (VerasSquare a) = 4 + 4 * a := by
  have h := Paper7Setup.sg_order 4 (verasP a) (fun _ => 0)
  rw [veras_parameters] at h
  rw [h]
  simp [nOf, verasP, Fin.sum_univ_succ]
  omega
#print axioms Paper7Veras.veras_order

theorem veras_pendant_count (a : ℕ) : pendantCount 4 (VerasSquare a) = 4 * a := by
  simp [pendantCount, VerasSquare, Fin.sum_univ_succ]
  omega
#print axioms Paper7Veras.veras_pendant_count

def verasSmallMatrix (a : ℕ) : Matrix (Fin 4) (Fin 4) (Polynomial ℤ) :=
  !![X^2, -X, 0, -X;
     -X, X^2-C (a : ℤ), -X, 0;
     0, -X, X^2-2*C (a : ℤ), -X;
     -X, 0, -X, X^2-C (a : ℤ)]
#print axioms Paper7Veras.verasSmallMatrix

theorem veras_cleared_matrix (a : ℕ) :
    clearedMatrix 4 (verasP a) (fun _ => 0) =
      (X ^ 2 - 1 : Polynomial ℤ) • verasSmallMatrix a := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, Paper7ThreeRepresentatives.cycle_adjacency_four,
      verasP, verasSmallMatrix, Matrix.smul_apply, smul_eq_mul, map_mul] <;> ring
#print axioms Paper7Veras.veras_cleared_matrix

theorem veras_small_det (a : ℕ) :
    (verasSmallMatrix a).det =
      X ^ 2 * (X ^ 2 - C (a : ℤ)) ^ 2 * (X ^ 2 - C (2 * (a : ℤ) + 4)) := by
  rw [verasSmallMatrix, Paper7ThreeRepresentatives.det_cycle_diagonal]
  simp only [map_add, map_mul, Polynomial.C_ofNat]
  ring
#print axioms Paper7Veras.veras_small_det

theorem veras_cleared_factorization (a : ℕ) :
    clearedF 4 (verasP a) (fun _ => 0) =
      (X ^ 2 - 1) ^ 4 *
        (X ^ 2 * (X ^ 2 - C (a : ℤ)) ^ 2 * (X ^ 2 - C (2 * (a : ℤ) + 4))) := by
  rw [clearedF, veras_cleared_matrix, Matrix.det_smul, Fintype.card_fin, veras_small_det]
#print axioms Paper7Veras.veras_cleared_factorization

theorem veras_reassociation {R : Type*} [CommRing R] (a : ℕ) (ha : 1 ≤ a)
    (x y f : R) :
    x ^ (4 * a) * (y ^ 4 * (x ^ 2 * f)) =
      (x ^ 4 * y ^ 4) * (x ^ (4 * a - 2) * f) := by
  have hpow : x ^ (4 * a) * x ^ 2 = x ^ 4 * x ^ (4 * a - 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = (x ^ (4 * a) * x ^ 2) * (y ^ 4 * f) := by ring
    _ = (x ^ 4 * x ^ (4 * a - 2)) * (y ^ 4 * f) := by rw [hpow]
    _ = _ := by ring
#print axioms Paper7Veras.veras_reassociation

/-- The complete characteristic polynomial of the original frozen graph. -/
theorem veras_graphPhi (a : ℕ) (ha : 1 ≤ a) :
    graphPhi (sunGraph 4 (VerasSquare a)) =
      X ^ (4 * a - 2) * (X ^ 2 - C (a : ℤ)) ^ 2 *
        (X ^ 2 - C (2 * (a : ℤ) + 4)) := by
  have hsg : graphPhi (SG 4 (verasP a) (fun _ => 0)) =
      X ^ (4 * a - 2) * (X ^ 2 - C (a : ℤ)) ^ 2 *
        (X ^ 2 - C (2 * (a : ℤ) + 4)) := by
    apply Paper7ThreeRepresentatives.graphPhi_of_cleared_four
    rw [veras_totalP, show totalQ 4 (fun _ => 0) = 0 by simp [totalQ],
      veras_cleared_factorization]
    simp only [pow_zero, mul_one]
    have h := veras_reassociation a ha X (X ^ 2 - 1)
      ((X ^ 2 - C (a : ℤ)) ^ 2 * (X ^ 2 - C (2 * (a : ℤ) + 4)))
    simpa only [mul_assoc] using h
  exact (congrArg
    (fun L : Fin 4 → List ℕ => graphPhi (sunGraph 4 L))
    (veras_parameters a)).symm.trans hsg
#print axioms Paper7Veras.veras_graphPhi

end Paper7Veras
