import Research.Backfill.Paper7.BMS32Polynomial
import Research.Backfill.Paper7.SetupCardinality

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped Matrix

namespace Paper7Hexagon

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

def hexagonP (a : ℕ) : Fin 6 → ℕ := ![0, a, a, 2 * a, a, a]
#print axioms Paper7Hexagon.hexagonP

theorem hexagon_parameters (a : ℕ) :
    pq 6 (hexagonP a) (fun _ => 0) = HexagonFamily a := by
  funext k
  fin_cases k <;> simp [pq, hexagonP, HexagonFamily]
#print axioms Paper7Hexagon.hexagon_parameters

theorem hexagon_six_eq : HexagonFamily 6 = C61 := by
  funext k
  fin_cases k <;> rfl
#print axioms Paper7Hexagon.hexagon_six_eq

theorem hexagon_totalP (a : ℕ) : totalP 6 (hexagonP a) = 6 * a := by
  simp [totalP, hexagonP, Fin.sum_univ_succ]
  omega
#print axioms Paper7Hexagon.hexagon_totalP

theorem hexagon_order (a : ℕ) : order 6 (HexagonFamily a) = 6 + 6 * a := by
  have h := Paper7Setup.sg_order 6 (hexagonP a) (fun _ => 0)
  rw [hexagon_parameters] at h
  rw [h]
  simp [nOf, hexagonP, Fin.sum_univ_succ]
  omega
#print axioms Paper7Hexagon.hexagon_order

theorem hexagon_pendant_count (a : ℕ) : pendantCount 6 (HexagonFamily a) = 6 * a := by
  simp [pendantCount, HexagonFamily, Fin.sum_univ_succ]
  omega
#print axioms Paper7Hexagon.hexagon_pendant_count

def hexagonSmallMatrix (a : ℕ) : Matrix (Fin 6) (Fin 6) (Polynomial ℤ) :=
  !![X^2, -X, 0, 0, 0, -X;
     -X, X^2-C (a : ℤ), -X, 0, 0, 0;
     0, -X, X^2-C (a : ℤ), -X, 0, 0;
     0, 0, -X, X^2-2*C (a : ℤ), -X, 0;
     0, 0, 0, -X, X^2-C (a : ℤ), -X;
     -X, 0, 0, 0, -X, X^2-C (a : ℤ)]
#print axioms Paper7Hexagon.hexagonSmallMatrix

theorem hexagon_cleared_matrix (a : ℕ) :
    clearedMatrix 6 (hexagonP a) (fun _ => 0) =
      (X ^ 2 - 1 : Polynomial ℤ) • hexagonSmallMatrix a := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, Paper7BMS32.cycle_adjacency_six, hexagonP,
      hexagonSmallMatrix, Matrix.smul_apply, smul_eq_mul, map_mul] <;> ring
#print axioms Paper7Hexagon.hexagon_cleared_matrix

theorem hexagon_small_det (a : ℕ) :
    (hexagonSmallMatrix a).det =
      X ^ 2 * (X ^ 2 - C (2 * (a : ℤ) + 4)) *
        ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2 := by
  rw [hexagonSmallMatrix, Paper7BMS32.det_six_reflection]
  simp only [map_add, map_mul, Polynomial.C_ofNat]
  ring
#print axioms Paper7Hexagon.hexagon_small_det

theorem hexagon_cleared_factorization (a : ℕ) :
    clearedF 6 (hexagonP a) (fun _ => 0) =
      (X ^ 2 - 1) ^ 6 *
        (X ^ 2 * (X ^ 2 - C (2 * (a : ℤ) + 4)) *
          ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2) := by
  rw [clearedF, hexagon_cleared_matrix, Matrix.det_smul, Fintype.card_fin, hexagon_small_det]
#print axioms Paper7Hexagon.hexagon_cleared_factorization

theorem hexagon_reassociation {R : Type*} [CommRing R] (a : ℕ) (ha : 1 ≤ a)
    (x y f : R) :
    x ^ (6 * a) * (y ^ 6 * (x ^ 2 * f)) =
      (x ^ 6 * y ^ 6) * (x ^ (6 * a - 4) * f) := by
  have hpow : x ^ (6 * a) * x ^ 2 = x ^ 6 * x ^ (6 * a - 4) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = (x ^ (6 * a) * x ^ 2) * (y ^ 6 * f) := by ring
    _ = (x ^ 6 * x ^ (6 * a - 4)) * (y ^ 6 * f) := by rw [hpow]
    _ = _ := by ring
#print axioms Paper7Hexagon.hexagon_reassociation

/-- Full characteristic polynomial of the original frozen six-cycle family. -/
theorem hexagon_graphPhi (a : ℕ) (ha : 1 ≤ a) :
    graphPhi (sunGraph 6 (HexagonFamily a)) =
      X ^ (6 * a - 4) * (X ^ 2 - C (2 * (a : ℤ) + 4)) *
        ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2 := by
  have hid := Paper7Cleared.cleared_identity 6 (hexagonP a) (fun _ => 0) (by decide)
  rw [hexagon_totalP, show totalQ 6 (fun _ => 0) = 0 by simp [totalQ],
    hexagon_cleared_factorization] at hid
  simp only [pow_zero, mul_one] at hid
  have hn : (X ^ 6 * (X ^ 2 - 1) ^ 6 : Polynomial ℤ) ≠ 0 :=
    (Paper7Cleared.monic_denominator_factor 6 6).ne_zero
  have hsg : graphPhi (SG 6 (hexagonP a) (fun _ => 0)) =
      X ^ (6 * a - 4) * (X ^ 2 - C (2 * (a : ℤ) + 4)) *
        ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2 := by
    apply mul_left_cancel₀ hn
    calc
      (X ^ 6 * (X ^ 2 - 1) ^ 6) * graphPhi (SG 6 (hexagonP a) (fun _ => 0)) =
          X ^ (6 * a) * ((X ^ 2 - 1) ^ 6 *
            (X ^ 2 * (X ^ 2 - C (2 * (a : ℤ) + 4)) *
              ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2)) := hid.symm
      _ = (X ^ 6 * (X ^ 2 - 1) ^ 6) *
          (X ^ (6 * a - 4) * (X ^ 2 - C (2 * (a : ℤ) + 4)) *
            ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2) := by
        have h := hexagon_reassociation a ha X (X ^ 2 - 1)
          ((X ^ 2 - C (2 * (a : ℤ) + 4)) * ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2)
        simpa only [mul_assoc] using h
  exact (congrArg
    (fun L : Fin 6 → List ℕ => graphPhi (sunGraph 6 L))
    (hexagon_parameters a)).symm.trans hsg
#print axioms Paper7Hexagon.hexagon_graphPhi

end Paper7Hexagon
