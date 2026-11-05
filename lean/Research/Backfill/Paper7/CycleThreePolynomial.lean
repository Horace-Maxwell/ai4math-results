import Research.Backfill.Paper7.ClearedCharacteristicPolynomial

/-! The actual three-cycle determinant, with symbolic parameters and no
integer-spectrum assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open scoped Matrix
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

def triangleDiagonal (p q : ℕ) : Polynomial ℤ :=
  X ^ 4 - C (1 + (p : ℤ) + q) * X ^ 2 + C (p : ℤ)
#print axioms Paper7CycleThree.triangleDiagonal

def triangleEdge : Polynomial ℤ := X * (X ^ 2 - 1)
#print axioms Paper7CycleThree.triangleEdge

def trianglePolynomial (p q : Fin 3 → ℕ) : Polynomial ℤ :=
  triangleDiagonal (p 0) (q 0) * triangleDiagonal (p 1) (q 1) *
      triangleDiagonal (p 2) (q 2) -
    triangleEdge ^ 2 * (triangleDiagonal (p 0) (q 0) +
      triangleDiagonal (p 1) (q 1) + triangleDiagonal (p 2) (q 2)) -
    2 * triangleEdge ^ 3
#print axioms Paper7CycleThree.trianglePolynomial

theorem triangle_cleared_matrix (p q : Fin 3 → ℕ) :
    clearedMatrix 3 p q =
      !![triangleDiagonal (p 0) (q 0), -triangleEdge, -triangleEdge;
         -triangleEdge, triangleDiagonal (p 1) (q 1), -triangleEdge;
         -triangleEdge, -triangleEdge, triangleDiagonal (p 2) (q 2)] := by
  have hA : cycleAdjZ 3 =
      (!![0,1,1; 1,0,1; 1,1,0] : Matrix (Fin 3) (Fin 3) ℤ) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cycleAdjZ, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;>
      decide
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, hA, triangleDiagonal, triangleEdge] <;> ring
#print axioms Paper7CycleThree.triangle_cleared_matrix

theorem triangle_clearedF (p q : Fin 3 → ℕ) :
    clearedF 3 p q = trianglePolynomial p q := by
  have hm : clearedMatrix 3 p q = Matrix.of
      (!![triangleDiagonal (p 0) (q 0), -triangleEdge, -triangleEdge;
         -triangleEdge, triangleDiagonal (p 1) (q 1), -triangleEdge;
         -triangleEdge, -triangleEdge, triangleDiagonal (p 2) (q 2)] :
        Matrix (Fin 3) (Fin 3) (Polynomial ℤ)) := triangle_cleared_matrix p q
  rw [clearedF, hm, Matrix.det_fin_three]
  change triangleDiagonal (p 0) (q 0) * triangleDiagonal (p 1) (q 1) *
      triangleDiagonal (p 2) (q 2) -
    triangleDiagonal (p 0) (q 0) * (-triangleEdge) * (-triangleEdge) -
    (-triangleEdge) * (-triangleEdge) * triangleDiagonal (p 2) (q 2) +
    (-triangleEdge) * (-triangleEdge) * (-triangleEdge) +
    (-triangleEdge) * (-triangleEdge) * (-triangleEdge) -
    (-triangleEdge) * triangleDiagonal (p 1) (q 1) * (-triangleEdge) = trianglePolynomial p q
  unfold trianglePolynomial
  ring
#print axioms Paper7CycleThree.triangle_clearedF

theorem triangle_monic_degree (p q : Fin 3 → ℕ) :
    (trianglePolynomial p q).Monic ∧ (trianglePolynomial p q).natDegree = 12 := by
  have h := (Paper7Cleared.check_ClearedCharacteristicPolynomial 3 p q (by omega)).2
  rw [triangle_clearedF] at h
  exact h
#print axioms Paper7CycleThree.triangle_monic_degree

theorem triangle_eval_neg_sub {K : Type*} [CommRing K]
    (f : ℤ →+* K) (p q : Fin 3 → ℕ) (x : K) :
    (trianglePolynomial p q).eval₂ f x - (trianglePolynomial p q).eval₂ f (-x) =
      -4 * x ^ 3 * (x ^ 2 - 1) ^ 3 := by
  simp only [trianglePolynomial, triangleDiagonal, triangleEdge,
    Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
  ring
#print axioms Paper7CycleThree.triangle_eval_neg_sub

end Paper7CycleThree
