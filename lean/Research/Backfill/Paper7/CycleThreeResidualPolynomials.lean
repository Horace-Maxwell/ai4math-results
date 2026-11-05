import Research.Backfill.Paper7.CycleThreePolynomial

/-! Exact symbolic factor removal in all three remaining support strata.
These are identities of the actual triangle polynomial, with zero parameters allowed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial BackfillPaper7.Challenge
open scoped BigOperators

def triangleResidualNoQ (p : Fin 3 → ℕ) : Polynomial ℤ :=
  (X ^ 2 - C (p 0 : ℤ)) * (X ^ 2 - C (p 1 : ℤ)) * (X ^ 2 - C (p 2 : ℤ)) -
    X ^ 2 * ((X ^ 2 - C (p 0 : ℤ)) + (X ^ 2 - C (p 1 : ℤ)) +
      (X ^ 2 - C (p 2 : ℤ))) - 2 * X ^ 3
#print axioms Paper7CycleThree.triangleResidualNoQ

def triangleResidualOneQ (p : Fin 3 → ℕ) (q0 : ℕ) : Polynomial ℤ :=
  triangleDiagonal (p 0) q0 * (X ^ 2 - C (p 1 : ℤ)) * (X ^ 2 - C (p 2 : ℤ)) -
    X ^ 2 * (triangleDiagonal (p 0) q0 + (X ^ 2 - 1) *
      ((X ^ 2 - C (p 1 : ℤ)) + (X ^ 2 - C (p 2 : ℤ)))) -
    2 * X ^ 3 * (X ^ 2 - 1)
#print axioms Paper7CycleThree.triangleResidualOneQ

/-- The zero p lies away from the zero q site: p0=0, q2=0. -/
def triangleResidualOffZero (p1 p2 q0 q1 : ℕ) : Polynomial ℤ :=
  (X ^ 2 - C (1 + (q0 : ℤ))) * triangleDiagonal p1 q1 * (X ^ 2 - C (p2 : ℤ)) -
    (X ^ 2 - 1) * (X ^ 2 * (X ^ 2 - C (1 + (q0 : ℤ))) +
      triangleDiagonal p1 q1 + (X ^ 2 - 1) * (X ^ 2 - C (p2 : ℤ))) -
    2 * X * (X ^ 2 - 1) ^ 2
#print axioms Paper7CycleThree.triangleResidualOffZero

/-- The zero p and zero q lie at the same site: p2=q2=0. -/
def triangleResidualAtZero (p0 p1 q0 q1 : ℕ) : Polynomial ℤ :=
  triangleDiagonal p0 q0 * triangleDiagonal p1 q1 -
    (X ^ 2 - 1) * (triangleDiagonal p0 q0 + triangleDiagonal p1 q1 +
      X ^ 2 * (X ^ 2 - 1)) - 2 * X * (X ^ 2 - 1) ^ 2
#print axioms Paper7CycleThree.triangleResidualAtZero

theorem triangle_noQ_factor (p q : Fin 3 → ℕ) (hq : ∀ i, q i = 0) :
    trianglePolynomial p q = (X ^ 2 - 1) ^ 3 * triangleResidualNoQ p := by
  simp [trianglePolynomial, triangleDiagonal, triangleEdge, triangleResidualNoQ, hq]
  ring
#print axioms Paper7CycleThree.triangle_noQ_factor

theorem triangle_oneQ_factor (p q : Fin 3 → ℕ) (hq1 : q 1 = 0) (hq2 : q 2 = 0) :
    trianglePolynomial p q = (X ^ 2 - 1) ^ 2 * triangleResidualOneQ p (q 0) := by
  simp [trianglePolynomial, triangleDiagonal, triangleEdge, triangleResidualOneQ, hq1, hq2]
  ring
#print axioms Paper7CycleThree.triangle_oneQ_factor

theorem triangle_offZero_factor (p q : Fin 3 → ℕ) (hp0 : p 0 = 0) (hq2 : q 2 = 0) :
    trianglePolynomial p q = X ^ 2 * (X ^ 2 - 1) *
      triangleResidualOffZero (p 1) (p 2) (q 0) (q 1) := by
  simp [trianglePolynomial, triangleDiagonal, triangleEdge, triangleResidualOffZero, hp0, hq2]
  ring
#print axioms Paper7CycleThree.triangle_offZero_factor

theorem triangle_atZero_factor (p q : Fin 3 → ℕ) (hp2 : p 2 = 0) (hq2 : q 2 = 0) :
    trianglePolynomial p q = X ^ 2 * (X ^ 2 - 1) *
      triangleResidualAtZero (p 0) (p 1) (q 0) (q 1) := by
  simp [trianglePolynomial, triangleDiagonal, triangleEdge, triangleResidualAtZero, hp2, hq2]
  ring
#print axioms Paper7CycleThree.triangle_atZero_factor

theorem triangle_prod_sum (p q : Fin 3 → ℕ) :
    trianglePolynomial p q = (∏ i, triangleDiagonal (p i) (q i)) -
      triangleEdge ^ 2 * (∑ i, triangleDiagonal (p i) (q i)) - 2 * triangleEdge ^ 3 := by
  rw [Fin.prod_univ_three, Fin.sum_univ_three]
  rfl
#print axioms Paper7CycleThree.triangle_prod_sum

theorem trianglePolynomial_permute (p q : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3)) :
    trianglePolynomial (fun i => p (e i)) (fun i => q (e i)) = trianglePolynomial p q := by
  rw [triangle_prod_sum, triangle_prod_sum]
  rw [Equiv.prod_comp e (fun i => triangleDiagonal (p i) (q i)),
    Equiv.sum_comp e (fun i => triangleDiagonal (p i) (q i))]
#print axioms Paper7CycleThree.trianglePolynomial_permute

theorem triangle_nOf_permute (p q : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3)) :
    nOf 3 (fun i => p (e i)) (fun i => q (e i)) = nOf 3 p q := by
  unfold nOf
  rw [Equiv.sum_comp e p, Equiv.sum_comp e q]
#print axioms Paper7CycleThree.triangle_nOf_permute

end Paper7CycleThree
