import Research.Backfill.Paper7.WeightedPathDeterminant
import Research.Backfill.Paper7.SchwenkChainAlgebra

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

theorem map_legPolynomial {K : Type*} [CommRing K]
    (f : Polynomial ℤ →+* K) (p q : ℕ) :
    f (legPolynomial p q) = (f X)^p * ((f X)^2-1)^q := by
  simp only [legPolynomial, map_mul, map_pow, map_sub, map_one]
#print axioms Paper7Schwenk.map_legPolynomial

theorem map_rootedLegPolynomial {K : Type*} [Field K]
    (f : Polynomial ℤ →+* K) (hx : f X ≠ 0) (hquad : (f X)^2-1 ≠ 0)
    (p q : ℕ) :
    f (rootedLegPolynomial p q) = f (legPolynomial p q) *
      (f X - (p : K) / f X - (q : K) * f X / ((f X)^2-1)) := by
  have h := congrArg f (rootedLegPolynomial_cleared p q)
  simp only [map_mul, map_sub, map_pow, map_one, map_natCast] at h
  apply mul_left_cancel₀ (mul_ne_zero hx hquad)
  rw [h]
  field_simp [hx, hquad]
#print axioms Paper7Schwenk.map_rootedLegPolynomial

theorem weightedPath_diagonal_mul {K : Type*} [CommRing K] (n : ℕ)
    (d l : Fin n → K) :
    Matrix.diagonal l * weightedPath d (fun _ => 1) =
      weightedPath (fun i => l i * d i) l := by
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    simp [weightedPath]
  · by_cases ha : i.val+1 = j.val ∨ j.val+1 = i.val <;>
      simp [weightedPath, hij, ha]
#print axioms Paper7Schwenk.weightedPath_diagonal_mul

/-- Multiplying the path Schur determinant by all actual leg determinants
produces precisely the frozen two-state chain polynomial. -/
theorem chain_eval_schur {K : Type*} [Field K] (f : Polynomial ℤ →+* K)
    (hx : f X ≠ 0) (hquad : (f X)^2-1 ≠ 0) (n : ℕ) (p q : Fin n → ℕ) :
    f (chainPolynomial (List.ofFn (fun i => (p i,q i)))) =
      (∏ i, f (legPolynomial (p i) (q i))) *
        (weightedPath (fun i => f X - (p i : K)/f X -
          (q i : K)*f X/((f X)^2-1)) (fun _ => 1)).det := by
  let d : Fin n → K := fun i =>
    f X - (p i : K)/f X - (q i : K)*f X/((f X)^2-1)
  let l : Fin n → K := fun i => f (legPolynomial (p i) (q i))
  have hdata : (fun i => (f (rootedLegPolynomial (p i) (q i)),
      f (legPolynomial (p i) (q i)))) = (fun i => (l i * d i, l i)) := by
    funext i
    exact Prod.ext (map_rootedLegPolynomial f hx hquad (p i) (q i)) rfl
  rw [chainPolynomial_eq_continuant, continuant_map]
  simp only [List.map_ofFn, Function.comp_def, legData]
  rw [hdata, ← weightedPath_det_continuant n]
  rw [← weightedPath_diagonal_mul, Matrix.det_mul, Matrix.det_diagonal]
#print axioms Paper7Schwenk.chain_eval_schur

end Paper7Schwenk
