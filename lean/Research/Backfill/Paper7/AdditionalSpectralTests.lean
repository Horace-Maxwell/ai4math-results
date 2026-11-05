import Research.Backfill.Paper7.BoundaryTestRequirements
import Research.Backfill.Paper7.LegacyTestRequirements

/-! Three local spectral controls, independent of the unproved paper contracts. -/
set_option autoImplicit false
set_option maxRecDepth 4096
open scoped Classical
noncomputable section
namespace Paper7StatementTestsV3
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra Polynomial

theorem path_three_charpoly_complex :
    ((SimpleGraph.pathGraph 3).adjMatrix ℂ).charpoly = X^3-2*X := by
  have hm : Matrix.charmatrix ((SimpleGraph.pathGraph 3).adjMatrix ℂ) =
      (!![X, -1, 0; -1, X, -1; 0, -1, X] : Matrix (Fin 3) (Fin 3) (Polynomial ℂ)) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.charmatrix_apply, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj]
  rw [Matrix.charpoly, hm, Matrix.det_fin_three]
  norm_num
  ring
#print axioms Paper7StatementTestsV3.path_three_charpoly_complex

theorem test074 : BackfillPaper7.BoundaryTestRequirements.test_074 := by
  intro hint
  have hsquare : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hroot : Polynomial.IsRoot ((SimpleGraph.pathGraph 3).adjMatrix ℂ).charpoly
      ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [path_three_charpoly_complex]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    calc
      _ = ((Real.sqrt 2 : ℝ) : ℂ) * ((((Real.sqrt 2 : ℝ) : ℂ)^2)-2) := by ring
      _ = 0 := by rw [hsquare]; ring
  obtain ⟨z,hz⟩ := hint ((Real.sqrt 2 : ℝ) : ℂ)
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot)
  have hzreal : Real.sqrt 2 = (z : ℝ) := by
    simpa using congrArg Complex.re hz
  exact irrational_sqrt_two.ne_int z hzreal
#print axioms Paper7StatementTestsV3.test074

theorem test115 : BackfillPaper7.Challenge.LegacyTests.test_115_required := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hker : LinearMap.ker (Matrix.toLin' (overQ (!![7] : Matrix (Fin 1) (Fin 1) ℤ))) = ⊥ := by
    ext v
    constructor
    · intro hv
      have hzero := congrFun (LinearMap.mem_ker.mp hv) 0
      have hv0 : (7 : ℚ)*v 0 = 0 := by
        simpa [Matrix.toLin'_apply, overQ, Matrix.mulVec, dotProduct] using hzero
      have hv0' : v 0 = 0 := (mul_eq_zero.mp hv0).resolve_left (by norm_num)
      change v = 0
      funext i
      fin_cases i
      exact hv0'
    · intro hv
      have : v = 0 := hv
      subst v
      simp
  have hmod : overMod 7 (!![7] : Matrix (Fin 1) (Fin 1) ℤ) = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    decide
  constructor
  · change Module.finrank ℚ (LinearMap.ker (Matrix.toLin' (overQ
      (!![7] : Matrix (Fin 1) (Fin 1) ℤ)))) = 0
    rw [hker]
    simp
  · rw [hmod]
    have hz : Matrix.toLin' (0 : Matrix (Fin 1) (Fin 1) (ZMod 7)) = 0 := by
      ext v i
      simp
    unfold matrixNullity
    rw [hz, LinearMap.ker_zero, finrank_top, Module.finrank_pi]
    rfl
#print axioms Paper7StatementTestsV3.test115

theorem test117 : BackfillPaper7.Challenge.LegacyTests.test_117_required := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h3 : (3 : ZMod 7)^2 = 2 := by decide
  have hF : reducePolynomial 7 (X^2-2) =
      (X-C (3 : ZMod 7))*(X-C (-3 : ZMod 7)) := by
    rw [reducePolynomial, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat]
    calc
      (X : Polynomial (ZMod 7))^2 - 2 = X^2-C ((3 : ZMod 7)^2) := by
        rw [h3, Polynomial.C_ofNat]
      _ = (X-C (3 : ZMod 7))*(X-C (-3 : ZMod 7)) := by
        rw [map_pow, map_neg]
        ring
  have hroots : (reducePolynomial 7 (X^2-2)).roots = ({3,-3} : Multiset (ZMod 7)) := by
    rw [hF, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C]
    rfl
  constructor
  · change (∑ z ∈ integerWindow 3,
      Polynomial.rootMultiplicity (z : ZMod 7) (reducePolynomial 7 (X^2-2))) = 2
    simp only [← Polynomial.count_roots, hroots]
    have hw : integerWindow 3 = ({-3,-2,-1,0,1,2,3} : Finset ℤ) := by decide
    rw [hw]
    decide +kernel
  · rintro ⟨a,ha,hpoly⟩
    cases a with
    | nil =>
      have hc := congrArg (fun f : Polynomial ℤ => f.coeff 2) hpoly
      norm_num [Polynomial.coeff_one] at hc
    | cons z zs =>
      obtain ⟨hzlo, hzhi⟩ : -3 ≤ z ∧ z ≤ 3 := by
        simpa [integerWindow] using ha z (by simp)
      rw [List.map_cons, List.prod_cons] at hpoly
      have heval := congrArg (Polynomial.eval z) hpoly
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_ofNat, Polynomial.eval_mul, Polynomial.eval_C, sub_self,
        zero_mul] at heval
      interval_cases z <;> norm_num at heval
#print axioms Paper7StatementTestsV3.test117

end Paper7StatementTestsV3
