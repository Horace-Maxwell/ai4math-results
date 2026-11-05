import Research.Backfill.Paper7.ModularPolynomialRejectSound
import Research.Backfill.Paper7.SpectrumFactorization

/-! Source-only bridges for the complete 44-vertex control.
No execution or acceptance is asserted by this candidate. -/

set_option autoImplicit false
open scoped Matrix

namespace Paper7Control44

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- The complete list of integer linear factors controls the complex spectrum. -/
theorem integral_of_integer_factor_list {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : List ℤ)
    (hf : graphPhi G = (a.map (fun z => X - C z)).prod) : IsIntegralGraph G := by
  classical
  apply (Paper7Spectrum.integral_iff_integerFactorization G).mpr
  exact ⟨a.toFinset, a, fun _ hz => List.mem_toFinset.mpr hz, hf⟩

#print axioms Paper7Control44.integral_of_integer_factor_list

/-- Repeated entries remain repeated roots in the actual real characteristic polynomial. -/
theorem spec_of_integer_factor_list {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : List ℤ)
    (hf : graphPhi G = (a.map (fun z => X - C z)).prod) :
    spec G = (a : Multiset ℤ).map (fun z => (z : ℝ)) := by
  classical
  have hf' : graphPhi G = BackfillPaper7.PolynomialRejectProof.linearProduct a := hf
  change (G.adjMatrix ℝ).charpoly.roots = _
  rw [← Paper7Spectrum.graphPhi_map G ℝ, hf',
    BackfillPaper7.PolynomialRejectProof.linearProduct_map]
  simpa only [BackfillPaper7.PolynomialRejectProof.linearProduct,
    Multiset.map_id', Multiset.bind_def, Multiset.pure_def,
    Multiset.bind_singleton, Multiset.map_coe, Multiset.prod_coe, List.map_id',
    Int.coe_castRingHom] using
    (Polynomial.roots_multiset_prod_X_sub_C
      ((a.map (Int.castRingHom ℝ) : List ℝ) : Multiset ℝ))

#print axioms Paper7Control44.spec_of_integer_factor_list

/-- A four-cycle matrix with two adjacent diagonal pairs; no large determinant is expanded. -/
theorem det_cycle_pair {R : Type*} [CommRing R] (a b c : R) :
    (!![a,c,0,c; c,a,c,0; 0,c,b,c; c,0,c,b] : Matrix (Fin 4) (Fin 4) R).det =
      (a * b) ^ 2 - c ^ 2 * (a + b) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

#print axioms Paper7Control44.det_cycle_pair

/-- Keep the degree-44 cancellation algebra factored instead of expanding a nineteenth power. -/
theorem cleared_control_reassociation {R : Type*} [CommRing R] (x y z t : R) :
    y ^ 20 * (x ^ 6 * y ^ 3 * z * t) =
      (x ^ 4 * y ^ 4) * (x ^ 2 * y ^ 19 * z * t) := by
  ring

#print axioms Paper7Control44.cleared_control_reassociation

end Paper7Control44
