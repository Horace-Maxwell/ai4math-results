import Research.Backfill.Paper7.Control44Polynomial
import Research.Backfill.Paper7.GraphPhiCharpoly

/-! Complete source-only candidate for the historically named ControlC42Ten.
All forty-four roots, their multiplicities, the integer polynomial, and complex
spectral integrality are conclusions. The single eigenvalue test114 is not used
as a substitute for this full contract. Root owns all future execution. -/

set_option autoImplicit false

namespace Paper7Control44

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

def controlRootList : List ℤ :=
  List.replicate 2 0 ++ List.replicate 19 1 ++
    List.replicate 19 (-1) ++ [3, -3, 4, -4]

#print axioms Paper7Control44.controlRootList

/-- Reassociate complete factor blocks in an abstract ring before polynomial instantiation. -/
theorem control_factor_blocks {R : Type*} [CommRing R] (a b c d e f g : R) :
    a * b * c * (d * (e * (f * g))) =
      a * (b * c) * (d * e) * (f * g) := by
  simp only [mul_assoc]

#print axioms Paper7Control44.control_factor_blocks

/-- Every one of the forty-four factors is present, including all repeated signs. -/
theorem control_root_product :
    (controlRootList.map (fun z => X - C z)).prod =
      X ^ 2 * (X ^ 2 - 1) ^ 19 * (X ^ 2 - 9) * (X ^ 2 - 16) := by
  have h1 : (X ^ 2 - 1 : Polynomial ℤ) = (X - 1) * (X + 1) := by ring
  have h9 : (X ^ 2 - 9 : Polynomial ℤ) = (X - 3) * (X + 3) := by ring
  have h16 : (X ^ 2 - 16 : Polynomial ℤ) = (X - 4) * (X + 4) := by ring
  rw [h1, h9, h16, mul_pow]
  simp only [controlRootList, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate]
  norm_num
  exact control_factor_blocks (X ^ 2) ((X - 1) ^ 19) ((X + 1) ^ 19)
    (X - 3) (X + 3) (X - 4) (X + 4)

#print axioms Paper7Control44.control_root_product

theorem control_integer_factors :
    graphPhi (sunGraph 4 C42Ten) = (controlRootList.map (fun z => X - C z)).prod :=
  control_graphPhi.trans control_root_product.symm

#print axioms Paper7Control44.control_integer_factors

theorem control_integral : IsIntegralGraph (sunGraph 4 C42Ten) :=
  integral_of_integer_factor_list (sunGraph 4 C42Ten) controlRootList control_integer_factors

#print axioms Paper7Control44.control_integral

theorem control_spectrum :
    spec (sunGraph 4 C42Ten) =
      2 • ({0} : Multiset ℝ) + 19 • {1} + 19 • {-1} + {3, -3, 4, -4} := by
  have htail :
      (([3, -3, 4, -4] : List ℤ) : Multiset ℤ).map
        (fun z : ℤ => (z : ℝ)) = ({3, -3, 4, -4} : Multiset ℝ) := by
    norm_num [Multiset.map_coe]
    simp only [← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero]
  rw [spec_of_integer_factor_list (sunGraph 4 C42Ten) controlRootList control_integer_factors]
  simp only [Multiset.map_id', Multiset.bind_def, Multiset.pure_def,
    Multiset.bind_singleton]
  simp only [controlRootList, ← Multiset.coe_add, Multiset.map_add,
    Multiset.coe_replicate, Multiset.map_replicate,
    Int.cast_zero, Int.cast_one, Int.cast_neg, htail,
    Multiset.nsmul_singleton, add_assoc]

#print axioms Paper7Control44.control_spectrum

theorem control_multiplicity_one : mult (sunGraph 4 C42Ten) 1 = 19 := by
  classical
  rw [mult, control_spectrum]
  norm_num [Multiset.count_add, Multiset.count_nsmul]

#print axioms Paper7Control44.control_multiplicity_one

theorem control_multiplicity_neg_one : mult (sunGraph 4 C42Ten) (-1) = 19 := by
  classical
  rw [mult, control_spectrum]
  norm_num [Multiset.count_add, Multiset.count_nsmul]

#print axioms Paper7Control44.control_multiplicity_neg_one

/-- The full seven-conjunct frozen target, not only its lambda-one control test. -/
theorem check_ControlC42Ten : BackfillPaper7.Challenge.ControlC42Ten := by
  refine ⟨control_order, control_pendant_positive, control_integral, ?_,
    control_spectrum, control_multiplicity_one, control_multiplicity_neg_one⟩
  exact (Paper7GraphPhi.graphPhi_eq_charpoly (sunGraph 4 C42Ten)).symm.trans
    control_graphPhi

#print axioms Paper7Control44.check_ControlC42Ten

end Paper7Control44
