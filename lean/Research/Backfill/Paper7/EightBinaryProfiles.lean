import Research.Backfill.Paper7.EightBinaryCycleDet

/-! Eight small scalar specializations of the proved sparse determinant
identity. Each declaration has its own unchanged default proof budget. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open scoped CharTwo

def binaryCycleProfile {R : Type*} [Semiring R] (j : Fin 8) (x : R) :
    Matrix (Fin 8) (Fin 8) R :=
  binaryCycleMatrix (fun i => x^2 + if i = 0 ∨ i = j then 1 else 0) x
#print axioms Paper7EightCycle.binaryCycleProfile

theorem binaryPathDet_one_function {R : Type*} [CommRing R] :
    (binaryPathDet (R := R) 1) = (fun (a : Fin 1 → R) (_x : R) => a 0) := by
  funext a x
  exact binaryPathDet_one a x
#print axioms Paper7EightCycle.binaryPathDet_one_function

theorem binary_cycle_profile_zero {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 0 x).det = x^16+x^14 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.binary_cycle_profile_zero

theorem binary_cycle_profile_one {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 1 x).det = x^16+x^12+x^10+x^6 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.binary_cycle_profile_one

theorem binary_cycle_profile_two {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 2 x).det = x^16+x^12+x^8 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
#print axioms Paper7EightCycle.binary_cycle_profile_two

theorem binary_cycle_profile_three {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 3 x).det = x^16+x^12+x^6 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.binary_cycle_profile_three

theorem binary_cycle_profile_four {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 4 x).det = x^16+x^12 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
#print axioms Paper7EightCycle.binary_cycle_profile_four

theorem binary_cycle_profile_five {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 5 x).det = x^16+x^12+x^6 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
#print axioms Paper7EightCycle.binary_cycle_profile_five

theorem binary_cycle_profile_six {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 6 x).det = x^16+x^12+x^8 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.binary_cycle_profile_six

theorem binary_cycle_profile_seven {R : Type*} [CommRing R] [CharP R 2] (x : R) :
    (binaryCycleProfile 7 x).det = x^16+x^12+x^10+x^6 := by
  rw [binaryCycleProfile, binary_cycle_det_paths]
  simp only [binaryPathDet_recur]
  simp only [binaryPathDet_one, binaryPathDet_zero]
  norm_num
  all_goals ring_nf
  all_goals simp
  all_goals rw [binaryPathDet_one_function]
  all_goals norm_num
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.binary_cycle_profile_seven

theorem binary_cycle_profile_det {R : Type*} [CommRing R] [CharP R 2]
    (j : Fin 8) (x : R) :
    (binaryCycleProfile j x).det =
      if j = 0 then x^16+x^14 else
      if j = 1 ∨ j = 7 then x^16+x^12+x^10+x^6 else
      if j = 2 ∨ j = 6 then x^16+x^12+x^8 else
      if j = 3 ∨ j = 5 then x^16+x^12+x^6 else x^16+x^12 := by
  fin_cases j
  · simpa using binary_cycle_profile_zero x
  · simpa using binary_cycle_profile_one x
  · simpa using binary_cycle_profile_two x
  · simpa using binary_cycle_profile_three x
  · simpa using binary_cycle_profile_four x
  · simpa using binary_cycle_profile_five x
  · simpa using binary_cycle_profile_six x
  · simpa using binary_cycle_profile_seven x
#print axioms Paper7EightCycle.binary_cycle_profile_det

end Paper7EightCycle
