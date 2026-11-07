import Research.Backfill.Paper2.Challenge

/-!
Paper 2, the entire positive-exponent continued-fraction family.
Only the first two defining relations are needed. Unit tails are derived
from the original constant-term conditions, rather than added as assumptions.
The algebra follows the published HannaA338633 argument for the whole family.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.CFFamily
open PowerSeries BackfillPaper2.Challenge

theorem check_RC_CFfamilyMod2 : RC_CFfamilyMod2 := by
  intro e he A T hCF
  rcases hCF with ⟨hunits, h0, hk⟩
  let f : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hT1 : IsUnit (T 1) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rcases hunits 1 with h | h <;> simp [h]
  have hEven : f ((2 : ℤ) ^ e) = 0 := by
    simp only [map_pow]
    have h2 : f 2 = 0 := by decide
    rw [h2, zero_pow (by omega : e ≠ 0)]
  have e1 : (A.map f - 1) * (T 0).map f = X := by
    have h := congrArg (PowerSeries.map f) h0
    simpa only [map_mul, map_sub, map_one, map_X] using h
  have e2 : (A.map f - (T 0).map f) * (T 1).map f = 0 := by
    have h := congrArg (PowerSeries.map f) (hk 0)
    rw [map_mul, map_sub, map_mul, map_C, map_X] at h
    change (A.map f - (T 0).map f) * (T 1).map f = C (f ((2 : ℤ) ^ e)) * X at h
    simpa only [hEven, map_zero, zero_mul] using h
  have hu : IsUnit ((T 1).map f) := hT1.map (PowerSeries.map f)
  have ht : (T 0).map f = A.map f :=
    (sub_eq_zero.mp (hu.mul_left_eq_zero.mp e2)).symm
  rw [ht] at e1
  change red 2 A * (red 2 A - 1) = X
  simpa only [red, mul_comm] using e1

end BackfillPaper2.CFFamily
#print axioms BackfillPaper2.CFFamily.check_RC_CFfamilyMod2
