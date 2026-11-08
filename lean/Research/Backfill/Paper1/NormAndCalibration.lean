import Research.Backfill.Paper1.ColumnIdentity
import Research.Backfill.Paper1.GraphBridge
import Research.Backfill.Paper1.NarrowContractTests

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1

theorem check_GeneralGNorm : NarrowSupplement.GeneralGNorm := by
  intro a b p q Y
  exact ColumnIdentity.Gval_corner a b p q Y

/-- A positive calibration of the actual graph spectrum, using the general
spectral bridge at exponent pair (1,0), not a replacement definition of energy. -/
theorem check_PositiveEnergyCalibration : NarrowContractTests.PositiveEnergyCalibration := by
  change Challenge.energy 3 {1} = 4
  have h := ICGGeneral.energy_icgAdj_pq 3 2 1 0 (by norm_num) (by norm_num)
    (by norm_num) {1}
  rw [← GraphBridge.graph_energy_eq (3 ^ 1 * 2 ^ 0) {1} (by decide)] at h
  norm_num only [Nat.cast_ofNat, pow_one, pow_zero, mul_one] at h
  rw [h]
  norm_num [ICGGeneral.L1mat, ICGGeneral.Mentry, ICGGeneral.Tent,
    ICGGeneral.phiX, ICGGeneral.ramX, Finset.sum_range_succ]

example : Challenge.energy 3 {1} = 4 := check_PositiveEnergyCalibration
example : 0 < Challenge.energy 3 {1} := by
  rw [check_PositiveEnergyCalibration]; norm_num

#print axioms check_GeneralGNorm
#print axioms check_PositiveEnergyCalibration
end CodexPaper1
