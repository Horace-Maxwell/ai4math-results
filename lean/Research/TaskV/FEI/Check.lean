import Research.TaskV.FEI.Walsh
import Research.TaskV.FEI.Determinant
import Research.TaskV.FEI.Analysis
import Research.TaskV.FEI.Layer
import Research.TaskV.FEI.UpperAnalysis

namespace Fei
open Finset

theorem check_upperProduct : UpperProduct := upperProduct_of (fun _ => tail_integral)
theorem check_signedProduct : SignedProduct := signedProduct_of_upper check_upperProduct
theorem check_supportEntropy : SupportEntropy :=
  supportEntropy_of check_signedProduct (fun _ => parseval)
theorem check_lowerMassFEI : LowerMassFEI :=
  lowerMassFEI_of check_supportEntropy (fun _ => parseval)
theorem check_boundedRatioFEI : BoundedRatioFEI :=
  boundedRatioFEI_of check_lowerMassFEI (fun _ => parseval)
theorem check_comparableMassFEI : ComparableMassFEI :=
  comparableMassFEI_core (fun _ => upper_layer_sum) (fun _ => parseval)
    (fun n f V hs hu => upper_log f V hs (check_upperProduct n f V hs hu))

example : character ({0} : Cube 1) {0} = -1 := by simp [character]
example : character (∅ : Cube 1) {0} = 1 := by simp [character]
example : coeff (n := 0) (fun _ => true) ∅ = -1 := by classical simp [coeff, value, character, Cube]

#print axioms check_signedProduct
#print axioms check_supportEntropy
#print axioms check_lowerMassFEI
#print axioms check_boundedRatioFEI
#print axioms check_upperProduct
#print axioms check_comparableMassFEI
end Fei
