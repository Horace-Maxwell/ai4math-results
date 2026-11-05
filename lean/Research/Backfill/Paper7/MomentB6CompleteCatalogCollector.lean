import Research.Backfill.Paper7.MomentB6ResidualPruned
import Research.Backfill.Paper7.MomentB6FourEmptyFibres
import Research.Backfill.Paper7.MomentB6Theta84Count
import Research.Backfill.Paper7.MomentB6Theta96Complete
import Research.Backfill.Paper7.MomentB6Theta252Count
import Research.Backfill.Paper7.MomentB6Theta264WholePrefix
import Research.Backfill.Paper7.MomentB6Theta312Whole
import Research.Backfill.Paper7.MomentB6Theta324DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta336LowQFiveDominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta384DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta396DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta408DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta612DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta624DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta672DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta684DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta696DominantTightCWhole
import Research.Backfill.Paper7.MomentB6Theta840DominantTightCWhole
import Research.Backfill.Paper7.MomentB6TopMomentCount

/-! SOURCE ONLY; NOT AN ACCEPTED COUNT.
The entire unchanged 21-entry feature catalogue is collected once, using
existing complete original B1 theta-fibre theorems. Named Values for pending
whole theta modules remain symbolic. No unknown numeral, new graph premise,
partial-Q replacement, count-by-subtraction or new enumeration occurs here.
The total's equality to 14215675 is deliberately NOT asserted in this module.
All pending exact whole sources must actually pass before this collector
can be selected for validation. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

/-- Complete catalogue certificate lookup. The default is outside the
catalogue and is never used by the guarded correctness theorem. -/
def b6CertifiedThetaCount (T : ℤ) : ℕ :=
  if T = 72 then 0 else
  if T = 84 then 66 else
  if T = 96 then 53903 else
  if T = 240 then 0 else
  if T = 252 then 36 else
  if T = 264 then b6Theta264Value else
  if T = 312 then b6Theta312WholeValue else
  if T = 324 then b6Theta324WholeValue else
  if T = 336 then b6Theta336WholeValue else
  if T = 384 then b6Theta384WholeValue else
  if T = 396 then b6Theta396WholeValue else
  if T = 408 then b6Theta408WholeValue else
  if T = 600 then 0 else
  if T = 612 then b6Theta612WholeValue else
  if T = 624 then b6Theta624WholeValue else
  if T = 672 then b6Theta672WholeValue else
  if T = 684 then b6Theta684WholeValue else
  if T = 696 then b6Theta696WholeValue else
  if T = 840 then b6Theta840WholeValue else
  if T = 1260 then 0 else
  if T = 1272 then 6 else
  0
#print axioms Paper7MomentCounts.b6CertifiedThetaCount

/-- Every one of the original catalogue entries uses its complete fibre. -/
theorem b6CertifiedThetaCount_eq_original_B1 (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard =
      b6CertifiedThetaCount sm.2 := by
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 72}.ncard = 0
    exact b6_candB1_four_theta_ncards.1
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 84}.ncard = 66
    exact b6_theta84_candB1_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 96}.ncard = 53903
    exact b6_candB1_theta96_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 240}.ncard = 0
    exact b6_candB1_four_theta_ncards.2.1
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 252}.ncard = 36
    exact b6_theta252_candB1_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 264}.ncard = b6Theta264Value
    exact b6Theta264_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 312}.ncard = b6Theta312WholeValue
    exact b6Theta312Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 324}.ncard = b6Theta324WholeValue
    exact b6Theta324Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 336}.ncard = b6Theta336WholeValue
    exact b6Theta336Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 384}.ncard = b6Theta384WholeValue
    exact b6Theta384Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 396}.ncard = b6Theta396WholeValue
    exact b6Theta396Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 408}.ncard = b6Theta408WholeValue
    exact b6Theta408Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 600}.ncard = 0
    exact b6_candB1_four_theta_ncards.2.2.1
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 612}.ncard = b6Theta612WholeValue
    exact b6Theta612Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 624}.ncard = b6Theta624WholeValue
    exact b6Theta624Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 672}.ncard = b6Theta672WholeValue
    exact b6Theta672Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 684}.ncard = b6Theta684WholeValue
    exact b6Theta684Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 696}.ncard = b6Theta696WholeValue
    exact b6Theta696Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 840}.ncard = b6Theta840WholeValue
    exact b6Theta840Whole_candB1_theta_ncard
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 1260}.ncard = 0
    exact b6_candB1_four_theta_ncards.2.2.2
  · change {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 1272}.ncard = 6
    exact b6_top_moment_candB1_ncard
#print axioms Paper7MomentCounts.b6CertifiedThetaCount_eq_original_B1

theorem b6CertifiedThetaCount_eq_original_D2 (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard =
      b6CertifiedThetaCount sm.2 := by
  rw [candD2_eq_candB1_of_even 6 42 (show Even (6 : ℕ) from ⟨3, rfl⟩)]
  exact b6CertifiedThetaCount_eq_original_B1 sm hsm
#print axioms Paper7MomentCounts.b6CertifiedThetaCount_eq_original_D2

/-- Sum over the original whole finite catalogue, not a selected subcatalogue. -/
def b6CertifiedCatalogSum : ℕ :=
  ∑ sm ∈ b6FeatureCatalog, b6CertifiedThetaCount sm.2
#print axioms Paper7MomentCounts.b6CertifiedCatalogSum

theorem b6CertifiedCatalogSum_eq_original_B1 :
    b6CertifiedCatalogSum = (CandB1 6 42).ncard := by
  have hcast : (b6CertifiedCatalogSum : ℤ) = ((CandB1 6 42).ncard : ℤ) := by
    calc
      (b6CertifiedCatalogSum : ℤ) =
          ∑ sm ∈ b6FeatureCatalog, (b6CertifiedThetaCount sm.2 : ℤ) := by
        simp only [b6CertifiedCatalogSum, Nat.cast_sum]
      _ = ∑ sm ∈ b6FeatureCatalog, b6StructuralResidualPrunedEvalTotal sm := by
        apply Finset.sum_congr rfl
        intro sm hsm
        exact ((b6StructuralResidualPrunedEvalTotal_eq_original_B1_theta sm hsm).trans
          (congrArg (fun n : ℕ => (n : ℤ))
            (b6CertifiedThetaCount_eq_original_B1 sm hsm))).symm
      _ = ((CandB1 6 42).ncard : ℤ) :=
        b6StructuralResidualPrunedEvalTotal_sum_eq_original_B1
  exact_mod_cast hcast
#print axioms Paper7MomentCounts.b6CertifiedCatalogSum_eq_original_B1

theorem b6CertifiedCatalogSum_eq_original_D2 :
    b6CertifiedCatalogSum = (CandD2 6 42).ncard := by
  rw [candD2_ncard_eq_candB1_of_even 6 42 (show Even (6 : ℕ) from ⟨3, rfl⟩)]
  exact b6CertifiedCatalogSum_eq_original_B1
#print axioms Paper7MomentCounts.b6CertifiedCatalogSum_eq_original_D2

end Paper7MomentCounts
