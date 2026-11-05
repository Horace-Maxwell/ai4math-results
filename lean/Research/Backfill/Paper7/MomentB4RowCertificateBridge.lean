import Research.Backfill.Paper7.MomentB4ZQFibres
import Research.Backfill.Paper7.MomentB4FirstRowPilot

/-! Interface from the exact original cardinality to the pending 19-pair
catalogue and literal prefix-table certificates. The complete numerical sum
is not evaluated here. Prior catalogue/table/pilot sources remain dependencies,
not hypotheses replacing the original candidate-set definition. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCertificate
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts Paper7MomentDP Paper7Budget
open scoped BigOperators Classical

def B4CatalogRowAccept (z : Fin 4 → ℕ) (Q : ℕ) : Prop :=
  Q ≤ (∑ i, z i) ∧ 0 < (∑ i, z i) + Q ∧ 4 + ((∑ i, z i) + Q) ≤ 41 ∧
    ∃ sm ∈ b4FeatureCatalog, sm.2 = b4Theta z Q + 4 ∧
      sm.1 ≤ (4 + ((∑ i, z i) + Q : ℕ) : ℤ) ∧
      (4 + ((∑ i, z i) + Q : ℕ) : ℤ) - max (Q : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCertificate.B4CatalogRowAccept

theorem b4_guarded_catalog_iff (z : Fin 4 → ℕ) (Q : ℕ) :
    B4GuardedRowAccept z Q ↔ B4CatalogRowAccept z Q := by
  unfold B4GuardedRowAccept B4RowAccept B4CatalogRowAccept
  rw [b4_evenFeature_catalog_iff]
  simp only [and_assoc]
#print axioms Paper7MomentCertificate.b4_guarded_catalog_iff

/-- Each Q is counted once, regardless of how many feature witnesses exist. -/
def b4RowContribution (z : Fin 4 → ℕ) : ℕ :=
  ∑ Q : Fin 19, if B4CatalogRowAccept z Q.val then boundedQDP 4 z Q.val else 0
#print axioms Paper7MomentCertificate.b4RowContribution

theorem candB1_b4_ncard_eq_row_contributions :
    (CandB1 4 41).ncard = ∑ z : BoundedTuple 4 37, b4RowContribution z.val := by
  rw [candB1_b4_ncard_eq_guarded_zq_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold b4RowContribution
  apply Finset.sum_congr rfl
  intro Q _
  rw [b4_guarded_catalog_iff]
#print axioms Paper7MomentCertificate.candB1_b4_ncard_eq_row_contributions

/-- A local certificate interface: all initial and successor cells are required.
This conditional table interface does not stand in for a numerical main check. -/
theorem b4RowContribution_eq_table (z : Fin 4 → ℕ)
    (L : Fin 5 → Fin 19 → ℕ) (hL : QTableValid z L) :
    b4RowContribution z =
      ∑ Q : Fin 19, if B4CatalogRowAccept z Q.val then L (Fin.last 4) Q else 0 := by
  unfold b4RowContribution
  apply Finset.sum_congr rfl
  intro Q _
  rw [qTable_last_eq z L hL Q]
#print axioms Paper7MomentCertificate.b4RowContribution_eq_table

theorem b4_pilot_guarded_iff (Q : Fin 19) :
    B4GuardedRowAccept pilotZ7 Q.val ↔ pilot7Accept Q := by
  have hz : (∑ i, pilotZ7 i) = 7 := by decide
  have hs : (∑ i, (pilotZ7 i : ℤ)^2) = 49 := by
    norm_num [pilotZ7, Fin.sum_univ_four]
  have ht : b4Theta pilotZ7 Q.val = 78 + 2*(Q.val : ℤ) := by
    unfold b4Theta
    rw [hz, hs]
    norm_num only [Nat.cast_ofNat]
    ring
  simp only [B4GuardedRowAccept, B4RowAccept, pilot7Accept, hz, ht, and_assoc]
#print axioms Paper7MomentCertificate.b4_pilot_guarded_iff

/-- The sealed row-7 pilot is now a row of the exact original-cardinality sum. -/
theorem b4RowContribution_pilot7 : b4RowContribution pilotZ7 = 1 := by
  calc
    b4RowContribution pilotZ7 =
        ∑ Q : Fin 19, if pilot7Accept Q then boundedQDP 4 pilotZ7 Q.val else 0 := by
      unfold b4RowContribution
      apply Finset.sum_congr rfl
      intro Q _
      rw [← b4_guarded_catalog_iff, b4_pilot_guarded_iff]
    _ = 1 := pilot7_contribution
#print axioms Paper7MomentCertificate.b4RowContribution_pilot7

theorem pilotZ7_bounded : (∑ i, pilotZ7 i) ≤ 37 := by decide
#print axioms Paper7MomentCertificate.pilotZ7_bounded

/-- Explicit membership of the pilot in the whole original z-domain. No other
row, complete block, or global numeric cardinality is claimed here. -/
theorem b4_indexed_pilot_contribution :
    b4RowContribution (⟨pilotZ7, pilotZ7_bounded⟩ : BoundedTuple 4 37).val = 1 :=
  b4RowContribution_pilot7
#print axioms Paper7MomentCertificate.b4_indexed_pilot_contribution

end Paper7MomentCertificate
