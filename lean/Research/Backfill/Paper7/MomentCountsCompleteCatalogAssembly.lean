import Research.Backfill.Paper7.MomentB6CompleteCatalogCollector
import Research.Backfill.Paper7.MomentCountsFinalReduction

/-! SOURCE ONLY. The original full sixteen-conjunct LegacyMomentCounts is
unchanged. This equivalence records the exact outstanding numeral certificate;
it does not prove that certificate, promote pending theta modules, or add
premises to the original contract. The prior canonical/Burnside derivation is
reused exclusively through the sealed final-reduction source. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge.Legacy

theorem legacyMomentCounts_iff_b6CertifiedCatalogSum :
    LegacyMomentCounts ↔ b6CertifiedCatalogSum = 14215675 := by
  rw [legacyMomentCounts_iff_b6_labelled_count,
    ← b6CertifiedCatalogSum_eq_original_B1]
#print axioms Paper7MomentCounts.legacyMomentCounts_iff_b6CertifiedCatalogSum

/-- A proof-composition helper, not a proof of its explicit numeral obligation. -/
theorem legacyMomentCounts_of_b6CertifiedCatalogSum
    (hcount : b6CertifiedCatalogSum = 14215675) : LegacyMomentCounts :=
  legacyMomentCounts_iff_b6CertifiedCatalogSum.mpr hcount
#print axioms Paper7MomentCounts.legacyMomentCounts_of_b6CertifiedCatalogSum

end Paper7MomentCounts
