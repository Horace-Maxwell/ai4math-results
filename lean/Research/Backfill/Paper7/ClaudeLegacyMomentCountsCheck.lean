import Research.Backfill.Paper7.MomentCountsCompleteCatalogAssembly

/-! Claude, 2026-11-03. The frozen contract LegacyMomentCounts, unchanged, from the
complete 21-entry catalogue: the certified catalogue sum is 14215675, checked by the
kernel (`decide`, heartbeat budget raised for this declaration only). -/
set_option autoImplicit false
namespace Paper7MomentCounts

set_option maxHeartbeats 0 in
theorem claude_b6CertifiedCatalogSum_eq : b6CertifiedCatalogSum = 14215675 := by
  decide
#print axioms Paper7MomentCounts.claude_b6CertifiedCatalogSum_eq

theorem check_LegacyMomentCounts : BackfillPaper7.Challenge.Legacy.LegacyMomentCounts :=
  legacyMomentCounts_of_b6CertifiedCatalogSum claude_b6CertifiedCatalogSum_eq
#print axioms Paper7MomentCounts.check_LegacyMomentCounts

end Paper7MomentCounts
