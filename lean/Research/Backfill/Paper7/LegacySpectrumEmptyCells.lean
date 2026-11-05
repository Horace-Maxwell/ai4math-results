import Research.Backfill.Paper7.SpectralFeatureEmpty
import Research.Backfill.Paper7.UnfilteredDReachEmpty

/-! Full frozen feature-cell contract. The last component uses the original
load=true, cycleFilter=false recurrence; no filtered replacement is made. -/
set_option autoImplicit false
noncomputable section
namespace Paper7FeatureEmpty
open BackfillPaper7.Challenge.Legacy

theorem check_LegacySpectrumEmptyCells :
    BackfillPaper7.Challenge.Legacy.LegacySpectrumEmptyCells := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    apply odd_cells_empty false 41 (by omega) b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    tauto
  · intro b hb
    apply odd_cells_empty false 41 (by omega) b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    tauto
  · intro b hb
    apply odd_cells_empty false 42 (by omega) b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    tauto
  · intro b hb
    exact ⟨odd_cells_empty false 42 (by omega) b hb,
      odd_cells_empty true 42 (by omega) b hb⟩
  · intro b hb
    refine ⟨even_cycle_filtered_cells_empty b ?_, unfiltered_dreach_empty b hb⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
#print axioms Paper7FeatureEmpty.check_LegacySpectrumEmptyCells

end Paper7FeatureEmpty
