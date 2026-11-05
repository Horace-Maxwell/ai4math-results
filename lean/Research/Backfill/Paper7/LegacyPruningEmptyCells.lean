import Research.Backfill.Paper7.PruningBCountEmpty
import Research.Backfill.Paper7.PruningCThirteenEmpty

/-! The three literal pruning cells, with each original version/flag retained.
The proof uses their guards as predicates, not as assertions of integrality. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningEmpty

theorem check_LegacyPruningEmptyCells :
    BackfillPaper7.Challenge.Legacy.LegacyPruningEmptyCells := by
  exact ⟨pruning_b3_fourteen_empty, pruning_b3_eighteen_empty, pruning_c_thirteen_empty⟩
#print axioms Paper7PruningEmpty.check_LegacyPruningEmptyCells

end Paper7PruningEmpty
