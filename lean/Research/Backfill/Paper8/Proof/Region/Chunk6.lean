import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 6 of 10 (kernel evaluation): the trees of the supports
with indices 1516 to 2549. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk6 : stats (chunk 1516 1034) = (990, true) := by decide +kernel

end P8Region
