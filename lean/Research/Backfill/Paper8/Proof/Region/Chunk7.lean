import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 7 of 10 (kernel evaluation): the trees of the supports
with indices 2550 to 3552. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk7 : stats (chunk 2550 1003) = (945, true) := by decide +kernel

end P8Region
