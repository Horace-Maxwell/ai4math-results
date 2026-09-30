import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 3 of 10 (kernel evaluation): the trees of the supports
with indices 491 to 1320. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk3 : stats (chunk 491 830) = (1959, true) := by decide +kernel

end P8Region
