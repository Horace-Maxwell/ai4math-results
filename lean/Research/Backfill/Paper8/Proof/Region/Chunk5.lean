import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 5 of 10 (kernel evaluation): the trees of the supports
with index 1515. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk5 : stats (chunk 1515 1) = (2400, true) := by decide +kernel

end P8Region
