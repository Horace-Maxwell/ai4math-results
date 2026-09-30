import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 10 of 10 (kernel evaluation): the trees of the supports
with indices 6300 to 8187, the last ones. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk10 : stats (chunk 6300 3700) = (960, true) := by decide +kernel

end P8Region
