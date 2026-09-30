import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 9 of 10 (kernel evaluation): the trees of the supports
with indices 4900 to 6299. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk9 : stats (chunk 4900 1400) = (0, true) := by decide +kernel

end P8Region
