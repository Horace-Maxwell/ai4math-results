import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 4 of 10 (kernel evaluation): the trees of the supports
with indices 1321 to 1514. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk4 : stats (chunk 1321 194) = (1935, true) := by decide +kernel

end P8Region
