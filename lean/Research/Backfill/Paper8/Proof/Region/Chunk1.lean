import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 1 of 10 (kernel evaluation): the trees of the supports
with indices 0 to 168. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk1 : stats (chunk 0 169) = (1975, true) := by decide +kernel

end P8Region
