import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 2 of 10 (kernel evaluation): the trees of the supports
with indices 169 to 490. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk2 : stats (chunk 169 322) = (1768, true) := by decide +kernel

end P8Region
