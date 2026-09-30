import Research.Backfill.Paper8.Proof.Region.Defs

/-! Region search, part 8 of 10 (kernel evaluation): the trees of the supports
with indices 3553 to 4899. -/

set_option autoImplicit false

namespace P8Region

theorem stats_chunk8 : stats (chunk 3553 1347) = (444, true) := by decide +kernel

end P8Region
