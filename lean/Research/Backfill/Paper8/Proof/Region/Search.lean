import Research.Backfill.Paper8.Proof.Region.Enum
import Research.Backfill.Paper8.Proof.Region.Chunk1
import Research.Backfill.Paper8.Proof.Region.Chunk2
import Research.Backfill.Paper8.Proof.Region.Chunk3
import Research.Backfill.Paper8.Proof.Region.Chunk4
import Research.Backfill.Paper8.Proof.Region.Chunk5
import Research.Backfill.Paper8.Proof.Region.Chunk6
import Research.Backfill.Paper8.Proof.Region.Chunk7
import Research.Backfill.Paper8.Proof.Region.Chunk8
import Research.Backfill.Paper8.Proof.Region.Chunk9
import Research.Backfill.Paper8.Proof.Region.Chunk10

/-!
# Region search: the result of the kernel evaluation (agent `region`)

The ten chunks `Research.Backfill.Paper8.Proof.Region.Chunk1`–`Chunk10` together cover `enum` (`enum_eq_chunk`,
`stats_split`): `enum` has `13376` trees and every tree passes `checkTree`.
-/

set_option autoImplicit false

namespace P8Region

theorem stats_enum : stats enum = (13376, true) := by
  have h9 := stats_split (lo := 4900) (a := 1400) (b := 3700) (lo' := 6300) (ab := 5100)
    (n₁ := 0) (n₂ := 960) (n := 960) rfl rfl rfl stats_chunk9 stats_chunk10
  have h8 := stats_split (lo := 3553) (a := 1347) (b := 5100) (lo' := 4900) (ab := 6447)
    (n₁ := 444) (n₂ := 960) (n := 1404) rfl rfl rfl stats_chunk8 h9
  have h7 := stats_split (lo := 2550) (a := 1003) (b := 6447) (lo' := 3553) (ab := 7450)
    (n₁ := 945) (n₂ := 1404) (n := 2349) rfl rfl rfl stats_chunk7 h8
  have h6 := stats_split (lo := 1516) (a := 1034) (b := 7450) (lo' := 2550) (ab := 8484)
    (n₁ := 990) (n₂ := 2349) (n := 3339) rfl rfl rfl stats_chunk6 h7
  have h5 := stats_split (lo := 1515) (a := 1) (b := 8484) (lo' := 1516) (ab := 8485)
    (n₁ := 2400) (n₂ := 3339) (n := 5739) rfl rfl rfl stats_chunk5 h6
  have h4 := stats_split (lo := 1321) (a := 194) (b := 8485) (lo' := 1515) (ab := 8679)
    (n₁ := 1935) (n₂ := 5739) (n := 7674) rfl rfl rfl stats_chunk4 h5
  have h3 := stats_split (lo := 491) (a := 830) (b := 8679) (lo' := 1321) (ab := 9509)
    (n₁ := 1959) (n₂ := 7674) (n := 9633) rfl rfl rfl stats_chunk3 h4
  have h2 := stats_split (lo := 169) (a := 322) (b := 9509) (lo' := 491) (ab := 9831)
    (n₁ := 1768) (n₂ := 9633) (n := 11401) rfl rfl rfl stats_chunk2 h3
  have h1 := stats_split (lo := 0) (a := 169) (b := 9831) (lo' := 169) (ab := 10000)
    (n₁ := 1975) (n₂ := 11401) (n := 13376) rfl rfl rfl stats_chunk1 h2
  rw [enum_eq_chunk]
  exact h1

theorem length_enum : enum.length = 13376 := by
  have h := stats_enum
  simp only [stats, Prod.mk.injEq] at h
  exact h.1

theorem checkTree_of_mem_enum {T : List (ℕ × ℕ)} (hT : T ∈ enum) : checkTree T = true := by
  have h := stats_enum
  simp only [stats, Prod.mk.injEq] at h
  exact List.all_eq_true.1 h.2 T hT

end P8Region
