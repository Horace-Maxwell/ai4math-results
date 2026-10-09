import Research.Backfill.Paper6.Calib166Part02

/-! Weight 166, blocks 24 through 31. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block24 : blockCount masks166 1536 = 0 := by
  decide +kernel

theorem calib166_prefix25 : countPrefix masks166 1600 = 32 := by
  calc
    countPrefix masks166 1600 = countPrefix masks166 1536 + blockCount masks166 1536 :=
      prefix_step masks166 1536
    _ = 32 := by rw [calib166_prefix24, calib166_block24]

theorem calib166_block25 : blockCount masks166 1600 = 0 := by
  decide +kernel

theorem calib166_prefix26 : countPrefix masks166 1664 = 32 := by
  calc
    countPrefix masks166 1664 = countPrefix masks166 1600 + blockCount masks166 1600 :=
      prefix_step masks166 1600
    _ = 32 := by rw [calib166_prefix25, calib166_block25]

theorem calib166_block26 : blockCount masks166 1664 = 0 := by
  decide +kernel

theorem calib166_prefix27 : countPrefix masks166 1728 = 32 := by
  calc
    countPrefix masks166 1728 = countPrefix masks166 1664 + blockCount masks166 1664 :=
      prefix_step masks166 1664
    _ = 32 := by rw [calib166_prefix26, calib166_block26]

theorem calib166_block27 : blockCount masks166 1728 = 0 := by
  decide +kernel

theorem calib166_prefix28 : countPrefix masks166 1792 = 32 := by
  calc
    countPrefix masks166 1792 = countPrefix masks166 1728 + blockCount masks166 1728 :=
      prefix_step masks166 1728
    _ = 32 := by rw [calib166_prefix27, calib166_block27]

theorem calib166_block28 : blockCount masks166 1792 = 0 := by
  decide +kernel

theorem calib166_prefix29 : countPrefix masks166 1856 = 32 := by
  calc
    countPrefix masks166 1856 = countPrefix masks166 1792 + blockCount masks166 1792 :=
      prefix_step masks166 1792
    _ = 32 := by rw [calib166_prefix28, calib166_block28]

theorem calib166_block29 : blockCount masks166 1856 = 0 := by
  decide +kernel

theorem calib166_prefix30 : countPrefix masks166 1920 = 32 := by
  calc
    countPrefix masks166 1920 = countPrefix masks166 1856 + blockCount masks166 1856 :=
      prefix_step masks166 1856
    _ = 32 := by rw [calib166_prefix29, calib166_block29]

theorem calib166_block30 : blockCount masks166 1920 = 0 := by
  decide +kernel

theorem calib166_prefix31 : countPrefix masks166 1984 = 32 := by
  calc
    countPrefix masks166 1984 = countPrefix masks166 1920 + blockCount masks166 1920 :=
      prefix_step masks166 1920
    _ = 32 := by rw [calib166_prefix30, calib166_block30]

theorem calib166_block31 : blockCount masks166 1984 = 0 := by
  decide +kernel

theorem calib166_prefix32 : countPrefix masks166 2048 = 32 := by
  calc
    countPrefix masks166 2048 = countPrefix masks166 1984 + blockCount masks166 1984 :=
      prefix_step masks166 1984
    _ = 32 := by rw [calib166_prefix31, calib166_block31]


end Paper6Calib

#print axioms Paper6Calib.calib166_block24
#print axioms Paper6Calib.calib166_prefix25
#print axioms Paper6Calib.calib166_block25
#print axioms Paper6Calib.calib166_prefix26
#print axioms Paper6Calib.calib166_block26
#print axioms Paper6Calib.calib166_prefix27
#print axioms Paper6Calib.calib166_block27
#print axioms Paper6Calib.calib166_prefix28
#print axioms Paper6Calib.calib166_block28
#print axioms Paper6Calib.calib166_prefix29
#print axioms Paper6Calib.calib166_block29
#print axioms Paper6Calib.calib166_prefix30
#print axioms Paper6Calib.calib166_block30
#print axioms Paper6Calib.calib166_prefix31
#print axioms Paper6Calib.calib166_block31
#print axioms Paper6Calib.calib166_prefix32
