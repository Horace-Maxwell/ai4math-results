import Research.Backfill.Paper6.Calib162Part02

/-! Unverified candidate: weight 162, point blocks 24 through 31. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block24 : blockCount masks162 1536 = 1 := by
  decide +kernel

theorem calib162_prefix25 : countPrefix masks162 1600 = 25 := by
  calc
    countPrefix masks162 1600 = countPrefix masks162 1536 + blockCount masks162 1536 :=
      prefix_step masks162 1536
    _ = 25 := by rw [calib162_prefix24, calib162_block24]

theorem calib162_block25 : blockCount masks162 1600 = 1 := by
  decide +kernel

theorem calib162_prefix26 : countPrefix masks162 1664 = 26 := by
  calc
    countPrefix masks162 1664 = countPrefix masks162 1600 + blockCount masks162 1600 :=
      prefix_step masks162 1600
    _ = 26 := by rw [calib162_prefix25, calib162_block25]

theorem calib162_block26 : blockCount masks162 1664 = 1 := by
  decide +kernel

theorem calib162_prefix27 : countPrefix masks162 1728 = 27 := by
  calc
    countPrefix masks162 1728 = countPrefix masks162 1664 + blockCount masks162 1664 :=
      prefix_step masks162 1664
    _ = 27 := by rw [calib162_prefix26, calib162_block26]

theorem calib162_block27 : blockCount masks162 1728 = 1 := by
  decide +kernel

theorem calib162_prefix28 : countPrefix masks162 1792 = 28 := by
  calc
    countPrefix masks162 1792 = countPrefix masks162 1728 + blockCount masks162 1728 :=
      prefix_step masks162 1728
    _ = 28 := by rw [calib162_prefix27, calib162_block27]

theorem calib162_block28 : blockCount masks162 1792 = 1 := by
  decide +kernel

theorem calib162_prefix29 : countPrefix masks162 1856 = 29 := by
  calc
    countPrefix masks162 1856 = countPrefix masks162 1792 + blockCount masks162 1792 :=
      prefix_step masks162 1792
    _ = 29 := by rw [calib162_prefix28, calib162_block28]

theorem calib162_block29 : blockCount masks162 1856 = 1 := by
  decide +kernel

theorem calib162_prefix30 : countPrefix masks162 1920 = 30 := by
  calc
    countPrefix masks162 1920 = countPrefix masks162 1856 + blockCount masks162 1856 :=
      prefix_step masks162 1856
    _ = 30 := by rw [calib162_prefix29, calib162_block29]

theorem calib162_block30 : blockCount masks162 1920 = 1 := by
  decide +kernel

theorem calib162_prefix31 : countPrefix masks162 1984 = 31 := by
  calc
    countPrefix masks162 1984 = countPrefix masks162 1920 + blockCount masks162 1920 :=
      prefix_step masks162 1920
    _ = 31 := by rw [calib162_prefix30, calib162_block30]

theorem calib162_block31 : blockCount masks162 1984 = 1 := by
  decide +kernel

theorem calib162_prefix32 : countPrefix masks162 2048 = 32 := by
  calc
    countPrefix masks162 2048 = countPrefix masks162 1984 + blockCount masks162 1984 :=
      prefix_step masks162 1984
    _ = 32 := by rw [calib162_prefix31, calib162_block31]


end Paper6Calib

#print axioms Paper6Calib.calib162_block24
#print axioms Paper6Calib.calib162_prefix25
#print axioms Paper6Calib.calib162_block25
#print axioms Paper6Calib.calib162_prefix26
#print axioms Paper6Calib.calib162_block26
#print axioms Paper6Calib.calib162_prefix27
#print axioms Paper6Calib.calib162_block27
#print axioms Paper6Calib.calib162_prefix28
#print axioms Paper6Calib.calib162_block28
#print axioms Paper6Calib.calib162_prefix29
#print axioms Paper6Calib.calib162_block29
#print axioms Paper6Calib.calib162_prefix30
#print axioms Paper6Calib.calib162_block30
#print axioms Paper6Calib.calib162_prefix31
#print axioms Paper6Calib.calib162_block31
#print axioms Paper6Calib.calib162_prefix32
