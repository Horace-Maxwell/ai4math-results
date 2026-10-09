import Research.Backfill.Paper6.Calib174Part02

/-! Weight 174, blocks 24 through 31. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_block24 : blockCount masks174 1536 = 0 := by
  decide +kernel

theorem calib174_prefix25 : countPrefix masks174 1600 = 32 := by
  calc
    countPrefix masks174 1600 = countPrefix masks174 1536 + blockCount masks174 1536 :=
      prefix_step masks174 1536
    _ = 32 := by rw [calib174_prefix24, calib174_block24]

theorem calib174_block25 : blockCount masks174 1600 = 0 := by
  decide +kernel

theorem calib174_prefix26 : countPrefix masks174 1664 = 32 := by
  calc
    countPrefix masks174 1664 = countPrefix masks174 1600 + blockCount masks174 1600 :=
      prefix_step masks174 1600
    _ = 32 := by rw [calib174_prefix25, calib174_block25]

theorem calib174_block26 : blockCount masks174 1664 = 0 := by
  decide +kernel

theorem calib174_prefix27 : countPrefix masks174 1728 = 32 := by
  calc
    countPrefix masks174 1728 = countPrefix masks174 1664 + blockCount masks174 1664 :=
      prefix_step masks174 1664
    _ = 32 := by rw [calib174_prefix26, calib174_block26]

theorem calib174_block27 : blockCount masks174 1728 = 0 := by
  decide +kernel

theorem calib174_prefix28 : countPrefix masks174 1792 = 32 := by
  calc
    countPrefix masks174 1792 = countPrefix masks174 1728 + blockCount masks174 1728 :=
      prefix_step masks174 1728
    _ = 32 := by rw [calib174_prefix27, calib174_block27]

theorem calib174_block28 : blockCount masks174 1792 = 0 := by
  decide +kernel

theorem calib174_prefix29 : countPrefix masks174 1856 = 32 := by
  calc
    countPrefix masks174 1856 = countPrefix masks174 1792 + blockCount masks174 1792 :=
      prefix_step masks174 1792
    _ = 32 := by rw [calib174_prefix28, calib174_block28]

theorem calib174_block29 : blockCount masks174 1856 = 0 := by
  decide +kernel

theorem calib174_prefix30 : countPrefix masks174 1920 = 32 := by
  calc
    countPrefix masks174 1920 = countPrefix masks174 1856 + blockCount masks174 1856 :=
      prefix_step masks174 1856
    _ = 32 := by rw [calib174_prefix29, calib174_block29]

theorem calib174_block30 : blockCount masks174 1920 = 0 := by
  decide +kernel

theorem calib174_prefix31 : countPrefix masks174 1984 = 32 := by
  calc
    countPrefix masks174 1984 = countPrefix masks174 1920 + blockCount masks174 1920 :=
      prefix_step masks174 1920
    _ = 32 := by rw [calib174_prefix30, calib174_block30]

theorem calib174_block31 : blockCount masks174 1984 = 0 := by
  decide +kernel

theorem calib174_prefix32 : countPrefix masks174 2048 = 32 := by
  calc
    countPrefix masks174 2048 = countPrefix masks174 1984 + blockCount masks174 1984 :=
      prefix_step masks174 1984
    _ = 32 := by rw [calib174_prefix31, calib174_block31]


end Paper6Calib

#print axioms Paper6Calib.calib174_block24
#print axioms Paper6Calib.calib174_prefix25
#print axioms Paper6Calib.calib174_block25
#print axioms Paper6Calib.calib174_prefix26
#print axioms Paper6Calib.calib174_block26
#print axioms Paper6Calib.calib174_prefix27
#print axioms Paper6Calib.calib174_block27
#print axioms Paper6Calib.calib174_prefix28
#print axioms Paper6Calib.calib174_block28
#print axioms Paper6Calib.calib174_prefix29
#print axioms Paper6Calib.calib174_block29
#print axioms Paper6Calib.calib174_prefix30
#print axioms Paper6Calib.calib174_block30
#print axioms Paper6Calib.calib174_prefix31
#print axioms Paper6Calib.calib174_block31
#print axioms Paper6Calib.calib174_prefix32
