import Research.Backfill.Paper6.Calib170Part02

/-! Weight 170, blocks 24 through 31. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block24 : blockCount masks170 1536 = 0 := by
  decide +kernel

theorem calib170_prefix25 : countPrefix masks170 1600 = 32 := by
  calc
    countPrefix masks170 1600 = countPrefix masks170 1536 + blockCount masks170 1536 :=
      prefix_step masks170 1536
    _ = 32 := by rw [calib170_prefix24, calib170_block24]

theorem calib170_block25 : blockCount masks170 1600 = 0 := by
  decide +kernel

theorem calib170_prefix26 : countPrefix masks170 1664 = 32 := by
  calc
    countPrefix masks170 1664 = countPrefix masks170 1600 + blockCount masks170 1600 :=
      prefix_step masks170 1600
    _ = 32 := by rw [calib170_prefix25, calib170_block25]

theorem calib170_block26 : blockCount masks170 1664 = 0 := by
  decide +kernel

theorem calib170_prefix27 : countPrefix masks170 1728 = 32 := by
  calc
    countPrefix masks170 1728 = countPrefix masks170 1664 + blockCount masks170 1664 :=
      prefix_step masks170 1664
    _ = 32 := by rw [calib170_prefix26, calib170_block26]

theorem calib170_block27 : blockCount masks170 1728 = 0 := by
  decide +kernel

theorem calib170_prefix28 : countPrefix masks170 1792 = 32 := by
  calc
    countPrefix masks170 1792 = countPrefix masks170 1728 + blockCount masks170 1728 :=
      prefix_step masks170 1728
    _ = 32 := by rw [calib170_prefix27, calib170_block27]

theorem calib170_block28 : blockCount masks170 1792 = 0 := by
  decide +kernel

theorem calib170_prefix29 : countPrefix masks170 1856 = 32 := by
  calc
    countPrefix masks170 1856 = countPrefix masks170 1792 + blockCount masks170 1792 :=
      prefix_step masks170 1792
    _ = 32 := by rw [calib170_prefix28, calib170_block28]

theorem calib170_block29 : blockCount masks170 1856 = 0 := by
  decide +kernel

theorem calib170_prefix30 : countPrefix masks170 1920 = 32 := by
  calc
    countPrefix masks170 1920 = countPrefix masks170 1856 + blockCount masks170 1856 :=
      prefix_step masks170 1856
    _ = 32 := by rw [calib170_prefix29, calib170_block29]

theorem calib170_block30 : blockCount masks170 1920 = 0 := by
  decide +kernel

theorem calib170_prefix31 : countPrefix masks170 1984 = 32 := by
  calc
    countPrefix masks170 1984 = countPrefix masks170 1920 + blockCount masks170 1920 :=
      prefix_step masks170 1920
    _ = 32 := by rw [calib170_prefix30, calib170_block30]

theorem calib170_block31 : blockCount masks170 1984 = 0 := by
  decide +kernel

theorem calib170_prefix32 : countPrefix masks170 2048 = 32 := by
  calc
    countPrefix masks170 2048 = countPrefix masks170 1984 + blockCount masks170 1984 :=
      prefix_step masks170 1984
    _ = 32 := by rw [calib170_prefix31, calib170_block31]


end Paper6Calib

#print axioms Paper6Calib.calib170_block24
#print axioms Paper6Calib.calib170_prefix25
#print axioms Paper6Calib.calib170_block25
#print axioms Paper6Calib.calib170_prefix26
#print axioms Paper6Calib.calib170_block26
#print axioms Paper6Calib.calib170_prefix27
#print axioms Paper6Calib.calib170_block27
#print axioms Paper6Calib.calib170_prefix28
#print axioms Paper6Calib.calib170_block28
#print axioms Paper6Calib.calib170_prefix29
#print axioms Paper6Calib.calib170_block29
#print axioms Paper6Calib.calib170_prefix30
#print axioms Paper6Calib.calib170_block30
#print axioms Paper6Calib.calib170_prefix31
#print axioms Paper6Calib.calib170_block31
#print axioms Paper6Calib.calib170_prefix32
