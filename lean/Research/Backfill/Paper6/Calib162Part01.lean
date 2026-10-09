import Research.Backfill.Paper6.Calib162Part00

/-! Unverified candidate: weight 162, point blocks 8 through 15. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block08 : blockCount masks162 512 = 1 := by
  decide +kernel

theorem calib162_prefix09 : countPrefix masks162 576 = 9 := by
  calc
    countPrefix masks162 576 = countPrefix masks162 512 + blockCount masks162 512 :=
      prefix_step masks162 512
    _ = 9 := by rw [calib162_prefix08, calib162_block08]

theorem calib162_block09 : blockCount masks162 576 = 1 := by
  decide +kernel

theorem calib162_prefix10 : countPrefix masks162 640 = 10 := by
  calc
    countPrefix masks162 640 = countPrefix masks162 576 + blockCount masks162 576 :=
      prefix_step masks162 576
    _ = 10 := by rw [calib162_prefix09, calib162_block09]

theorem calib162_block10 : blockCount masks162 640 = 1 := by
  decide +kernel

theorem calib162_prefix11 : countPrefix masks162 704 = 11 := by
  calc
    countPrefix masks162 704 = countPrefix masks162 640 + blockCount masks162 640 :=
      prefix_step masks162 640
    _ = 11 := by rw [calib162_prefix10, calib162_block10]

theorem calib162_block11 : blockCount masks162 704 = 1 := by
  decide +kernel

theorem calib162_prefix12 : countPrefix masks162 768 = 12 := by
  calc
    countPrefix masks162 768 = countPrefix masks162 704 + blockCount masks162 704 :=
      prefix_step masks162 704
    _ = 12 := by rw [calib162_prefix11, calib162_block11]

theorem calib162_block12 : blockCount masks162 768 = 1 := by
  decide +kernel

theorem calib162_prefix13 : countPrefix masks162 832 = 13 := by
  calc
    countPrefix masks162 832 = countPrefix masks162 768 + blockCount masks162 768 :=
      prefix_step masks162 768
    _ = 13 := by rw [calib162_prefix12, calib162_block12]

theorem calib162_block13 : blockCount masks162 832 = 1 := by
  decide +kernel

theorem calib162_prefix14 : countPrefix masks162 896 = 14 := by
  calc
    countPrefix masks162 896 = countPrefix masks162 832 + blockCount masks162 832 :=
      prefix_step masks162 832
    _ = 14 := by rw [calib162_prefix13, calib162_block13]

theorem calib162_block14 : blockCount masks162 896 = 1 := by
  decide +kernel

theorem calib162_prefix15 : countPrefix masks162 960 = 15 := by
  calc
    countPrefix masks162 960 = countPrefix masks162 896 + blockCount masks162 896 :=
      prefix_step masks162 896
    _ = 15 := by rw [calib162_prefix14, calib162_block14]

theorem calib162_block15 : blockCount masks162 960 = 1 := by
  decide +kernel

theorem calib162_prefix16 : countPrefix masks162 1024 = 16 := by
  calc
    countPrefix masks162 1024 = countPrefix masks162 960 + blockCount masks162 960 :=
      prefix_step masks162 960
    _ = 16 := by rw [calib162_prefix15, calib162_block15]


end Paper6Calib

#print axioms Paper6Calib.calib162_block08
#print axioms Paper6Calib.calib162_prefix09
#print axioms Paper6Calib.calib162_block09
#print axioms Paper6Calib.calib162_prefix10
#print axioms Paper6Calib.calib162_block10
#print axioms Paper6Calib.calib162_prefix11
#print axioms Paper6Calib.calib162_block11
#print axioms Paper6Calib.calib162_prefix12
#print axioms Paper6Calib.calib162_block12
#print axioms Paper6Calib.calib162_prefix13
#print axioms Paper6Calib.calib162_block13
#print axioms Paper6Calib.calib162_prefix14
#print axioms Paper6Calib.calib162_block14
#print axioms Paper6Calib.calib162_prefix15
#print axioms Paper6Calib.calib162_block15
#print axioms Paper6Calib.calib162_prefix16
