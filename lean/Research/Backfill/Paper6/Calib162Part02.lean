import Research.Backfill.Paper6.Calib162Part01

/-! Unverified candidate: weight 162, point blocks 16 through 23. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block16 : blockCount masks162 1024 = 1 := by
  decide +kernel

theorem calib162_prefix17 : countPrefix masks162 1088 = 17 := by
  calc
    countPrefix masks162 1088 = countPrefix masks162 1024 + blockCount masks162 1024 :=
      prefix_step masks162 1024
    _ = 17 := by rw [calib162_prefix16, calib162_block16]

theorem calib162_block17 : blockCount masks162 1088 = 1 := by
  decide +kernel

theorem calib162_prefix18 : countPrefix masks162 1152 = 18 := by
  calc
    countPrefix masks162 1152 = countPrefix masks162 1088 + blockCount masks162 1088 :=
      prefix_step masks162 1088
    _ = 18 := by rw [calib162_prefix17, calib162_block17]

theorem calib162_block18 : blockCount masks162 1152 = 1 := by
  decide +kernel

theorem calib162_prefix19 : countPrefix masks162 1216 = 19 := by
  calc
    countPrefix masks162 1216 = countPrefix masks162 1152 + blockCount masks162 1152 :=
      prefix_step masks162 1152
    _ = 19 := by rw [calib162_prefix18, calib162_block18]

theorem calib162_block19 : blockCount masks162 1216 = 1 := by
  decide +kernel

theorem calib162_prefix20 : countPrefix masks162 1280 = 20 := by
  calc
    countPrefix masks162 1280 = countPrefix masks162 1216 + blockCount masks162 1216 :=
      prefix_step masks162 1216
    _ = 20 := by rw [calib162_prefix19, calib162_block19]

theorem calib162_block20 : blockCount masks162 1280 = 1 := by
  decide +kernel

theorem calib162_prefix21 : countPrefix masks162 1344 = 21 := by
  calc
    countPrefix masks162 1344 = countPrefix masks162 1280 + blockCount masks162 1280 :=
      prefix_step masks162 1280
    _ = 21 := by rw [calib162_prefix20, calib162_block20]

theorem calib162_block21 : blockCount masks162 1344 = 1 := by
  decide +kernel

theorem calib162_prefix22 : countPrefix masks162 1408 = 22 := by
  calc
    countPrefix masks162 1408 = countPrefix masks162 1344 + blockCount masks162 1344 :=
      prefix_step masks162 1344
    _ = 22 := by rw [calib162_prefix21, calib162_block21]

theorem calib162_block22 : blockCount masks162 1408 = 1 := by
  decide +kernel

theorem calib162_prefix23 : countPrefix masks162 1472 = 23 := by
  calc
    countPrefix masks162 1472 = countPrefix masks162 1408 + blockCount masks162 1408 :=
      prefix_step masks162 1408
    _ = 23 := by rw [calib162_prefix22, calib162_block22]

theorem calib162_block23 : blockCount masks162 1472 = 1 := by
  decide +kernel

theorem calib162_prefix24 : countPrefix masks162 1536 = 24 := by
  calc
    countPrefix masks162 1536 = countPrefix masks162 1472 + blockCount masks162 1472 :=
      prefix_step masks162 1472
    _ = 24 := by rw [calib162_prefix23, calib162_block23]


end Paper6Calib

#print axioms Paper6Calib.calib162_block16
#print axioms Paper6Calib.calib162_prefix17
#print axioms Paper6Calib.calib162_block17
#print axioms Paper6Calib.calib162_prefix18
#print axioms Paper6Calib.calib162_block18
#print axioms Paper6Calib.calib162_prefix19
#print axioms Paper6Calib.calib162_block19
#print axioms Paper6Calib.calib162_prefix20
#print axioms Paper6Calib.calib162_block20
#print axioms Paper6Calib.calib162_prefix21
#print axioms Paper6Calib.calib162_block21
#print axioms Paper6Calib.calib162_prefix22
#print axioms Paper6Calib.calib162_block22
#print axioms Paper6Calib.calib162_prefix23
#print axioms Paper6Calib.calib162_block23
#print axioms Paper6Calib.calib162_prefix24
