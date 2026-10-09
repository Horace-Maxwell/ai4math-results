import Research.Backfill.Paper6.Calib162Part05

/-! Unverified candidate: weight 162, point blocks 48 through 55. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block48 : blockCount masks162 3072 = 1 := by
  decide +kernel

theorem calib162_prefix49 : countPrefix masks162 3136 = 105 := by
  calc
    countPrefix masks162 3136 = countPrefix masks162 3072 + blockCount masks162 3072 :=
      prefix_step masks162 3072
    _ = 105 := by rw [calib162_prefix48, calib162_block48]

theorem calib162_block49 : blockCount masks162 3136 = 1 := by
  decide +kernel

theorem calib162_prefix50 : countPrefix masks162 3200 = 106 := by
  calc
    countPrefix masks162 3200 = countPrefix masks162 3136 + blockCount masks162 3136 :=
      prefix_step masks162 3136
    _ = 106 := by rw [calib162_prefix49, calib162_block49]

theorem calib162_block50 : blockCount masks162 3200 = 7 := by
  decide +kernel

theorem calib162_prefix51 : countPrefix masks162 3264 = 113 := by
  calc
    countPrefix masks162 3264 = countPrefix masks162 3200 + blockCount masks162 3200 :=
      prefix_step masks162 3200
    _ = 113 := by rw [calib162_prefix50, calib162_block50]

theorem calib162_block51 : blockCount masks162 3264 = 5 := by
  decide +kernel

theorem calib162_prefix52 : countPrefix masks162 3328 = 118 := by
  calc
    countPrefix masks162 3328 = countPrefix masks162 3264 + blockCount masks162 3264 :=
      prefix_step masks162 3264
    _ = 118 := by rw [calib162_prefix51, calib162_block51]

theorem calib162_block52 : blockCount masks162 3328 = 1 := by
  decide +kernel

theorem calib162_prefix53 : countPrefix masks162 3392 = 119 := by
  calc
    countPrefix masks162 3392 = countPrefix masks162 3328 + blockCount masks162 3328 :=
      prefix_step masks162 3328
    _ = 119 := by rw [calib162_prefix52, calib162_block52]

theorem calib162_block53 : blockCount masks162 3392 = 1 := by
  decide +kernel

theorem calib162_prefix54 : countPrefix masks162 3456 = 120 := by
  calc
    countPrefix masks162 3456 = countPrefix masks162 3392 + blockCount masks162 3392 :=
      prefix_step masks162 3392
    _ = 120 := by rw [calib162_prefix53, calib162_block53]

theorem calib162_block54 : blockCount masks162 3456 = 7 := by
  decide +kernel

theorem calib162_prefix55 : countPrefix masks162 3520 = 127 := by
  calc
    countPrefix masks162 3520 = countPrefix masks162 3456 + blockCount masks162 3456 :=
      prefix_step masks162 3456
    _ = 127 := by rw [calib162_prefix54, calib162_block54]

theorem calib162_block55 : blockCount masks162 3520 = 7 := by
  decide +kernel

theorem calib162_prefix56 : countPrefix masks162 3584 = 134 := by
  calc
    countPrefix masks162 3584 = countPrefix masks162 3520 + blockCount masks162 3520 :=
      prefix_step masks162 3520
    _ = 134 := by rw [calib162_prefix55, calib162_block55]


end Paper6Calib

#print axioms Paper6Calib.calib162_block48
#print axioms Paper6Calib.calib162_prefix49
#print axioms Paper6Calib.calib162_block49
#print axioms Paper6Calib.calib162_prefix50
#print axioms Paper6Calib.calib162_block50
#print axioms Paper6Calib.calib162_prefix51
#print axioms Paper6Calib.calib162_block51
#print axioms Paper6Calib.calib162_prefix52
#print axioms Paper6Calib.calib162_block52
#print axioms Paper6Calib.calib162_prefix53
#print axioms Paper6Calib.calib162_block53
#print axioms Paper6Calib.calib162_prefix54
#print axioms Paper6Calib.calib162_block54
#print axioms Paper6Calib.calib162_prefix55
#print axioms Paper6Calib.calib162_block55
#print axioms Paper6Calib.calib162_prefix56
