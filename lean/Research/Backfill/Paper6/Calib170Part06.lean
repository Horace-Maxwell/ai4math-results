import Research.Backfill.Paper6.Calib170Part05

/-! Weight 170, blocks 48 through 55. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block48 : blockCount masks170 3072 = 2 := by
  decide +kernel

theorem calib170_prefix49 : countPrefix masks170 3136 = 98 := by
  calc
    countPrefix masks170 3136 = countPrefix masks170 3072 + blockCount masks170 3072 :=
      prefix_step masks170 3072
    _ = 98 := by rw [calib170_prefix48, calib170_block48]

theorem calib170_block49 : blockCount masks170 3136 = 2 := by
  decide +kernel

theorem calib170_prefix50 : countPrefix masks170 3200 = 100 := by
  calc
    countPrefix masks170 3200 = countPrefix masks170 3136 + blockCount masks170 3136 :=
      prefix_step masks170 3136
    _ = 100 := by rw [calib170_prefix49, calib170_block49]

theorem calib170_block50 : blockCount masks170 3200 = 6 := by
  decide +kernel

theorem calib170_prefix51 : countPrefix masks170 3264 = 106 := by
  calc
    countPrefix masks170 3264 = countPrefix masks170 3200 + blockCount masks170 3200 :=
      prefix_step masks170 3200
    _ = 106 := by rw [calib170_prefix50, calib170_block50]

theorem calib170_block51 : blockCount masks170 3264 = 8 := by
  decide +kernel

theorem calib170_prefix52 : countPrefix masks170 3328 = 114 := by
  calc
    countPrefix masks170 3328 = countPrefix masks170 3264 + blockCount masks170 3264 :=
      prefix_step masks170 3264
    _ = 114 := by rw [calib170_prefix51, calib170_block51]

theorem calib170_block52 : blockCount masks170 3328 = 4 := by
  decide +kernel

theorem calib170_prefix53 : countPrefix masks170 3392 = 118 := by
  calc
    countPrefix masks170 3392 = countPrefix masks170 3328 + blockCount masks170 3328 :=
      prefix_step masks170 3328
    _ = 118 := by rw [calib170_prefix52, calib170_block52]

theorem calib170_block53 : blockCount masks170 3392 = 6 := by
  decide +kernel

theorem calib170_prefix54 : countPrefix masks170 3456 = 124 := by
  calc
    countPrefix masks170 3456 = countPrefix masks170 3392 + blockCount masks170 3392 :=
      prefix_step masks170 3392
    _ = 124 := by rw [calib170_prefix53, calib170_block53]

theorem calib170_block54 : blockCount masks170 3456 = 2 := by
  decide +kernel

theorem calib170_prefix55 : countPrefix masks170 3520 = 126 := by
  calc
    countPrefix masks170 3520 = countPrefix masks170 3456 + blockCount masks170 3456 :=
      prefix_step masks170 3456
    _ = 126 := by rw [calib170_prefix54, calib170_block54]

theorem calib170_block55 : blockCount masks170 3520 = 6 := by
  decide +kernel

theorem calib170_prefix56 : countPrefix masks170 3584 = 132 := by
  calc
    countPrefix masks170 3584 = countPrefix masks170 3520 + blockCount masks170 3520 :=
      prefix_step masks170 3520
    _ = 132 := by rw [calib170_prefix55, calib170_block55]


end Paper6Calib

#print axioms Paper6Calib.calib170_block48
#print axioms Paper6Calib.calib170_prefix49
#print axioms Paper6Calib.calib170_block49
#print axioms Paper6Calib.calib170_prefix50
#print axioms Paper6Calib.calib170_block50
#print axioms Paper6Calib.calib170_prefix51
#print axioms Paper6Calib.calib170_block51
#print axioms Paper6Calib.calib170_prefix52
#print axioms Paper6Calib.calib170_block52
#print axioms Paper6Calib.calib170_prefix53
#print axioms Paper6Calib.calib170_block53
#print axioms Paper6Calib.calib170_prefix54
#print axioms Paper6Calib.calib170_block54
#print axioms Paper6Calib.calib170_prefix55
#print axioms Paper6Calib.calib170_block55
#print axioms Paper6Calib.calib170_prefix56
