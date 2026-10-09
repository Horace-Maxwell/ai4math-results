import Research.Backfill.Paper6.Calib166Part05

/-! Weight 166, blocks 48 through 55. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block48 : blockCount masks166 3072 = 0 := by
  decide +kernel

theorem calib166_prefix49 : countPrefix masks166 3136 = 110 := by
  calc
    countPrefix masks166 3136 = countPrefix masks166 3072 + blockCount masks166 3072 :=
      prefix_step masks166 3072
    _ = 110 := by rw [calib166_prefix48, calib166_block48]

theorem calib166_block49 : blockCount masks166 3136 = 0 := by
  decide +kernel

theorem calib166_prefix50 : countPrefix masks166 3200 = 110 := by
  calc
    countPrefix masks166 3200 = countPrefix masks166 3136 + blockCount masks166 3136 :=
      prefix_step masks166 3136
    _ = 110 := by rw [calib166_prefix49, calib166_block49]

theorem calib166_block50 : blockCount masks166 3200 = 0 := by
  decide +kernel

theorem calib166_prefix51 : countPrefix masks166 3264 = 110 := by
  calc
    countPrefix masks166 3264 = countPrefix masks166 3200 + blockCount masks166 3200 :=
      prefix_step masks166 3200
    _ = 110 := by rw [calib166_prefix50, calib166_block50]

theorem calib166_block51 : blockCount masks166 3264 = 0 := by
  decide +kernel

theorem calib166_prefix52 : countPrefix masks166 3328 = 110 := by
  calc
    countPrefix masks166 3328 = countPrefix masks166 3264 + blockCount masks166 3264 :=
      prefix_step masks166 3264
    _ = 110 := by rw [calib166_prefix51, calib166_block51]

theorem calib166_block52 : blockCount masks166 3328 = 8 := by
  decide +kernel

theorem calib166_prefix53 : countPrefix masks166 3392 = 118 := by
  calc
    countPrefix masks166 3392 = countPrefix masks166 3328 + blockCount masks166 3328 :=
      prefix_step masks166 3328
    _ = 118 := by rw [calib166_prefix52, calib166_block52]

theorem calib166_block53 : blockCount masks166 3392 = 12 := by
  decide +kernel

theorem calib166_prefix54 : countPrefix masks166 3456 = 130 := by
  calc
    countPrefix masks166 3456 = countPrefix masks166 3392 + blockCount masks166 3392 :=
      prefix_step masks166 3392
    _ = 130 := by rw [calib166_prefix53, calib166_block53]

theorem calib166_block54 : blockCount masks166 3456 = 12 := by
  decide +kernel

theorem calib166_prefix55 : countPrefix masks166 3520 = 142 := by
  calc
    countPrefix masks166 3520 = countPrefix masks166 3456 + blockCount masks166 3456 :=
      prefix_step masks166 3456
    _ = 142 := by rw [calib166_prefix54, calib166_block54]

theorem calib166_block55 : blockCount masks166 3520 = 8 := by
  decide +kernel

theorem calib166_prefix56 : countPrefix masks166 3584 = 150 := by
  calc
    countPrefix masks166 3584 = countPrefix masks166 3520 + blockCount masks166 3520 :=
      prefix_step masks166 3520
    _ = 150 := by rw [calib166_prefix55, calib166_block55]


end Paper6Calib

#print axioms Paper6Calib.calib166_block48
#print axioms Paper6Calib.calib166_prefix49
#print axioms Paper6Calib.calib166_block49
#print axioms Paper6Calib.calib166_prefix50
#print axioms Paper6Calib.calib166_block50
#print axioms Paper6Calib.calib166_prefix51
#print axioms Paper6Calib.calib166_block51
#print axioms Paper6Calib.calib166_prefix52
#print axioms Paper6Calib.calib166_block52
#print axioms Paper6Calib.calib166_prefix53
#print axioms Paper6Calib.calib166_block53
#print axioms Paper6Calib.calib166_prefix54
#print axioms Paper6Calib.calib166_block54
#print axioms Paper6Calib.calib166_prefix55
#print axioms Paper6Calib.calib166_block55
#print axioms Paper6Calib.calib166_prefix56
