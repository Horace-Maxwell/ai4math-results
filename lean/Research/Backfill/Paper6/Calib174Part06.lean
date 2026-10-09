import Research.Backfill.Paper6.Calib174Part05

/-! Weight 174, blocks 48 through 55. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_block48 : blockCount masks174 3072 = 2 := by
  decide +kernel

theorem calib174_prefix49 : countPrefix masks174 3136 = 114 := by
  calc
    countPrefix masks174 3136 = countPrefix masks174 3072 + blockCount masks174 3072 :=
      prefix_step masks174 3072
    _ = 114 := by rw [calib174_prefix48, calib174_block48]

theorem calib174_block49 : blockCount masks174 3136 = 2 := by
  decide +kernel

theorem calib174_prefix50 : countPrefix masks174 3200 = 116 := by
  calc
    countPrefix masks174 3200 = countPrefix masks174 3136 + blockCount masks174 3136 :=
      prefix_step masks174 3136
    _ = 116 := by rw [calib174_prefix49, calib174_block49]

theorem calib174_block50 : blockCount masks174 3200 = 2 := by
  decide +kernel

theorem calib174_prefix51 : countPrefix masks174 3264 = 118 := by
  calc
    countPrefix masks174 3264 = countPrefix masks174 3200 + blockCount masks174 3200 :=
      prefix_step masks174 3200
    _ = 118 := by rw [calib174_prefix50, calib174_block50]

theorem calib174_block51 : blockCount masks174 3264 = 6 := by
  decide +kernel

theorem calib174_prefix52 : countPrefix masks174 3328 = 124 := by
  calc
    countPrefix masks174 3328 = countPrefix masks174 3264 + blockCount masks174 3264 :=
      prefix_step masks174 3264
    _ = 124 := by rw [calib174_prefix51, calib174_block51]

theorem calib174_block52 : blockCount masks174 3328 = 2 := by
  decide +kernel

theorem calib174_prefix53 : countPrefix masks174 3392 = 126 := by
  calc
    countPrefix masks174 3392 = countPrefix masks174 3328 + blockCount masks174 3328 :=
      prefix_step masks174 3328
    _ = 126 := by rw [calib174_prefix52, calib174_block52]

theorem calib174_block53 : blockCount masks174 3392 = 2 := by
  decide +kernel

theorem calib174_prefix54 : countPrefix masks174 3456 = 128 := by
  calc
    countPrefix masks174 3456 = countPrefix masks174 3392 + blockCount masks174 3392 :=
      prefix_step masks174 3392
    _ = 128 := by rw [calib174_prefix53, calib174_block53]

theorem calib174_block54 : blockCount masks174 3456 = 2 := by
  decide +kernel

theorem calib174_prefix55 : countPrefix masks174 3520 = 130 := by
  calc
    countPrefix masks174 3520 = countPrefix masks174 3456 + blockCount masks174 3456 :=
      prefix_step masks174 3456
    _ = 130 := by rw [calib174_prefix54, calib174_block54]

theorem calib174_block55 : blockCount masks174 3520 = 6 := by
  decide +kernel

theorem calib174_prefix56 : countPrefix masks174 3584 = 136 := by
  calc
    countPrefix masks174 3584 = countPrefix masks174 3520 + blockCount masks174 3520 :=
      prefix_step masks174 3520
    _ = 136 := by rw [calib174_prefix55, calib174_block55]


end Paper6Calib

#print axioms Paper6Calib.calib174_block48
#print axioms Paper6Calib.calib174_prefix49
#print axioms Paper6Calib.calib174_block49
#print axioms Paper6Calib.calib174_prefix50
#print axioms Paper6Calib.calib174_block50
#print axioms Paper6Calib.calib174_prefix51
#print axioms Paper6Calib.calib174_block51
#print axioms Paper6Calib.calib174_prefix52
#print axioms Paper6Calib.calib174_block52
#print axioms Paper6Calib.calib174_prefix53
#print axioms Paper6Calib.calib174_block53
#print axioms Paper6Calib.calib174_prefix54
#print axioms Paper6Calib.calib174_block54
#print axioms Paper6Calib.calib174_prefix55
#print axioms Paper6Calib.calib174_block55
#print axioms Paper6Calib.calib174_prefix56
