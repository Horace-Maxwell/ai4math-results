import Research.Backfill.Paper6.Calib166Part01

/-! Weight 166, blocks 16 through 23. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block16 : blockCount masks166 1024 = 0 := by
  decide +kernel

theorem calib166_prefix17 : countPrefix masks166 1088 = 32 := by
  calc
    countPrefix masks166 1088 = countPrefix masks166 1024 + blockCount masks166 1024 :=
      prefix_step masks166 1024
    _ = 32 := by rw [calib166_prefix16, calib166_block16]

theorem calib166_block17 : blockCount masks166 1088 = 0 := by
  decide +kernel

theorem calib166_prefix18 : countPrefix masks166 1152 = 32 := by
  calc
    countPrefix masks166 1152 = countPrefix masks166 1088 + blockCount masks166 1088 :=
      prefix_step masks166 1088
    _ = 32 := by rw [calib166_prefix17, calib166_block17]

theorem calib166_block18 : blockCount masks166 1152 = 0 := by
  decide +kernel

theorem calib166_prefix19 : countPrefix masks166 1216 = 32 := by
  calc
    countPrefix masks166 1216 = countPrefix masks166 1152 + blockCount masks166 1152 :=
      prefix_step masks166 1152
    _ = 32 := by rw [calib166_prefix18, calib166_block18]

theorem calib166_block19 : blockCount masks166 1216 = 0 := by
  decide +kernel

theorem calib166_prefix20 : countPrefix masks166 1280 = 32 := by
  calc
    countPrefix masks166 1280 = countPrefix masks166 1216 + blockCount masks166 1216 :=
      prefix_step masks166 1216
    _ = 32 := by rw [calib166_prefix19, calib166_block19]

theorem calib166_block20 : blockCount masks166 1280 = 0 := by
  decide +kernel

theorem calib166_prefix21 : countPrefix masks166 1344 = 32 := by
  calc
    countPrefix masks166 1344 = countPrefix masks166 1280 + blockCount masks166 1280 :=
      prefix_step masks166 1280
    _ = 32 := by rw [calib166_prefix20, calib166_block20]

theorem calib166_block21 : blockCount masks166 1344 = 0 := by
  decide +kernel

theorem calib166_prefix22 : countPrefix masks166 1408 = 32 := by
  calc
    countPrefix masks166 1408 = countPrefix masks166 1344 + blockCount masks166 1344 :=
      prefix_step masks166 1344
    _ = 32 := by rw [calib166_prefix21, calib166_block21]

theorem calib166_block22 : blockCount masks166 1408 = 0 := by
  decide +kernel

theorem calib166_prefix23 : countPrefix masks166 1472 = 32 := by
  calc
    countPrefix masks166 1472 = countPrefix masks166 1408 + blockCount masks166 1408 :=
      prefix_step masks166 1408
    _ = 32 := by rw [calib166_prefix22, calib166_block22]

theorem calib166_block23 : blockCount masks166 1472 = 0 := by
  decide +kernel

theorem calib166_prefix24 : countPrefix masks166 1536 = 32 := by
  calc
    countPrefix masks166 1536 = countPrefix masks166 1472 + blockCount masks166 1472 :=
      prefix_step masks166 1472
    _ = 32 := by rw [calib166_prefix23, calib166_block23]


end Paper6Calib

#print axioms Paper6Calib.calib166_block16
#print axioms Paper6Calib.calib166_prefix17
#print axioms Paper6Calib.calib166_block17
#print axioms Paper6Calib.calib166_prefix18
#print axioms Paper6Calib.calib166_block18
#print axioms Paper6Calib.calib166_prefix19
#print axioms Paper6Calib.calib166_block19
#print axioms Paper6Calib.calib166_prefix20
#print axioms Paper6Calib.calib166_block20
#print axioms Paper6Calib.calib166_prefix21
#print axioms Paper6Calib.calib166_block21
#print axioms Paper6Calib.calib166_prefix22
#print axioms Paper6Calib.calib166_block22
#print axioms Paper6Calib.calib166_prefix23
#print axioms Paper6Calib.calib166_block23
#print axioms Paper6Calib.calib166_prefix24
