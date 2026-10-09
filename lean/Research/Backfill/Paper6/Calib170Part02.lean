import Research.Backfill.Paper6.Calib170Part01

/-! Weight 170, blocks 16 through 23. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block16 : blockCount masks170 1024 = 0 := by
  decide +kernel

theorem calib170_prefix17 : countPrefix masks170 1088 = 32 := by
  calc
    countPrefix masks170 1088 = countPrefix masks170 1024 + blockCount masks170 1024 :=
      prefix_step masks170 1024
    _ = 32 := by rw [calib170_prefix16, calib170_block16]

theorem calib170_block17 : blockCount masks170 1088 = 0 := by
  decide +kernel

theorem calib170_prefix18 : countPrefix masks170 1152 = 32 := by
  calc
    countPrefix masks170 1152 = countPrefix masks170 1088 + blockCount masks170 1088 :=
      prefix_step masks170 1088
    _ = 32 := by rw [calib170_prefix17, calib170_block17]

theorem calib170_block18 : blockCount masks170 1152 = 0 := by
  decide +kernel

theorem calib170_prefix19 : countPrefix masks170 1216 = 32 := by
  calc
    countPrefix masks170 1216 = countPrefix masks170 1152 + blockCount masks170 1152 :=
      prefix_step masks170 1152
    _ = 32 := by rw [calib170_prefix18, calib170_block18]

theorem calib170_block19 : blockCount masks170 1216 = 0 := by
  decide +kernel

theorem calib170_prefix20 : countPrefix masks170 1280 = 32 := by
  calc
    countPrefix masks170 1280 = countPrefix masks170 1216 + blockCount masks170 1216 :=
      prefix_step masks170 1216
    _ = 32 := by rw [calib170_prefix19, calib170_block19]

theorem calib170_block20 : blockCount masks170 1280 = 0 := by
  decide +kernel

theorem calib170_prefix21 : countPrefix masks170 1344 = 32 := by
  calc
    countPrefix masks170 1344 = countPrefix masks170 1280 + blockCount masks170 1280 :=
      prefix_step masks170 1280
    _ = 32 := by rw [calib170_prefix20, calib170_block20]

theorem calib170_block21 : blockCount masks170 1344 = 0 := by
  decide +kernel

theorem calib170_prefix22 : countPrefix masks170 1408 = 32 := by
  calc
    countPrefix masks170 1408 = countPrefix masks170 1344 + blockCount masks170 1344 :=
      prefix_step masks170 1344
    _ = 32 := by rw [calib170_prefix21, calib170_block21]

theorem calib170_block22 : blockCount masks170 1408 = 0 := by
  decide +kernel

theorem calib170_prefix23 : countPrefix masks170 1472 = 32 := by
  calc
    countPrefix masks170 1472 = countPrefix masks170 1408 + blockCount masks170 1408 :=
      prefix_step masks170 1408
    _ = 32 := by rw [calib170_prefix22, calib170_block22]

theorem calib170_block23 : blockCount masks170 1472 = 0 := by
  decide +kernel

theorem calib170_prefix24 : countPrefix masks170 1536 = 32 := by
  calc
    countPrefix masks170 1536 = countPrefix masks170 1472 + blockCount masks170 1472 :=
      prefix_step masks170 1472
    _ = 32 := by rw [calib170_prefix23, calib170_block23]


end Paper6Calib

#print axioms Paper6Calib.calib170_block16
#print axioms Paper6Calib.calib170_prefix17
#print axioms Paper6Calib.calib170_block17
#print axioms Paper6Calib.calib170_prefix18
#print axioms Paper6Calib.calib170_block18
#print axioms Paper6Calib.calib170_prefix19
#print axioms Paper6Calib.calib170_block19
#print axioms Paper6Calib.calib170_prefix20
#print axioms Paper6Calib.calib170_block20
#print axioms Paper6Calib.calib170_prefix21
#print axioms Paper6Calib.calib170_block21
#print axioms Paper6Calib.calib170_prefix22
#print axioms Paper6Calib.calib170_block22
#print axioms Paper6Calib.calib170_prefix23
#print axioms Paper6Calib.calib170_block23
#print axioms Paper6Calib.calib170_prefix24
