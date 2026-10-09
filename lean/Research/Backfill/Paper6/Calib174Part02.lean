import Research.Backfill.Paper6.Calib174Part01

/-! Weight 174, blocks 16 through 23. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_block16 : blockCount masks174 1024 = 0 := by
  decide +kernel

theorem calib174_prefix17 : countPrefix masks174 1088 = 16 := by
  calc
    countPrefix masks174 1088 = countPrefix masks174 1024 + blockCount masks174 1024 :=
      prefix_step masks174 1024
    _ = 16 := by rw [calib174_prefix16, calib174_block16]

theorem calib174_block17 : blockCount masks174 1088 = 0 := by
  decide +kernel

theorem calib174_prefix18 : countPrefix masks174 1152 = 16 := by
  calc
    countPrefix masks174 1152 = countPrefix masks174 1088 + blockCount masks174 1088 :=
      prefix_step masks174 1088
    _ = 16 := by rw [calib174_prefix17, calib174_block17]

theorem calib174_block18 : blockCount masks174 1152 = 4 := by
  decide +kernel

theorem calib174_prefix19 : countPrefix masks174 1216 = 20 := by
  calc
    countPrefix masks174 1216 = countPrefix masks174 1152 + blockCount masks174 1152 :=
      prefix_step masks174 1152
    _ = 20 := by rw [calib174_prefix18, calib174_block18]

theorem calib174_block19 : blockCount masks174 1216 = 4 := by
  decide +kernel

theorem calib174_prefix20 : countPrefix masks174 1280 = 24 := by
  calc
    countPrefix masks174 1280 = countPrefix masks174 1216 + blockCount masks174 1216 :=
      prefix_step masks174 1216
    _ = 24 := by rw [calib174_prefix19, calib174_block19]

theorem calib174_block20 : blockCount masks174 1280 = 4 := by
  decide +kernel

theorem calib174_prefix21 : countPrefix masks174 1344 = 28 := by
  calc
    countPrefix masks174 1344 = countPrefix masks174 1280 + blockCount masks174 1280 :=
      prefix_step masks174 1280
    _ = 28 := by rw [calib174_prefix20, calib174_block20]

theorem calib174_block21 : blockCount masks174 1344 = 4 := by
  decide +kernel

theorem calib174_prefix22 : countPrefix masks174 1408 = 32 := by
  calc
    countPrefix masks174 1408 = countPrefix masks174 1344 + blockCount masks174 1344 :=
      prefix_step masks174 1344
    _ = 32 := by rw [calib174_prefix21, calib174_block21]

theorem calib174_block22 : blockCount masks174 1408 = 0 := by
  decide +kernel

theorem calib174_prefix23 : countPrefix masks174 1472 = 32 := by
  calc
    countPrefix masks174 1472 = countPrefix masks174 1408 + blockCount masks174 1408 :=
      prefix_step masks174 1408
    _ = 32 := by rw [calib174_prefix22, calib174_block22]

theorem calib174_block23 : blockCount masks174 1472 = 0 := by
  decide +kernel

theorem calib174_prefix24 : countPrefix masks174 1536 = 32 := by
  calc
    countPrefix masks174 1536 = countPrefix masks174 1472 + blockCount masks174 1472 :=
      prefix_step masks174 1472
    _ = 32 := by rw [calib174_prefix23, calib174_block23]


end Paper6Calib

#print axioms Paper6Calib.calib174_block16
#print axioms Paper6Calib.calib174_prefix17
#print axioms Paper6Calib.calib174_block17
#print axioms Paper6Calib.calib174_prefix18
#print axioms Paper6Calib.calib174_block18
#print axioms Paper6Calib.calib174_prefix19
#print axioms Paper6Calib.calib174_block19
#print axioms Paper6Calib.calib174_prefix20
#print axioms Paper6Calib.calib174_block20
#print axioms Paper6Calib.calib174_prefix21
#print axioms Paper6Calib.calib174_block21
#print axioms Paper6Calib.calib174_prefix22
#print axioms Paper6Calib.calib174_block22
#print axioms Paper6Calib.calib174_prefix23
#print axioms Paper6Calib.calib174_block23
#print axioms Paper6Calib.calib174_prefix24
