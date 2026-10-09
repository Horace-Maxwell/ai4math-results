import Research.Backfill.Paper6.CalibData

/-! Unverified candidate: weight 162, point blocks 0 through 7. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_prefix00 : countPrefix masks162 0 = 0 := rfl

theorem calib162_block00 : blockCount masks162 0 = 1 := by
  decide +kernel

theorem calib162_prefix01 : countPrefix masks162 64 = 1 := by
  calc
    countPrefix masks162 64 = countPrefix masks162 0 + blockCount masks162 0 :=
      prefix_step masks162 0
    _ = 1 := by rw [calib162_prefix00, calib162_block00]

theorem calib162_block01 : blockCount masks162 64 = 1 := by
  decide +kernel

theorem calib162_prefix02 : countPrefix masks162 128 = 2 := by
  calc
    countPrefix masks162 128 = countPrefix masks162 64 + blockCount masks162 64 :=
      prefix_step masks162 64
    _ = 2 := by rw [calib162_prefix01, calib162_block01]

theorem calib162_block02 : blockCount masks162 128 = 1 := by
  decide +kernel

theorem calib162_prefix03 : countPrefix masks162 192 = 3 := by
  calc
    countPrefix masks162 192 = countPrefix masks162 128 + blockCount masks162 128 :=
      prefix_step masks162 128
    _ = 3 := by rw [calib162_prefix02, calib162_block02]

theorem calib162_block03 : blockCount masks162 192 = 1 := by
  decide +kernel

theorem calib162_prefix04 : countPrefix masks162 256 = 4 := by
  calc
    countPrefix masks162 256 = countPrefix masks162 192 + blockCount masks162 192 :=
      prefix_step masks162 192
    _ = 4 := by rw [calib162_prefix03, calib162_block03]

theorem calib162_block04 : blockCount masks162 256 = 1 := by
  decide +kernel

theorem calib162_prefix05 : countPrefix masks162 320 = 5 := by
  calc
    countPrefix masks162 320 = countPrefix masks162 256 + blockCount masks162 256 :=
      prefix_step masks162 256
    _ = 5 := by rw [calib162_prefix04, calib162_block04]

theorem calib162_block05 : blockCount masks162 320 = 1 := by
  decide +kernel

theorem calib162_prefix06 : countPrefix masks162 384 = 6 := by
  calc
    countPrefix masks162 384 = countPrefix masks162 320 + blockCount masks162 320 :=
      prefix_step masks162 320
    _ = 6 := by rw [calib162_prefix05, calib162_block05]

theorem calib162_block06 : blockCount masks162 384 = 1 := by
  decide +kernel

theorem calib162_prefix07 : countPrefix masks162 448 = 7 := by
  calc
    countPrefix masks162 448 = countPrefix masks162 384 + blockCount masks162 384 :=
      prefix_step masks162 384
    _ = 7 := by rw [calib162_prefix06, calib162_block06]

theorem calib162_block07 : blockCount masks162 448 = 1 := by
  decide +kernel

theorem calib162_prefix08 : countPrefix masks162 512 = 8 := by
  calc
    countPrefix masks162 512 = countPrefix masks162 448 + blockCount masks162 448 :=
      prefix_step masks162 448
    _ = 8 := by rw [calib162_prefix07, calib162_block07]


end Paper6Calib

#print axioms Paper6Calib.calib162_prefix00
#print axioms Paper6Calib.calib162_block00
#print axioms Paper6Calib.calib162_prefix01
#print axioms Paper6Calib.calib162_block01
#print axioms Paper6Calib.calib162_prefix02
#print axioms Paper6Calib.calib162_block02
#print axioms Paper6Calib.calib162_prefix03
#print axioms Paper6Calib.calib162_block03
#print axioms Paper6Calib.calib162_prefix04
#print axioms Paper6Calib.calib162_block04
#print axioms Paper6Calib.calib162_prefix05
#print axioms Paper6Calib.calib162_block05
#print axioms Paper6Calib.calib162_prefix06
#print axioms Paper6Calib.calib162_block06
#print axioms Paper6Calib.calib162_prefix07
#print axioms Paper6Calib.calib162_block07
#print axioms Paper6Calib.calib162_prefix08
