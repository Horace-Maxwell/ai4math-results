import Research.Backfill.Paper6.Calib174Data

/-! Weight 174, blocks 0 through 7. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib174_prefix00 : countPrefix masks174 0 = 0 := rfl

theorem calib174_block00 : blockCount masks174 0 = 0 := by
  decide +kernel

theorem calib174_prefix01 : countPrefix masks174 64 = 0 := by
  calc
    countPrefix masks174 64 = countPrefix masks174 0 + blockCount masks174 0 :=
      prefix_step masks174 0
    _ = 0 := by rw [calib174_prefix00, calib174_block00]

theorem calib174_block01 : blockCount masks174 64 = 0 := by
  decide +kernel

theorem calib174_prefix02 : countPrefix masks174 128 = 0 := by
  calc
    countPrefix masks174 128 = countPrefix masks174 64 + blockCount masks174 64 :=
      prefix_step masks174 64
    _ = 0 := by rw [calib174_prefix01, calib174_block01]

theorem calib174_block02 : blockCount masks174 128 = 4 := by
  decide +kernel

theorem calib174_prefix03 : countPrefix masks174 192 = 4 := by
  calc
    countPrefix masks174 192 = countPrefix masks174 128 + blockCount masks174 128 :=
      prefix_step masks174 128
    _ = 4 := by rw [calib174_prefix02, calib174_block02]

theorem calib174_block03 : blockCount masks174 192 = 4 := by
  decide +kernel

theorem calib174_prefix04 : countPrefix masks174 256 = 8 := by
  calc
    countPrefix masks174 256 = countPrefix masks174 192 + blockCount masks174 192 :=
      prefix_step masks174 192
    _ = 8 := by rw [calib174_prefix03, calib174_block03]

theorem calib174_block04 : blockCount masks174 256 = 4 := by
  decide +kernel

theorem calib174_prefix05 : countPrefix masks174 320 = 12 := by
  calc
    countPrefix masks174 320 = countPrefix masks174 256 + blockCount masks174 256 :=
      prefix_step masks174 256
    _ = 12 := by rw [calib174_prefix04, calib174_block04]

theorem calib174_block05 : blockCount masks174 320 = 4 := by
  decide +kernel

theorem calib174_prefix06 : countPrefix masks174 384 = 16 := by
  calc
    countPrefix masks174 384 = countPrefix masks174 320 + blockCount masks174 320 :=
      prefix_step masks174 320
    _ = 16 := by rw [calib174_prefix05, calib174_block05]

theorem calib174_block06 : blockCount masks174 384 = 0 := by
  decide +kernel

theorem calib174_prefix07 : countPrefix masks174 448 = 16 := by
  calc
    countPrefix masks174 448 = countPrefix masks174 384 + blockCount masks174 384 :=
      prefix_step masks174 384
    _ = 16 := by rw [calib174_prefix06, calib174_block06]

theorem calib174_block07 : blockCount masks174 448 = 0 := by
  decide +kernel

theorem calib174_prefix08 : countPrefix masks174 512 = 16 := by
  calc
    countPrefix masks174 512 = countPrefix masks174 448 + blockCount masks174 448 :=
      prefix_step masks174 448
    _ = 16 := by rw [calib174_prefix07, calib174_block07]


end Paper6Calib

#print axioms Paper6Calib.calib174_prefix00
#print axioms Paper6Calib.calib174_block00
#print axioms Paper6Calib.calib174_prefix01
#print axioms Paper6Calib.calib174_block01
#print axioms Paper6Calib.calib174_prefix02
#print axioms Paper6Calib.calib174_block02
#print axioms Paper6Calib.calib174_prefix03
#print axioms Paper6Calib.calib174_block03
#print axioms Paper6Calib.calib174_prefix04
#print axioms Paper6Calib.calib174_block04
#print axioms Paper6Calib.calib174_prefix05
#print axioms Paper6Calib.calib174_block05
#print axioms Paper6Calib.calib174_prefix06
#print axioms Paper6Calib.calib174_block06
#print axioms Paper6Calib.calib174_prefix07
#print axioms Paper6Calib.calib174_block07
#print axioms Paper6Calib.calib174_prefix08
