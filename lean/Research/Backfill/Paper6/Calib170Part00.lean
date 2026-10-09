import Research.Backfill.Paper6.Calib170Data

/-! Weight 170, blocks 0 through 7. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_prefix00 : countPrefix masks170 0 = 0 := rfl

theorem calib170_block00 : blockCount masks170 0 = 0 := by
  decide +kernel

theorem calib170_prefix01 : countPrefix masks170 64 = 0 := by
  calc
    countPrefix masks170 64 = countPrefix masks170 0 + blockCount masks170 0 :=
      prefix_step masks170 0
    _ = 0 := by rw [calib170_prefix00, calib170_block00]

theorem calib170_block01 : blockCount masks170 64 = 0 := by
  decide +kernel

theorem calib170_prefix02 : countPrefix masks170 128 = 0 := by
  calc
    countPrefix masks170 128 = countPrefix masks170 64 + blockCount masks170 64 :=
      prefix_step masks170 64
    _ = 0 := by rw [calib170_prefix01, calib170_block01]

theorem calib170_block02 : blockCount masks170 128 = 4 := by
  decide +kernel

theorem calib170_prefix03 : countPrefix masks170 192 = 4 := by
  calc
    countPrefix masks170 192 = countPrefix masks170 128 + blockCount masks170 128 :=
      prefix_step masks170 128
    _ = 4 := by rw [calib170_prefix02, calib170_block02]

theorem calib170_block03 : blockCount masks170 192 = 4 := by
  decide +kernel

theorem calib170_prefix04 : countPrefix masks170 256 = 8 := by
  calc
    countPrefix masks170 256 = countPrefix masks170 192 + blockCount masks170 192 :=
      prefix_step masks170 192
    _ = 8 := by rw [calib170_prefix03, calib170_block03]

theorem calib170_block04 : blockCount masks170 256 = 4 := by
  decide +kernel

theorem calib170_prefix05 : countPrefix masks170 320 = 12 := by
  calc
    countPrefix masks170 320 = countPrefix masks170 256 + blockCount masks170 256 :=
      prefix_step masks170 256
    _ = 12 := by rw [calib170_prefix04, calib170_block04]

theorem calib170_block05 : blockCount masks170 320 = 4 := by
  decide +kernel

theorem calib170_prefix06 : countPrefix masks170 384 = 16 := by
  calc
    countPrefix masks170 384 = countPrefix masks170 320 + blockCount masks170 320 :=
      prefix_step masks170 320
    _ = 16 := by rw [calib170_prefix05, calib170_block05]

theorem calib170_block06 : blockCount masks170 384 = 0 := by
  decide +kernel

theorem calib170_prefix07 : countPrefix masks170 448 = 16 := by
  calc
    countPrefix masks170 448 = countPrefix masks170 384 + blockCount masks170 384 :=
      prefix_step masks170 384
    _ = 16 := by rw [calib170_prefix06, calib170_block06]

theorem calib170_block07 : blockCount masks170 448 = 0 := by
  decide +kernel

theorem calib170_prefix08 : countPrefix masks170 512 = 16 := by
  calc
    countPrefix masks170 512 = countPrefix masks170 448 + blockCount masks170 448 :=
      prefix_step masks170 448
    _ = 16 := by rw [calib170_prefix07, calib170_block07]


end Paper6Calib

#print axioms Paper6Calib.calib170_prefix00
#print axioms Paper6Calib.calib170_block00
#print axioms Paper6Calib.calib170_prefix01
#print axioms Paper6Calib.calib170_block01
#print axioms Paper6Calib.calib170_prefix02
#print axioms Paper6Calib.calib170_block02
#print axioms Paper6Calib.calib170_prefix03
#print axioms Paper6Calib.calib170_block03
#print axioms Paper6Calib.calib170_prefix04
#print axioms Paper6Calib.calib170_block04
#print axioms Paper6Calib.calib170_prefix05
#print axioms Paper6Calib.calib170_block05
#print axioms Paper6Calib.calib170_prefix06
#print axioms Paper6Calib.calib170_block06
#print axioms Paper6Calib.calib170_prefix07
#print axioms Paper6Calib.calib170_block07
#print axioms Paper6Calib.calib170_prefix08
