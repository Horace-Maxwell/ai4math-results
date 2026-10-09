import Research.Backfill.Paper6.Calib166Data

/-! Weight 166, blocks 0 through 7. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_prefix00 : countPrefix masks166 0 = 0 := rfl

theorem calib166_block00 : blockCount masks166 0 = 0 := by
  decide +kernel

theorem calib166_prefix01 : countPrefix masks166 64 = 0 := by
  calc
    countPrefix masks166 64 = countPrefix masks166 0 + blockCount masks166 0 :=
      prefix_step masks166 0
    _ = 0 := by rw [calib166_prefix00, calib166_block00]

theorem calib166_block01 : blockCount masks166 64 = 4 := by
  decide +kernel

theorem calib166_prefix02 : countPrefix masks166 128 = 4 := by
  calc
    countPrefix masks166 128 = countPrefix masks166 64 + blockCount masks166 64 :=
      prefix_step masks166 64
    _ = 4 := by rw [calib166_prefix01, calib166_block01]

theorem calib166_block02 : blockCount masks166 128 = 0 := by
  decide +kernel

theorem calib166_prefix03 : countPrefix masks166 192 = 4 := by
  calc
    countPrefix masks166 192 = countPrefix masks166 128 + blockCount masks166 128 :=
      prefix_step masks166 128
    _ = 4 := by rw [calib166_prefix02, calib166_block02]

theorem calib166_block03 : blockCount masks166 192 = 4 := by
  decide +kernel

theorem calib166_prefix04 : countPrefix masks166 256 = 8 := by
  calc
    countPrefix masks166 256 = countPrefix masks166 192 + blockCount masks166 192 :=
      prefix_step masks166 192
    _ = 8 := by rw [calib166_prefix03, calib166_block03]

theorem calib166_block04 : blockCount masks166 256 = 0 := by
  decide +kernel

theorem calib166_prefix05 : countPrefix masks166 320 = 8 := by
  calc
    countPrefix masks166 320 = countPrefix masks166 256 + blockCount masks166 256 :=
      prefix_step masks166 256
    _ = 8 := by rw [calib166_prefix04, calib166_block04]

theorem calib166_block05 : blockCount masks166 320 = 4 := by
  decide +kernel

theorem calib166_prefix06 : countPrefix masks166 384 = 12 := by
  calc
    countPrefix masks166 384 = countPrefix masks166 320 + blockCount masks166 320 :=
      prefix_step masks166 320
    _ = 12 := by rw [calib166_prefix05, calib166_block05]

theorem calib166_block06 : blockCount masks166 384 = 0 := by
  decide +kernel

theorem calib166_prefix07 : countPrefix masks166 448 = 12 := by
  calc
    countPrefix masks166 448 = countPrefix masks166 384 + blockCount masks166 384 :=
      prefix_step masks166 384
    _ = 12 := by rw [calib166_prefix06, calib166_block06]

theorem calib166_block07 : blockCount masks166 448 = 4 := by
  decide +kernel

theorem calib166_prefix08 : countPrefix masks166 512 = 16 := by
  calc
    countPrefix masks166 512 = countPrefix masks166 448 + blockCount masks166 448 :=
      prefix_step masks166 448
    _ = 16 := by rw [calib166_prefix07, calib166_block07]


end Paper6Calib

#print axioms Paper6Calib.calib166_prefix00
#print axioms Paper6Calib.calib166_block00
#print axioms Paper6Calib.calib166_prefix01
#print axioms Paper6Calib.calib166_block01
#print axioms Paper6Calib.calib166_prefix02
#print axioms Paper6Calib.calib166_block02
#print axioms Paper6Calib.calib166_prefix03
#print axioms Paper6Calib.calib166_block03
#print axioms Paper6Calib.calib166_prefix04
#print axioms Paper6Calib.calib166_block04
#print axioms Paper6Calib.calib166_prefix05
#print axioms Paper6Calib.calib166_block05
#print axioms Paper6Calib.calib166_prefix06
#print axioms Paper6Calib.calib166_block06
#print axioms Paper6Calib.calib166_prefix07
#print axioms Paper6Calib.calib166_block07
#print axioms Paper6Calib.calib166_prefix08
