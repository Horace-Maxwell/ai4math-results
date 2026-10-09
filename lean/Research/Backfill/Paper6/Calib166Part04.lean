import Research.Backfill.Paper6.Calib166Part03

/-! Weight 166, blocks 32 through 39. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block32 : blockCount masks166 2048 = 0 := by
  decide +kernel

theorem calib166_prefix33 : countPrefix masks166 2112 = 32 := by
  calc
    countPrefix masks166 2112 = countPrefix masks166 2048 + blockCount masks166 2048 :=
      prefix_step masks166 2048
    _ = 32 := by rw [calib166_prefix32, calib166_block32]

theorem calib166_block33 : blockCount masks166 2112 = 4 := by
  decide +kernel

theorem calib166_prefix34 : countPrefix masks166 2176 = 36 := by
  calc
    countPrefix masks166 2176 = countPrefix masks166 2112 + blockCount masks166 2112 :=
      prefix_step masks166 2112
    _ = 36 := by rw [calib166_prefix33, calib166_block33]

theorem calib166_block34 : blockCount masks166 2176 = 0 := by
  decide +kernel

theorem calib166_prefix35 : countPrefix masks166 2240 = 36 := by
  calc
    countPrefix masks166 2240 = countPrefix masks166 2176 + blockCount masks166 2176 :=
      prefix_step masks166 2176
    _ = 36 := by rw [calib166_prefix34, calib166_block34]

theorem calib166_block35 : blockCount masks166 2240 = 4 := by
  decide +kernel

theorem calib166_prefix36 : countPrefix masks166 2304 = 40 := by
  calc
    countPrefix masks166 2304 = countPrefix masks166 2240 + blockCount masks166 2240 :=
      prefix_step masks166 2240
    _ = 40 := by rw [calib166_prefix35, calib166_block35]

theorem calib166_block36 : blockCount masks166 2304 = 8 := by
  decide +kernel

theorem calib166_prefix37 : countPrefix masks166 2368 = 48 := by
  calc
    countPrefix masks166 2368 = countPrefix masks166 2304 + blockCount masks166 2304 :=
      prefix_step masks166 2304
    _ = 48 := by rw [calib166_prefix36, calib166_block36]

theorem calib166_block37 : blockCount masks166 2368 = 14 := by
  decide +kernel

theorem calib166_prefix38 : countPrefix masks166 2432 = 62 := by
  calc
    countPrefix masks166 2432 = countPrefix masks166 2368 + blockCount masks166 2368 :=
      prefix_step masks166 2368
    _ = 62 := by rw [calib166_prefix37, calib166_block37]

theorem calib166_block38 : blockCount masks166 2432 = 12 := by
  decide +kernel

theorem calib166_prefix39 : countPrefix masks166 2496 = 74 := by
  calc
    countPrefix masks166 2496 = countPrefix masks166 2432 + blockCount masks166 2432 :=
      prefix_step masks166 2432
    _ = 74 := by rw [calib166_prefix38, calib166_block38]

theorem calib166_block39 : blockCount masks166 2496 = 8 := by
  decide +kernel

theorem calib166_prefix40 : countPrefix masks166 2560 = 82 := by
  calc
    countPrefix masks166 2560 = countPrefix masks166 2496 + blockCount masks166 2496 :=
      prefix_step masks166 2496
    _ = 82 := by rw [calib166_prefix39, calib166_block39]


end Paper6Calib

#print axioms Paper6Calib.calib166_block32
#print axioms Paper6Calib.calib166_prefix33
#print axioms Paper6Calib.calib166_block33
#print axioms Paper6Calib.calib166_prefix34
#print axioms Paper6Calib.calib166_block34
#print axioms Paper6Calib.calib166_prefix35
#print axioms Paper6Calib.calib166_block35
#print axioms Paper6Calib.calib166_prefix36
#print axioms Paper6Calib.calib166_block36
#print axioms Paper6Calib.calib166_prefix37
#print axioms Paper6Calib.calib166_block37
#print axioms Paper6Calib.calib166_prefix38
#print axioms Paper6Calib.calib166_block38
#print axioms Paper6Calib.calib166_prefix39
#print axioms Paper6Calib.calib166_block39
#print axioms Paper6Calib.calib166_prefix40
