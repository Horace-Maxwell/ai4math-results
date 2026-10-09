import Research.Backfill.Paper6.Calib162Part03

/-! Unverified candidate: weight 162, point blocks 32 through 39. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block32 : blockCount masks162 2048 = 1 := by
  decide +kernel

theorem calib162_prefix33 : countPrefix masks162 2112 = 33 := by
  calc
    countPrefix masks162 2112 = countPrefix masks162 2048 + blockCount masks162 2048 :=
      prefix_step masks162 2048
    _ = 33 := by rw [calib162_prefix32, calib162_block32]

theorem calib162_block33 : blockCount masks162 2112 = 1 := by
  decide +kernel

theorem calib162_prefix34 : countPrefix masks162 2176 = 34 := by
  calc
    countPrefix masks162 2176 = countPrefix masks162 2112 + blockCount masks162 2112 :=
      prefix_step masks162 2112
    _ = 34 := by rw [calib162_prefix33, calib162_block33]

theorem calib162_block34 : blockCount masks162 2176 = 7 := by
  decide +kernel

theorem calib162_prefix35 : countPrefix masks162 2240 = 41 := by
  calc
    countPrefix masks162 2240 = countPrefix masks162 2176 + blockCount masks162 2176 :=
      prefix_step masks162 2176
    _ = 41 := by rw [calib162_prefix34, calib162_block34]

theorem calib162_block35 : blockCount masks162 2240 = 9 := by
  decide +kernel

theorem calib162_prefix36 : countPrefix masks162 2304 = 50 := by
  calc
    countPrefix masks162 2304 = countPrefix masks162 2240 + blockCount masks162 2240 :=
      prefix_step masks162 2240
    _ = 50 := by rw [calib162_prefix35, calib162_block35]

theorem calib162_block36 : blockCount masks162 2304 = 1 := by
  decide +kernel

theorem calib162_prefix37 : countPrefix masks162 2368 = 51 := by
  calc
    countPrefix masks162 2368 = countPrefix masks162 2304 + blockCount masks162 2304 :=
      prefix_step masks162 2304
    _ = 51 := by rw [calib162_prefix36, calib162_block36]

theorem calib162_block37 : blockCount masks162 2368 = 1 := by
  decide +kernel

theorem calib162_prefix38 : countPrefix masks162 2432 = 52 := by
  calc
    countPrefix masks162 2432 = countPrefix masks162 2368 + blockCount masks162 2368 :=
      prefix_step masks162 2368
    _ = 52 := by rw [calib162_prefix37, calib162_block37]

theorem calib162_block38 : blockCount masks162 2432 = 7 := by
  decide +kernel

theorem calib162_prefix39 : countPrefix masks162 2496 = 59 := by
  calc
    countPrefix masks162 2496 = countPrefix masks162 2432 + blockCount masks162 2432 :=
      prefix_step masks162 2432
    _ = 59 := by rw [calib162_prefix38, calib162_block38]

theorem calib162_block39 : blockCount masks162 2496 = 9 := by
  decide +kernel

theorem calib162_prefix40 : countPrefix masks162 2560 = 68 := by
  calc
    countPrefix masks162 2560 = countPrefix masks162 2496 + blockCount masks162 2496 :=
      prefix_step masks162 2496
    _ = 68 := by rw [calib162_prefix39, calib162_block39]


end Paper6Calib

#print axioms Paper6Calib.calib162_block32
#print axioms Paper6Calib.calib162_prefix33
#print axioms Paper6Calib.calib162_block33
#print axioms Paper6Calib.calib162_prefix34
#print axioms Paper6Calib.calib162_block34
#print axioms Paper6Calib.calib162_prefix35
#print axioms Paper6Calib.calib162_block35
#print axioms Paper6Calib.calib162_prefix36
#print axioms Paper6Calib.calib162_block36
#print axioms Paper6Calib.calib162_prefix37
#print axioms Paper6Calib.calib162_block37
#print axioms Paper6Calib.calib162_prefix38
#print axioms Paper6Calib.calib162_block38
#print axioms Paper6Calib.calib162_prefix39
#print axioms Paper6Calib.calib162_block39
#print axioms Paper6Calib.calib162_prefix40
