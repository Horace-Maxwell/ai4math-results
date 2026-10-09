import Research.Backfill.Paper6.Calib170Part03

/-! Weight 170, blocks 32 through 39. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block32 : blockCount masks170 2048 = 2 := by
  decide +kernel

theorem calib170_prefix33 : countPrefix masks170 2112 = 34 := by
  calc
    countPrefix masks170 2112 = countPrefix masks170 2048 + blockCount masks170 2048 :=
      prefix_step masks170 2048
    _ = 34 := by rw [calib170_prefix32, calib170_block32]

theorem calib170_block33 : blockCount masks170 2112 = 10 := by
  decide +kernel

theorem calib170_prefix34 : countPrefix masks170 2176 = 44 := by
  calc
    countPrefix masks170 2176 = countPrefix masks170 2112 + blockCount masks170 2112 :=
      prefix_step masks170 2112
    _ = 44 := by rw [calib170_prefix33, calib170_block33]

theorem calib170_block34 : blockCount masks170 2176 = 2 := by
  decide +kernel

theorem calib170_prefix35 : countPrefix masks170 2240 = 46 := by
  calc
    countPrefix masks170 2240 = countPrefix masks170 2176 + blockCount masks170 2176 :=
      prefix_step masks170 2176
    _ = 46 := by rw [calib170_prefix34, calib170_block34]

theorem calib170_block35 : blockCount masks170 2240 = 2 := by
  decide +kernel

theorem calib170_prefix36 : countPrefix masks170 2304 = 48 := by
  calc
    countPrefix masks170 2304 = countPrefix masks170 2240 + blockCount masks170 2240 :=
      prefix_step masks170 2240
    _ = 48 := by rw [calib170_prefix35, calib170_block35]

theorem calib170_block36 : blockCount masks170 2304 = 2 := by
  decide +kernel

theorem calib170_prefix37 : countPrefix masks170 2368 = 50 := by
  calc
    countPrefix masks170 2368 = countPrefix masks170 2304 + blockCount masks170 2304 :=
      prefix_step masks170 2304
    _ = 50 := by rw [calib170_prefix36, calib170_block36]

theorem calib170_block37 : blockCount masks170 2368 = 10 := by
  decide +kernel

theorem calib170_prefix38 : countPrefix masks170 2432 = 60 := by
  calc
    countPrefix masks170 2432 = countPrefix masks170 2368 + blockCount masks170 2368 :=
      prefix_step masks170 2368
    _ = 60 := by rw [calib170_prefix37, calib170_block37]

theorem calib170_block38 : blockCount masks170 2432 = 2 := by
  decide +kernel

theorem calib170_prefix39 : countPrefix masks170 2496 = 62 := by
  calc
    countPrefix masks170 2496 = countPrefix masks170 2432 + blockCount masks170 2432 :=
      prefix_step masks170 2432
    _ = 62 := by rw [calib170_prefix38, calib170_block38]

theorem calib170_block39 : blockCount masks170 2496 = 2 := by
  decide +kernel

theorem calib170_prefix40 : countPrefix masks170 2560 = 64 := by
  calc
    countPrefix masks170 2560 = countPrefix masks170 2496 + blockCount masks170 2496 :=
      prefix_step masks170 2496
    _ = 64 := by rw [calib170_prefix39, calib170_block39]


end Paper6Calib

#print axioms Paper6Calib.calib170_block32
#print axioms Paper6Calib.calib170_prefix33
#print axioms Paper6Calib.calib170_block33
#print axioms Paper6Calib.calib170_prefix34
#print axioms Paper6Calib.calib170_block34
#print axioms Paper6Calib.calib170_prefix35
#print axioms Paper6Calib.calib170_block35
#print axioms Paper6Calib.calib170_prefix36
#print axioms Paper6Calib.calib170_block36
#print axioms Paper6Calib.calib170_prefix37
#print axioms Paper6Calib.calib170_block37
#print axioms Paper6Calib.calib170_prefix38
#print axioms Paper6Calib.calib170_block38
#print axioms Paper6Calib.calib170_prefix39
#print axioms Paper6Calib.calib170_block39
#print axioms Paper6Calib.calib170_prefix40
