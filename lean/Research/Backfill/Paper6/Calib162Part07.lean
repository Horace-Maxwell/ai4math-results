import Research.Backfill.Paper6.Calib162Part06

/-! Unverified candidate: weight 162, point blocks 56 through 63. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib162_block56 : blockCount masks162 3584 = 1 := by
  decide +kernel

theorem calib162_prefix57 : countPrefix masks162 3648 = 135 := by
  calc
    countPrefix masks162 3648 = countPrefix masks162 3584 + blockCount masks162 3584 :=
      prefix_step masks162 3584
    _ = 135 := by rw [calib162_prefix56, calib162_block56]

theorem calib162_block57 : blockCount masks162 3648 = 1 := by
  decide +kernel

theorem calib162_prefix58 : countPrefix masks162 3712 = 136 := by
  calc
    countPrefix masks162 3712 = countPrefix masks162 3648 + blockCount masks162 3648 :=
      prefix_step masks162 3648
    _ = 136 := by rw [calib162_prefix57, calib162_block57]

theorem calib162_block58 : blockCount masks162 3712 = 7 := by
  decide +kernel

theorem calib162_prefix59 : countPrefix masks162 3776 = 143 := by
  calc
    countPrefix masks162 3776 = countPrefix masks162 3712 + blockCount masks162 3712 :=
      prefix_step masks162 3712
    _ = 143 := by rw [calib162_prefix58, calib162_block58]

theorem calib162_block59 : blockCount masks162 3776 = 5 := by
  decide +kernel

theorem calib162_prefix60 : countPrefix masks162 3840 = 148 := by
  calc
    countPrefix masks162 3840 = countPrefix masks162 3776 + blockCount masks162 3776 :=
      prefix_step masks162 3776
    _ = 148 := by rw [calib162_prefix59, calib162_block59]

theorem calib162_block60 : blockCount masks162 3840 = 1 := by
  decide +kernel

theorem calib162_prefix61 : countPrefix masks162 3904 = 149 := by
  calc
    countPrefix masks162 3904 = countPrefix masks162 3840 + blockCount masks162 3840 :=
      prefix_step masks162 3840
    _ = 149 := by rw [calib162_prefix60, calib162_block60]

theorem calib162_block61 : blockCount masks162 3904 = 1 := by
  decide +kernel

theorem calib162_prefix62 : countPrefix masks162 3968 = 150 := by
  calc
    countPrefix masks162 3968 = countPrefix masks162 3904 + blockCount masks162 3904 :=
      prefix_step masks162 3904
    _ = 150 := by rw [calib162_prefix61, calib162_block61]

theorem calib162_block62 : blockCount masks162 3968 = 7 := by
  decide +kernel

theorem calib162_prefix63 : countPrefix masks162 4032 = 157 := by
  calc
    countPrefix masks162 4032 = countPrefix masks162 3968 + blockCount masks162 3968 :=
      prefix_step masks162 3968
    _ = 157 := by rw [calib162_prefix62, calib162_block62]

theorem calib162_block63 : blockCount masks162 4032 = 5 := by
  decide +kernel

theorem calib162_prefix64 : countPrefix masks162 4096 = 162 := by
  calc
    countPrefix masks162 4096 = countPrefix masks162 4032 + blockCount masks162 4032 :=
      prefix_step masks162 4032
    _ = 162 := by rw [calib162_prefix63, calib162_block63]


end Paper6Calib

#print axioms Paper6Calib.calib162_block56
#print axioms Paper6Calib.calib162_prefix57
#print axioms Paper6Calib.calib162_block57
#print axioms Paper6Calib.calib162_prefix58
#print axioms Paper6Calib.calib162_block58
#print axioms Paper6Calib.calib162_prefix59
#print axioms Paper6Calib.calib162_block59
#print axioms Paper6Calib.calib162_prefix60
#print axioms Paper6Calib.calib162_block60
#print axioms Paper6Calib.calib162_prefix61
#print axioms Paper6Calib.calib162_block61
#print axioms Paper6Calib.calib162_prefix62
#print axioms Paper6Calib.calib162_block62
#print axioms Paper6Calib.calib162_prefix63
#print axioms Paper6Calib.calib162_block63
#print axioms Paper6Calib.calib162_prefix64
