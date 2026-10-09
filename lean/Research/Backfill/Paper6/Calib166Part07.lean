import Research.Backfill.Paper6.Calib166Part06

/-! Weight 166, blocks 56 through 63. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib166_block56 : blockCount masks166 3584 = 0 := by
  decide +kernel

theorem calib166_prefix57 : countPrefix masks166 3648 = 150 := by
  calc
    countPrefix masks166 3648 = countPrefix masks166 3584 + blockCount masks166 3584 :=
      prefix_step masks166 3584
    _ = 150 := by rw [calib166_prefix56, calib166_block56]

theorem calib166_block57 : blockCount masks166 3648 = 0 := by
  decide +kernel

theorem calib166_prefix58 : countPrefix masks166 3712 = 150 := by
  calc
    countPrefix masks166 3712 = countPrefix masks166 3648 + blockCount masks166 3648 :=
      prefix_step masks166 3648
    _ = 150 := by rw [calib166_prefix57, calib166_block57]

theorem calib166_block58 : blockCount masks166 3712 = 0 := by
  decide +kernel

theorem calib166_prefix59 : countPrefix masks166 3776 = 150 := by
  calc
    countPrefix masks166 3776 = countPrefix masks166 3712 + blockCount masks166 3712 :=
      prefix_step masks166 3712
    _ = 150 := by rw [calib166_prefix58, calib166_block58]

theorem calib166_block59 : blockCount masks166 3776 = 0 := by
  decide +kernel

theorem calib166_prefix60 : countPrefix masks166 3840 = 150 := by
  calc
    countPrefix masks166 3840 = countPrefix masks166 3776 + blockCount masks166 3776 :=
      prefix_step masks166 3776
    _ = 150 := by rw [calib166_prefix59, calib166_block59]

theorem calib166_block60 : blockCount masks166 3840 = 4 := by
  decide +kernel

theorem calib166_prefix61 : countPrefix masks166 3904 = 154 := by
  calc
    countPrefix masks166 3904 = countPrefix masks166 3840 + blockCount masks166 3840 :=
      prefix_step masks166 3840
    _ = 154 := by rw [calib166_prefix60, calib166_block60]

theorem calib166_block61 : blockCount masks166 3904 = 4 := by
  decide +kernel

theorem calib166_prefix62 : countPrefix masks166 3968 = 158 := by
  calc
    countPrefix masks166 3968 = countPrefix masks166 3904 + blockCount masks166 3904 :=
      prefix_step masks166 3904
    _ = 158 := by rw [calib166_prefix61, calib166_block61]

theorem calib166_block62 : blockCount masks166 3968 = 4 := by
  decide +kernel

theorem calib166_prefix63 : countPrefix masks166 4032 = 162 := by
  calc
    countPrefix masks166 4032 = countPrefix masks166 3968 + blockCount masks166 3968 :=
      prefix_step masks166 3968
    _ = 162 := by rw [calib166_prefix62, calib166_block62]

theorem calib166_block63 : blockCount masks166 4032 = 4 := by
  decide +kernel

theorem calib166_prefix64 : countPrefix masks166 4096 = 166 := by
  calc
    countPrefix masks166 4096 = countPrefix masks166 4032 + blockCount masks166 4032 :=
      prefix_step masks166 4032
    _ = 166 := by rw [calib166_prefix63, calib166_block63]


end Paper6Calib

#print axioms Paper6Calib.calib166_block56
#print axioms Paper6Calib.calib166_prefix57
#print axioms Paper6Calib.calib166_block57
#print axioms Paper6Calib.calib166_prefix58
#print axioms Paper6Calib.calib166_block58
#print axioms Paper6Calib.calib166_prefix59
#print axioms Paper6Calib.calib166_block59
#print axioms Paper6Calib.calib166_prefix60
#print axioms Paper6Calib.calib166_block60
#print axioms Paper6Calib.calib166_prefix61
#print axioms Paper6Calib.calib166_block61
#print axioms Paper6Calib.calib166_prefix62
#print axioms Paper6Calib.calib166_block62
#print axioms Paper6Calib.calib166_prefix63
#print axioms Paper6Calib.calib166_block63
#print axioms Paper6Calib.calib166_prefix64
