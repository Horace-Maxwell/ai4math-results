import Research.Backfill.Paper6.Calib170Part06

/-! Weight 170, blocks 56 through 63. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem calib170_block56 : blockCount masks170 3584 = 2 := by
  decide +kernel

theorem calib170_prefix57 : countPrefix masks170 3648 = 134 := by
  calc
    countPrefix masks170 3648 = countPrefix masks170 3584 + blockCount masks170 3584 :=
      prefix_step masks170 3584
    _ = 134 := by rw [calib170_prefix56, calib170_block56]

theorem calib170_block57 : blockCount masks170 3648 = 2 := by
  decide +kernel

theorem calib170_prefix58 : countPrefix masks170 3712 = 136 := by
  calc
    countPrefix masks170 3712 = countPrefix masks170 3648 + blockCount masks170 3648 :=
      prefix_step masks170 3648
    _ = 136 := by rw [calib170_prefix57, calib170_block57]

theorem calib170_block58 : blockCount masks170 3712 = 6 := by
  decide +kernel

theorem calib170_prefix59 : countPrefix masks170 3776 = 142 := by
  calc
    countPrefix masks170 3776 = countPrefix masks170 3712 + blockCount masks170 3712 :=
      prefix_step masks170 3712
    _ = 142 := by rw [calib170_prefix58, calib170_block58]

theorem calib170_block59 : blockCount masks170 3776 = 10 := by
  decide +kernel

theorem calib170_prefix60 : countPrefix masks170 3840 = 152 := by
  calc
    countPrefix masks170 3840 = countPrefix masks170 3776 + blockCount masks170 3776 :=
      prefix_step masks170 3776
    _ = 152 := by rw [calib170_prefix59, calib170_block59]

theorem calib170_block60 : blockCount masks170 3840 = 6 := by
  decide +kernel

theorem calib170_prefix61 : countPrefix masks170 3904 = 158 := by
  calc
    countPrefix masks170 3904 = countPrefix masks170 3840 + blockCount masks170 3840 :=
      prefix_step masks170 3840
    _ = 158 := by rw [calib170_prefix60, calib170_block60]

theorem calib170_block61 : blockCount masks170 3904 = 4 := by
  decide +kernel

theorem calib170_prefix62 : countPrefix masks170 3968 = 162 := by
  calc
    countPrefix masks170 3968 = countPrefix masks170 3904 + blockCount masks170 3904 :=
      prefix_step masks170 3904
    _ = 162 := by rw [calib170_prefix61, calib170_block61]

theorem calib170_block62 : blockCount masks170 3968 = 2 := by
  decide +kernel

theorem calib170_prefix63 : countPrefix masks170 4032 = 164 := by
  calc
    countPrefix masks170 4032 = countPrefix masks170 3968 + blockCount masks170 3968 :=
      prefix_step masks170 3968
    _ = 164 := by rw [calib170_prefix62, calib170_block62]

theorem calib170_block63 : blockCount masks170 4032 = 6 := by
  decide +kernel

theorem calib170_prefix64 : countPrefix masks170 4096 = 170 := by
  calc
    countPrefix masks170 4096 = countPrefix masks170 4032 + blockCount masks170 4032 :=
      prefix_step masks170 4032
    _ = 170 := by rw [calib170_prefix63, calib170_block63]


end Paper6Calib

#print axioms Paper6Calib.calib170_block56
#print axioms Paper6Calib.calib170_prefix57
#print axioms Paper6Calib.calib170_block57
#print axioms Paper6Calib.calib170_prefix58
#print axioms Paper6Calib.calib170_block58
#print axioms Paper6Calib.calib170_prefix59
#print axioms Paper6Calib.calib170_block59
#print axioms Paper6Calib.calib170_prefix60
#print axioms Paper6Calib.calib170_block60
#print axioms Paper6Calib.calib170_prefix61
#print axioms Paper6Calib.calib170_block61
#print axioms Paper6Calib.calib170_prefix62
#print axioms Paper6Calib.calib170_block62
#print axioms Paper6Calib.calib170_prefix63
#print axioms Paper6Calib.calib170_block63
#print axioms Paper6Calib.calib170_prefix64
